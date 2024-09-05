// Package inference provides a Datalog-like inference engine.
// It is embeddable in Go programs and can use a database by mapping predicates to queries.
//
// # Values
//
// Several kinds of values can be used in facts and rules:
//   - variables,
//   - atoms,
//   - strings,
//   - integers,
//   - compound terms.
//
// Lists of values can be defined using special compound terms.
//
// # Variables
//
// Variables can be free or bound. Broadly speaking, free variables can be thought of as return values,
// while bound variables can be thought of as input arguments.
//
// # Unification
//
// The process of unification compares the structures of two values and find the most general substitution
// that makes them equal, in case one exists.
// For example, the following two lists can be unified using the given substitution:
//
//	[1, X], [Y, 2]
//	X = 2, Y = 1
//
// Most general unifiers are unique for any two terms.
//
// # AVMs
//
// AVMs are special data structures which don't support unification out of the box.
// However it's a simple matter to implement a predicate which unifies two AVMs represented as open lists.
//
// # Facts
//
// Facts are compound terms that can be thought of as records in a relational database.
// A fact is a positive literal representing a piece of knowledge.
// Technically, a fact is rule without a tail (see below).
//
// # Rules
//
// Rules represent pieces of knowledge that captures causality. A rule consists of a head,
// which is a positive literal, and a tail, which is a list of positive literals.
// The inference engine evaluates a rule's head for truth or falsity
// depending on whether the tail can be proven true.
//
// # Negation as failure
//
// Logical negation can't be used in rules. However, negation-as-failure can be implemented via an in-built predicate.
// According to this concept, a goal evaluates to falsity if it can't be proven. Schematically:
//
//	not(X) :- call(X), !, fail.
//	not(X).
//
// # Inference
//
// The algorithm used for inference is based on [SLD-resolution].
//
// [SLD-resolution]: https://en.wikipedia.org/wiki/SLD_resolution
package inference

import (
	"cmp"
	"context"
	"fmt"
	"maps"
	"sort"
	"strconv"
	"strings"
	"unsafe"

	"github.com/fealsamh/go-utils/dbutils"
)

// EvalContext is an evaluation context for a goal.
type EvalContext struct {
	// Engine is the underlying inference engine.
	Engine *Engine
	// DB is the database to be used with predicates backed by queries.
	DB interface {
		dbutils.Querier
		dbutils.Txer
	}
	// Context is the associated context used for interruptable operations.
	Context context.Context
	cut     bool
	vars    map[*Var]Value
}

func (ctx *EvalContext) clone() *EvalContext {
	return &EvalContext{
		Engine:  ctx.Engine,
		DB:      ctx.DB,
		Context: ctx.Context,
		cut:     ctx.cut,
		vars:    maps.Clone(ctx.vars),
	}
}

func listProfile(ctx *EvalContext, l []Value) string {
	var sb strings.Builder
	for i, x := range l {
		if i > 0 {
			sb.WriteRune(':')
		}
		sb.WriteString(x.profile(ctx))
	}
	return sb.String()
}

// Dummy is a dummy method to placate the linter in rangefunc expressions.
func (ctx *EvalContext) Dummy() {}

// Value is a value used by the inference engine.
type Value interface {
	fmt.Stringer
	// Type is the type of the value.
	Type(*EvalContext) *Type
	// IsGround returns whether the value is ground, that is, contains no free variables.
	IsGround(*EvalContext) bool
	// Ground returns the ground value of the value.
	Ground(*EvalContext) (Value, bool)
	// TryGround tries to return the ground value of the value.
	TryGround(*EvalContext) (Value, bool)
	// Unify unifies the value with another value.
	Unify(*EvalContext, Value) func(func(*EvalContext) bool)

	profile(*EvalContext) string
}

// Bottom returns the bottom value of the value.
func Bottom(ctx *EvalContext, val Value) Value {
	if x, ok := val.(*Var); ok {
		return x.bottom(ctx)
	}
	return val
}

// Var is a variable that can be either free or bound.
type Var struct {
	name string
}

func (v *Var) bottom(ctx *EvalContext) Value {
	val, ok := ctx.vars[v]
	if !ok {
		return v
	}
	switch x := val.(type) {
	case *Var:
		return x.bottom(ctx)
	default:
		return x
	}
}

func (v *Var) String() string { return cmp.Or(v.name, "?") }

// Type returns the type of a bound variable.
func (v *Var) Type(ctx *EvalContext) *Type {
	if ctx == nil {
		panic("failed to get type of variable, no context")
	}
	x := v.bottom(ctx)
	if _, ok := x.(*Var); ok {
		panic("failed to get type of variable, not bound")
	}
	return x.Type(ctx)
}

// IsGround returns whether the variable is ground.
func (v *Var) IsGround(ctx *EvalContext) bool {
	_, ok := v.bottom(ctx).(*Var)
	return !ok
}

// Ground returns the ground value of the variable.
func (v *Var) Ground(ctx *EvalContext) (Value, bool) {
	x := v.bottom(ctx)
	if _, ok := x.(*Var); ok {
		return nil, false
	}
	return x.Ground(ctx)
}

// TryGround tries to return the ground value of the variable.
func (v *Var) TryGround(ctx *EvalContext) (Value, bool) {
	x := v.bottom(ctx)
	if _, ok := x.(*Var); ok {
		return v, false
	}
	return x.TryGround(ctx)
}

// Unify unifies the variable with a value.
func (v *Var) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		b := v.bottom(ctx)
		if v, ok := b.(*Var); ok {
			if ctx.vars == nil {
				ctx.vars = make(map[*Var]Value)
			}
			ctx.vars[v] = val
			yield(ctx)
			delete(ctx.vars, v)
		} else {
			for ctx := range b.Unify(ctx, val) {
				if !yield(ctx) {
					return
				}
			}
		}
	}
}

func (v *Var) profile(ctx *EvalContext) string {
	b := v.bottom(ctx)
	if _, ok := b.(*Var); ok {
		return "?"
	}
	return b.profile(ctx)
}

// Atom is an atomic value.
type Atom string

func (a Atom) String() string { return string(a) }

// Type returns the type of the atom.
func (a Atom) Type(ctx *EvalContext) *Type {
	return &Type{Name: "atom"}
}

// IsGround returns whether the value is ground.
func (a Atom) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the atom, which is the atom itself.
func (a Atom) Ground(ctx *EvalContext) (Value, bool) { return a, true }

// TryGround tries to return the ground value of the atom, which is the atom itself.
func (a Atom) TryGround(ctx *EvalContext) (Value, bool) { return a, true }

// Unify unifies the atom with a value.
func (a Atom) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, a) {
				yield(ctx)
			}
		case Atom:
			if x == a {
				yield(ctx)
			}
		}
	}
}

func (a Atom) profile(ctx *EvalContext) string { return string(a) }

// String is a string value.
type String string

func (s String) String() string { return strconv.Quote(string(s)) }

// Type returns the type of the string.
func (s String) Type(ctx *EvalContext) *Type {
	return &Type{Name: "string"}
}

// IsGround returns whether the value is ground.
func (s String) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the string, which is the string itself.
func (s String) Ground(ctx *EvalContext) (Value, bool) { return s, true }

// TryGround tries to return the ground value of the string, which is the string itself.
func (s String) TryGround(ctx *EvalContext) (Value, bool) { return s, true }

// Unify unifies the string with a value.
func (s String) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, s) {
				yield(ctx)
			}
		case String:
			if x == s {
				yield(ctx)
			}
		}
	}
}

func (s String) profile(ctx *EvalContext) string { return strconv.Quote(string(s)) }

// Integer is an integer value.
type Integer int

func (i Integer) String() string { return strconv.Itoa(int(i)) }

// Type returns the type of the integer.
func (i Integer) Type(ctx *EvalContext) *Type {
	return &Type{Name: "integer"}
}

// IsGround returns whether the value is ground.
func (i Integer) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the integer, which is the integer itself.
func (i Integer) Ground(ctx *EvalContext) (Value, bool) { return i, true }

// TryGround tries to return the ground value of the integer, which is the integer itself.
func (i Integer) TryGround(ctx *EvalContext) (Value, bool) { return i, true }

// Unify unifies the integer with a value.
func (i Integer) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, i) {
				yield(ctx)
			}
		case Integer:
			if x == i {
				yield(ctx)
			}
		}
	}
}

func (i Integer) profile(ctx *EvalContext) string { return strconv.Itoa(int(i)) }

// Float is a float value.
type Float float64

func (f Float) String() string { return fmt.Sprintf("%f", f) }

// Type returns the type of the float.
func (f Float) Type(ctx *EvalContext) *Type {
	return &Type{Name: "float"}
}

// IsGround returns whether the value is ground.
func (f Float) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the float, which is the float itself.
func (f Float) Ground(ctx *EvalContext) (Value, bool) { return f, true }

// TryGround tries to return the ground value of the float, which is the float itself.
func (f Float) TryGround(ctx *EvalContext) (Value, bool) { return f, true }

// Unify unifies the float with a value.
func (f Float) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, f) {
				yield(ctx)
			}
		case Float:
			if x == f {
				yield(ctx)
			}
		}
	}
}

func (f Float) profile(ctx *EvalContext) string { return fmt.Sprintf("%f", f) }

// Pointer is a pointer value.
type Pointer struct {
	ptr unsafe.Pointer
}

func (p Pointer) String() string { return fmt.Sprintf("%p", p.ptr) }

// Type returns the type of the pointer.
func (p Pointer) Type(ctx *EvalContext) *Type {
	return &Type{Name: "pointer"}
}

// IsGround returns whether the value is ground.
func (p Pointer) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the pointer, which is the pointer itself.
func (p Pointer) Ground(ctx *EvalContext) (Value, bool) { return p, true }

// TryGround tries to return the ground value of the pointer, which is the pointer itself.
func (p Pointer) TryGround(ctx *EvalContext) (Value, bool) { return p, true }

// Unify unifies the pointer with a value.
func (p Pointer) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, p) {
				yield(ctx)
			}
		case Pointer:
			if x.ptr == p.ptr {
				yield(ctx)
			}
		}
	}
}

func (p Pointer) profile(ctx *EvalContext) string { return fmt.Sprintf("%p", p.ptr) }

// Channel is a channel value.
type Channel struct {
	Ch chan Value
}

func (ch *Channel) String() string { return fmt.Sprintf("%p", ch.Ch) }

// Type returns the type of the channel.
func (ch *Channel) Type(ctx *EvalContext) *Type {
	return &Type{Name: "channel"}
}

// IsGround returns whether the value is ground.
func (ch *Channel) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the channel, which is the channel itself.
func (ch *Channel) Ground(ctx *EvalContext) (Value, bool) { return ch, true }

// TryGround tries to return the ground value of the channel, which is the channel itself.
func (ch *Channel) TryGround(ctx *EvalContext) (Value, bool) { return ch, true }

// Unify unifies the channel with a value.
func (ch *Channel) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, ch) {
				yield(ctx)
			}
		case *Channel:
			if x.Ch == ch.Ch {
				yield(ctx)
			}
		}
	}
}

func (ch *Channel) profile(ctx *EvalContext) string { return fmt.Sprintf("%p", ch.Ch) }

// Nil is a nil value. Nils are empty lists.
type Nil struct{}

func (n Nil) String() string { return "[]" }

// Type returns the type of the nil.
func (n Nil) Type(ctx *EvalContext) *Type {
	return &Type{Name: "nil"}
}

// IsGround returns whether the value is ground.
func (n Nil) IsGround(ctx *EvalContext) bool { return true }

// Ground returns the ground value of the nil, which is the nil itself.
func (n Nil) Ground(ctx *EvalContext) (Value, bool) { return n, true }

// TryGround tries to return the ground value of the nil, which is the nil itself.
func (n Nil) TryGround(ctx *EvalContext) (Value, bool) { return n, true }

// Unify unifies the nil with a value.
func (n Nil) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, n) {
				yield(ctx)
			}
		case Nil:
			yield(ctx)
		}
	}
}

func (n Nil) profile(ctx *EvalContext) string { return "[]" }

// CompoundTerm is a compound term.
type CompoundTerm struct {
	Functor string
	Args    []Value
}

func (t *CompoundTerm) String() string {
	var sb strings.Builder
	if t.Functor == "." {
		sb.WriteRune('[')
		sb.WriteString(t.Args[0].String())
		sb.WriteRune('|')
		sb.WriteString(t.Args[1].String())
		sb.WriteRune(']')
	} else {
		sb.WriteString(t.Functor)
		if len(t.Args) > 0 {
			sb.WriteRune('(')
			for i, arg := range t.Args {
				if i > 0 {
					sb.WriteString(", ")
				}
				sb.WriteString(arg.String())
			}
			sb.WriteRune(')')
		}
	}
	return sb.String()
}

// Type returns the type of the compound term.
func (t *CompoundTerm) Type(ctx *EvalContext) *Type {
	args := make([]*Type, len(t.Args))
	for i, arg := range t.Args {
		args[i] = arg.Type(ctx)
	}
	return &Type{Name: t.Functor, Args: args}
}

// IsGround returns whether the value is ground.
func (t *CompoundTerm) IsGround(ctx *EvalContext) bool {
	for _, arg := range t.Args {
		if !arg.IsGround(ctx) {
			return false
		}
	}
	return true
}

// Ground returns the ground value of the compound term.
func (t *CompoundTerm) Ground(ctx *EvalContext) (Value, bool) {
	args := make([]Value, len(t.Args))
	for i, arg := range t.Args {
		arg, ok := arg.Ground(ctx)
		if !ok {
			return nil, false
		}
		args[i] = arg
	}
	return &CompoundTerm{Functor: t.Functor, Args: args}, true
}

// TryGround tries to return the ground value of the compound term.
func (t *CompoundTerm) TryGround(ctx *EvalContext) (Value, bool) {
	args := make([]Value, len(t.Args))
	ground := true
	for i, arg := range t.Args {
		arg2, ok := arg.TryGround(ctx)
		if !ok {
			ground = false
		}
		args[i] = arg2
	}
	return &CompoundTerm{Functor: t.Functor, Args: args}, ground
}

// Unify unifies the compound term with a value.
func (t *CompoundTerm) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, t) {
				yield(ctx)
			}
		case *CompoundTerm:
			if t.Functor == x.Functor && len(t.Args) == len(x.Args) {
				for ctx := range unifyListsFrom(ctx, t.Args, x.Args, 0) {
					yield(ctx)
				}
			}
		}
	}
}

func (t *CompoundTerm) profile(ctx *EvalContext) string {
	var sb strings.Builder
	for i, arg := range t.Args {
		if i > 0 {
			sb.WriteRune(':')
		}
		sb.WriteString(arg.profile(ctx))
	}
	return sb.String()
}

// AVM is an attribute-value matrix.
type AVM struct {
	Map map[string]Value
}

func (m *AVM) String() string {
	var sb strings.Builder
	sb.WriteByte('{')
	first := true
	for k, v := range m.Map {
		if first {
			first = false
		} else {
			sb.WriteString(", ")
		}
		sb.WriteString(k)
		sb.WriteString("=")
		sb.WriteString(v.String())
	}
	sb.WriteByte('}')
	return sb.String()
}

// Type returns the type of the AVM.
func (m *AVM) Type(ctx *EvalContext) *Type {
	return &Type{Name: "avm"}
}

// IsGround returns whether the value is ground.
func (m *AVM) IsGround(ctx *EvalContext) bool {
	for _, v := range m.Map {
		if !v.IsGround(ctx) {
			return false
		}
	}
	return true
}

// Ground returns the ground value of the AVM.
func (m *AVM) Ground(ctx *EvalContext) (Value, bool) {
	m2 := make(map[string]Value, len(m.Map))
	for k, v := range m.Map {
		v, ok := v.Ground(ctx)
		if !ok {
			return nil, false
		}
		m2[k] = v
	}
	return &AVM{Map: m2}, true
}

// TryGround tries to return the ground value of the AVM.
func (m *AVM) TryGround(ctx *EvalContext) (Value, bool) {
	m2 := make(map[string]Value, len(m.Map))
	for k, v := range m.Map {
		if v2, ok := v.TryGround(ctx); ok {
			m2[k] = v2
		} else {
			m2[k] = v
		}
	}
	return &AVM{Map: m2}, true
}

// Unify unifies the AVM with a value.
func (m *AVM) Unify(ctx *EvalContext, val Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		switch x := val.(type) {
		case *Var:
			for ctx := range x.Unify(ctx, m) {
				yield(ctx)
			}
		case *AVM:
			zipMaps(ctx, m.Map, x.Map, func(r map[string]Value) {
				om := m.Map
				m.Map = r
				ox := x.Map
				x.Map = r
				yield(ctx)
				m.Map = om
				x.Map = ox
			})
		}
	}
}

func zipMaps(ctx *EvalContext, m1, m2 map[string]Value, cb func(map[string]Value)) {
	pairs1 := mapPairs(m1)
	pairs2 := mapPairs(m2)
	zipMapPairs(ctx, pairs1, pairs2, 0, 0, make(map[string]Value), cb)
}

func zipMapPairs(ctx *EvalContext, pairs1, pairs2 []keyValuePair, i, j int, m map[string]Value, cb func(map[string]Value)) {
	l1, l2 := len(pairs1), len(pairs2)
	switch {
	case i == l1 && j == l2:
		cb(m)
	case j == l2:
		p := pairs1[i]
		m[p.key] = p.value
		zipMapPairs(ctx, pairs1, pairs2, i+1, j, m, cb)
	case i == l1:
		p := pairs2[j]
		m[p.key] = p.value
		zipMapPairs(ctx, pairs1, pairs2, i, j+1, m, cb)
	default:
		p1 := pairs1[i]
		p2 := pairs2[j]
		switch {
		case p1.key < p2.key:
			m[p1.key] = p1.value
			zipMapPairs(ctx, pairs1, pairs2, i+1, j, m, cb)
		case p1.key > p2.key:
			m[p2.key] = p2.value
			zipMapPairs(ctx, pairs1, pairs2, i, j+1, m, cb)
		default:
			for ctx := range p1.value.Unify(ctx, p2.value) {
				m[p1.key] = p1.value
				zipMapPairs(ctx, pairs1, pairs2, i+1, j+1, m, cb)
			}
		}
	}
}

type keyValuePair struct {
	key   string
	value Value
}

func mapPairs(m map[string]Value) []keyValuePair {
	pairs := make([]keyValuePair, 0, len(m))
	for k, v := range m {
		pairs = append(pairs, keyValuePair{k, v})
	}
	sort.Slice(pairs, func(i, j int) bool {
		return pairs[i].key < pairs[j].key
	})
	return pairs
}

func (m *AVM) profile(ctx *EvalContext) string {
	var sb strings.Builder
	sb.WriteByte('{')
	first := true
	for k, v := range m.Map {
		if first {
			first = false
		} else {
			sb.WriteByte(',')
		}
		sb.WriteString(k)
		sb.WriteByte('=')
		sb.WriteString(v.profile(ctx))
	}
	sb.WriteByte('}')
	return sb.String()
}
