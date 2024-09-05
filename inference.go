package inference

import (
	"context"
	"errors"
	"fmt"
	"io"
	"strings"

	"github.com/fealsamh/go-utils/dbutils"
	"github.com/mailstepcz/sexpr"
	"gopkg.in/yaml.v3"
)

type source struct {
	Predicates []predicate `yaml:"predicates"`
}

type predicate struct {
	Functor string   `yaml:"functor"`
	Args    []string `yaml:"args"`
}

// Engine is an inference engine with a set of predicates.
type Engine struct {
	rules map[Signature][]func(*EvalContext, []Value) func(func(*EvalContext) bool)
}

// NewContext returns a new eval context for the given engine.
func (e *Engine) NewContext(ctx context.Context, db interface {
	dbutils.Querier
	dbutils.Txer
}) *EvalContext {
	return &EvalContext{
		Engine:  e,
		DB:      db,
		Context: ctx,
	}
}

// TypeCheck type checks the set of predicates.
func (e *Engine) TypeCheck(rules map[string][]*Rule, typeAnnots map[string]*ASTTypeAnnot) error {
	for f, rs := range rules {
		ta, ok := typeAnnots[f]
		if !ok {
			return fmt.Errorf("no type annotation for '%s'", f)
		}
		for _, r := range rs {
			varTypes := make(map[string]*Type)
			for i, arg := range r.Head.Args {
				if arg, ok := arg.(Value); ok {
					typ := arg.Type(nil)
					if !ta.Args[i].Type().Eq(typ) {
						return fmt.Errorf("ill-typed argument '%s' of '%s'", arg, f)
					}
					continue
				}
				if vs, ok := arg.(varSym); ok {
					if typ, ok := varTypes[vs.name]; ok {
						if !typ.Eq(ta.Args[i].Type()) {
							return fmt.Errorf("ill-typed argument '$%s' of '%s'", vs, f)
						}
						vs.typ = typ
					} else {
						typ := ta.Args[i].Type()
						varTypes[vs.name] = typ
						vs.typ = typ
					}
				} else {
					panic("unknown type in term template")
				}
			}
		}
	}
	return nil
}

// LoadYAML loads a set of facts for a YAML reader.
func (e *Engine) LoadYAML(r io.Reader) error {
	var source source
	if err := yaml.NewDecoder(r).Decode(&source); err != nil {
		return err
	}
	for _, pred := range source.Predicates {
		vals := make([]Value, len(pred.Args))
		for i, arg := range pred.Args {
			vals[i] = String(arg)
		}
		e.AddRule(Signature{Functor: pred.Functor, Arity: len(pred.Args)}, func(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
			return func(yield func(*EvalContext) bool) {
				for ctx := range unifyListsFrom(ctx, args, vals, 0) {
					if !yield(ctx) {
						return
					}
				}
			}
		})
	}

	return nil
}

// Eval evaluate a goal in the given context.
func (e *Engine) Eval(ctx *EvalContext, functor string, args []Value) func(func(*EvalContext) bool) {
	sig := Signature{Functor: functor, Arity: len(args)}
	funcs, ok := e.rules[sig]
	if !ok {
		panic("undefined predicate " + sig.String())
	}
	return func(yield func(*EvalContext) bool) {
		for _, f := range funcs {
			if ctx.cut {
				ctx.cut = false
				return
			}
			for ctx := range f(ctx, args) {
				if !yield(ctx) {
					return
				}
			}
		}
	}
}

// AddRule adds a rule with a specific signature to the engine.
func (e *Engine) AddRule(sig Signature, f func(*EvalContext, []Value) func(func(*EvalContext) bool)) {
	if e.rules == nil {
		e.rules = make(map[Signature][]func(*EvalContext, []Value) func(func(*EvalContext) bool))
	}
	l := e.rules[sig]
	l = append(l, f)
	e.rules[sig] = l
}

// Signature represents the signature of a predicate.
type Signature struct {
	Functor string
	Arity   int
}

func (s *Signature) String() string { return fmt.Sprintf("%s/%d", s.Functor, s.Arity) }

// TermTemplate is a term template.
type TermTemplate struct {
	Functor string
	Args    []fmt.Stringer
}

func (tt *TermTemplate) String() string {
	var sb strings.Builder
	sb.WriteString(tt.Functor)
	if len(tt.Args) > 0 {
		sb.WriteRune('(')
		for i, arg := range tt.Args {
			if i > 0 {
				sb.WriteString(", ")
			}
			sb.WriteString(arg.String())
		}
		sb.WriteRune(')')
	}
	return sb.String()
}

func (tt *TermTemplate) compoundTerm(vars map[string]*Var) *CompoundTerm {
	args := make([]Value, len(tt.Args))
	for i, arg := range tt.Args {
		switch x := arg.(type) {
		case varSym:
			if x.name == "_" {
				args[i] = new(Var)
			} else {
				v, ok := vars[x.name]
				if !ok {
					v = new(Var)
					vars[x.name] = v
				}
				args[i] = v
			}
		case *TermTemplate:
			args[i] = x.compoundTerm(vars)
		case Value:
			args[i] = x
		}
	}
	return &CompoundTerm{Functor: tt.Functor, Args: args}
}

// Rule is a Horn clause.
type Rule struct {
	Head *TermTemplate
	Tail []*TermTemplate
	SLG  bool
}

func (r *Rule) String() string {
	var sb strings.Builder
	sb.WriteString(r.Head.String())
	if len(r.Tail) > 0 {
		sb.WriteString(" :-")
		for i, x := range r.Tail {
			if i > 0 {
				sb.WriteRune(',')
			}
			sb.WriteRune(' ')
			sb.WriteString(x.String())
		}
	}
	sb.WriteRune('.')
	return sb.String()
}

// HeadSignature returns the signature of the rules head.
func (r *Rule) HeadSignature() Signature {
	return Signature{
		Functor: r.Head.Functor,
		Arity:   len(r.Head.Args),
	}
}

// Func returns a function that returns the range function for the rule.
func (r *Rule) Func() func(*EvalContext, []Value) func(func(*EvalContext) bool) {
	return func(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
		return func(yield func(*EvalContext) bool) {
			vars := make(map[string]*Var)
			head := r.Head.compoundTerm(vars)
			for ctx := range unifyListsFrom(ctx, head.Args, args, 0) {
				var cut bool
				for ctx := range evalTail(ctx, vars, r.Tail, 0, &cut) {
					if !yield(ctx) {
						return
					}
				}
				if cut {
					ctx.cut = true
					return
				}
			}
		}
	}
}

func evalTail(ctx *EvalContext, vars map[string]*Var, tts []*TermTemplate, i int, cut *bool) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if i == len(tts) {
			yield(ctx)
		} else {
			tt := tts[i]
			if tt.Functor == "!" && len(tt.Args) == 0 {
				if cut != nil {
					*cut = true
				}
				for ctx := range evalTail(ctx, vars, tts, i+1, nil) {
					if !yield(ctx) {
						return
					}
				}
			} else {
				t := tt.compoundTerm(vars)
				for ctx := range ctx.Engine.Eval(ctx, t.Functor, t.Args) {
					var cut2 bool
					for ctx := range evalTail(ctx, vars, tts, i+1, &cut2) {
						if !yield(ctx) {
							return
						}
					}
					if cut2 {
						*cut = true
						return
					}
				}
			}
		}
	}
}

type varSym struct {
	name string
	typ  *Type
}

func (v varSym) String() string { return "$" + v.name }

func atomIsVar(s string) bool {
	if len(s) > 0 {
		return s[:1] == strings.ToUpper(s[:1])
	}
	return false
}

// ErrIllFormed signifies a parse error.
var ErrIllFormed = errors.New("parse error")

// NewEngine creates a new inference engine by parsing source code into predicates.
func NewEngine(code string, typeCheck bool) (*Engine, error) {
	r, err := parseCode(code)
	if err != nil {
		return nil, err
	}
	stmts, ok := r.([]AST)
	if !ok {
		panic("unexpected type of parser output")
	}
	var (
		engine     Engine
		typeAnnots = make(map[string]*ASTTypeAnnot)
		rules      = make(map[string][]*Rule)
	)
	for _, stmt := range stmts {
		switch stmt := stmt.(type) {
		case *ASTRule:
			head := stmt.Head.Template()
			tail := make([]*TermTemplate, len(stmt.Tail))
			for i, t := range stmt.Tail {
				tail[i] = t.Template()
			}
			r := &Rule{Head: head, Tail: tail}
			sig := r.HeadSignature()
			engine.AddRule(sig, r.Func())
			rules[sig.Functor] = append(rules[sig.Functor], r)
		case *ASTTypeAnnot:
			typeAnnots[stmt.Selector] = stmt
		case *ASTSLGDirective:
			return nil, errors.ErrUnsupported
		default:
			panic("unexpected type of AST")
		}
	}
	if typeCheck {
		if err := engine.TypeCheck(rules, typeAnnots); err != nil {
			return nil, err
		}
	}
	return &engine, nil
}

// NewEngineFromSymbolicExpression creates a new inference engine from a symbolic expression.
func NewEngineFromSymbolicExpression(code string) (*Engine, error) {
	expr, err := sexpr.Parse(code)
	if err != nil {
		return nil, err
	}
	var engine Engine
	for _, rule := range expr {
		if rule, ok := rule.([]interface{}); ok {
			if len(rule) == 0 {
				return nil, ErrIllFormed
			}
			if _, ok := rule[0].(sexpr.Identifier); ok {
				continue
			}
			if ex, ok := rule[0].([]interface{}); ok {
				head, err := exprToTermTemplate(ex)
				if err != nil {
					return nil, err
				}
				tail := make([]*TermTemplate, 0, len(rule)-1)
				for _, ex := range rule[1:] {
					if ex, ok := ex.(sexpr.Identifier); ok && ex == "!" {
						tail = append(tail, &TermTemplate{Functor: "!"})
						continue
					}
					if ex, ok := ex.([]interface{}); ok {
						tt, err := exprToTermTemplate(ex)
						if err != nil {
							return nil, err
						}
						tail = append(tail, tt)
					} else {
						return nil, ErrIllFormed
					}
				}
				r := &Rule{Head: head, Tail: tail}
				engine.AddRule(r.HeadSignature(), r.Func())
			} else {
				return nil, ErrIllFormed
			}
		} else {
			return nil, ErrIllFormed
		}
	}
	return &engine, nil
}

func exprToTermTemplate(expr []interface{}) (*TermTemplate, error) {
	functor, ok := expr[0].(sexpr.Identifier)
	if !ok {
		return nil, ErrIllFormed
	}
	args := make([]fmt.Stringer, 0, len(expr)-1)
	for _, arg := range expr[1:] {
		switch x := arg.(type) {
		case sexpr.Identifier:
			if atomIsVar(string(x)) {
				args = append(args, varSym{name: string(x)})
			} else {
				args = append(args, Atom(x))
			}
		case sexpr.QuotedString:
			args = append(args, String(x))
		case []interface{}:
			tt, err := exprToTermTemplate(x)
			if err != nil {
				return nil, err
			}
			args = append(args, tt)
		}
	}
	return &TermTemplate{Functor: string(functor), Args: args}, nil
}
