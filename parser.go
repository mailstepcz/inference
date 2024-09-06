package inference

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/phomola/lrparser"
	"github.com/phomola/textkit"
)

var (
	grammar = lrparser.NewGrammar(lrparser.MustBuildRules([]*lrparser.SynSem{
		{Syn: `Init -> Stmts`, Sem: func(args []any) any { return args[0] }},
		{Syn: `Stmts -> Stmts Stmt`, Sem: func(args []any) any { return append(args[0].([]AST), args[1].(AST)) }},
		{Syn: `Stmts -> Stmt`, Sem: func(args []any) any { return []AST{args[0].(AST)} }},
		{Syn: `Stmt -> TypeAnnot`, Sem: func(args []any) any { return args[0] }},
		{Syn: `Stmt -> "@table" string "/" integer "."`, Sem: func(args []any) any {
			functor := args[1].(string)
			arity := args[3].(int)
			return &ASTSLGDirective{
				Functor: functor,
				Arity:   arity,
			}
		}},
		{Syn: `Stmt -> Rule`, Sem: func(args []any) any { return args[0] }},
		{Syn: `TypeAnnot -> "%" Selector "~" TypeTuple "."`, Sem: func(args []any) any {
			return &ASTTypeAnnot{Selector: args[1].(string), Args: args[3].([]*ASTType)}
		}},
		{Syn: `TypeTuple -> Type`, Sem: func(args []any) any { return []*ASTType{args[0].(*ASTType)} }},
		{Syn: `TypeTuple -> TypeTuple "*" Type`, Sem: func(args []any) any {
			return append(args[0].([]*ASTType), args[2].(*ASTType))
		}},
		{Syn: `Type -> ident`, Sem: func(args []any) any { return &ASTType{Name: args[0].(string)} }},
		{Syn: `Selector -> ident`, Sem: func(args []any) any { return args[0] }},
		{Syn: `Selector -> ident ":"`, Sem: func(args []any) any { return args[0].(string) + ":" }},
		{Syn: `Selector -> Selector ident ":"`, Sem: func(args []any) any {
			return args[0].(string) + args[1].(string) + ":"
		}},
		{Syn: `Rule -> Term "."`, Sem: func(args []any) any { return &ASTRule{Head: args[0].(*ASTTerm)} }},
		{Syn: `Rule -> Term ":-" Terms "."`, Sem: func(args []any) any {
			return &ASTRule{Head: args[0].(*ASTTerm), Tail: args[2].([]*ASTTerm)}
		}},
		{Syn: `Terms -> Terms "," Term`, Sem: func(args []any) any {
			return append(args[0].([]*ASTTerm), args[2].(*ASTTerm))
		}},
		{Syn: `Terms -> Term`, Sem: func(args []any) any { return []*ASTTerm{args[0].(*ASTTerm)} }},
		{Syn: `Term -> "fail"`, Sem: func(args []any) any { return &ASTTerm{Functor: args[0].(string)} }},
		{Syn: `Term -> "!"`, Sem: func(args []any) any { return &ASTTerm{Functor: args[0].(string)} }},
		{Syn: `Term -> Atomic ident`, Sem: func(args []any) any {
			return &ASTTerm{Functor: args[1].(string), Args: []ASTExpr{args[0].(ASTExpr)}}
		}},
		{Syn: `Term -> Atomic SelVal`, Sem: func(args []any) any {
			selVal := args[1].(*selVal)
			return &ASTTerm{Functor: selVal.selPart + ":", Args: []ASTExpr{args[0].(ASTExpr), selVal.value}}
		}},
		{Syn: `Term -> Term SelVal`, Sem: func(args []any) any {
			t := args[0].(*ASTTerm)
			selVal := args[1].(*selVal)
			return &ASTTerm{Functor: t.Functor + selVal.selPart + ":", Args: append(t.Args, selVal.value)}
		}},
		{Syn: `SelVal -> ident ":" Atomic`, Sem: func(args []any) any {
			return &selVal{selPart: args[0].(string), value: args[2].(ASTExpr)}
		}},
		{Syn: `Expr -> Atomic`, Sem: func(args []any) any { return args[0] }},
		{Syn: `Expr -> Term`, Sem: func(args []any) any { return args[0] }},
		{Syn: `Atomic -> "(" Expr ")`, Sem: func(args []any) any { return args[1] }},
		{Syn: `Atomic -> ident`, Sem: func(args []any) any { return &ASTIdent{Name: args[0].(string)} }},
		{Syn: `Atomic -> string`, Sem: func(args []any) any { return &ASTString{Value: args[0].(string)} }},
		{Syn: `Atomic -> integer`, Sem: func(args []any) any { return &ASTInteger{Value: args[0].(int)} }},
		{Syn: `Atomic -> "[" "]"`, Sem: func(args []any) any { return new(ASTNil) }},
		{Syn: `Atomic -> "[" List "]"`, Sem: func(args []any) any {
			list := args[1].([]ASTExpr)
			return termFromList(list, new(ASTNil))
		}},
		{Syn: `Atomic -> "[" List "|" Expr "]"`, Sem: func(args []any) any {
			list := args[1].([]ASTExpr)
			return termFromList(list, args[3].(ASTExpr))
		}},
		{Syn: `List -> Expr`, Sem: func(args []any) any { return []ASTExpr{args[0].(ASTExpr)} }},
		{Syn: `List -> Expr "," List`, Sem: func(args []any) any {
			return append([]ASTExpr{args[0].(ASTExpr)}, args[2].([]ASTExpr)...)
		}},
		{Syn: `Atomic -> "{" PairList "}"`, Sem: func(args []any) any {
			list := args[1].([]ASTExpr)
			return termFromList(list, &ASTIdent{Name: "_"})
		}},
		{Syn: `Atomic -> "<" PairList2 ">"`, Sem: func(args []any) any {
			pairs := args[1].([]*ASTKVPair)
			m := make(map[string]ASTExpr, len(pairs))
			for _, p := range pairs {
				m[p.Key] = p.Value
			}
			return &ASTAVM{Map: m}
		}},
		{Syn: `PairList -> ident ":" Expr`, Sem: func(args []any) any {
			return []ASTExpr{
				&ASTTerm{Functor: "keyValue:", Args: []ASTExpr{&ASTIdent{Name: args[0].(string)}, args[2].(ASTExpr)}},
			}
		}},
		{Syn: `PairList -> ident ":" Expr "," PairList`, Sem: func(args []any) any {
			return append(
				[]ASTExpr{
					&ASTTerm{Functor: "keyValue:", Args: []ASTExpr{&ASTIdent{Name: args[0].(string)}, args[2].(ASTExpr)}},
				},
				args[4].([]ASTExpr)...,
			)
		}},
		{Syn: `PairList2 -> ident ":" Expr`, Sem: func(args []any) any {
			return []*ASTKVPair{
				&ASTKVPair{Key: args[0].(string), Value: args[2].(ASTExpr)},
			}
		}},
		{Syn: `PairList2 -> ident ":" Expr "," PairList2`, Sem: func(args []any) any {
			return append(
				[]*ASTKVPair{
					&ASTKVPair{Key: args[0].(string), Value: args[2].(ASTExpr)},
				},
				args[4].([]*ASTKVPair)...,
			)
		}},
	}))
)

// Type is a type checked by the type checker.
type Type struct {
	Name string
	Args []*Type
}

// Eq compares two types.
func (t *Type) Eq(t2 *Type) bool {
	if t.Name != t2.Name || len(t.Args) != len(t2.Args) {
		return false
	}
	for i, arg := range t.Args {
		arg2 := t2.Args[i]
		if !arg.Eq(arg2) {
			return false
		}
	}
	return true
}

func (t *Type) String() string {
	var sb strings.Builder
	sb.WriteString(t.Name)
	if len(t.Args) > 0 {
		sb.WriteRune('(')
		for i, arg := range t.Args {
			if i > 0 {
				sb.WriteRune(',')
			}
			sb.WriteString(arg.String())
		}
		sb.WriteRune(')')
	}
	return sb.String()
}

// AST is an abstract syntax tree.
type AST interface {
	fmt.Stringer
}

// ASTType is a type node.
type ASTType struct {
	Name string
	Loc  textkit.Location
}

func (t *ASTType) String() string { return t.Name }

// Type returns the type represented by the node.
func (t *ASTType) Type() *Type {
	return &Type{Name: t.Name}
}

// ASTTypeAnnot is a type annotation node.
type ASTTypeAnnot struct {
	Selector string
	Args     []*ASTType
	Loc      textkit.Location
}

func (t *ASTTypeAnnot) String() string {
	var sb strings.Builder
	sb.WriteString(t.Selector)
	sb.WriteString(" ~ ")
	for i, arg := range t.Args {
		if i > 0 {
			sb.WriteString(" * ")
		}
		sb.WriteString(arg.String())
	}
	return sb.String()
}

type selVal struct {
	selPart string
	value   ASTExpr
}

// ASTNil is a nil node.
type ASTNil struct {
	Loc textkit.Location
}

func (n *ASTNil) String() string { return "[]" }

// ASTTerm is a compound term node.
type ASTTerm struct {
	Functor string
	Args    []ASTExpr
	Loc     textkit.Location
}

// Template return the term template for the node.
func (t *ASTTerm) Template() *TermTemplate {
	args := make([]fmt.Stringer, len(t.Args))
	for i, arg := range t.Args {
		switch x := arg.(type) {
		case *ASTString:
			args[i] = String(x.Value)
		case *ASTInteger:
			args[i] = Integer(x.Value)
		case *ASTIdent:
			if x.Name[:1] == strings.ToUpper(x.Name[:1]) {
				args[i] = varSym{name: x.Name}
			} else {
				args[i] = Atom(x.Name)
			}
		case *ASTNil:
			args[i] = Nil{}
		case *ASTTerm:
			args[i] = x.Template()
		case *ASTAVM:
			args[i] = x.AsTerm().Template()
		default:
			panic(fmt.Sprintf("unhandled type when converting to template: %T", arg))
		}
	}
	return &TermTemplate{Functor: t.Functor, Args: args}
}

func (t *ASTTerm) String() string {
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

// ASTRule is a rule node.
type ASTRule struct {
	Head *ASTTerm
	Tail []*ASTTerm
	SLG  bool
	Loc  textkit.Location
}

// Rule returns the rule for the node.
func (r *ASTRule) Rule() *Rule {
	tail := make([]*TermTemplate, len(r.Tail))
	for i, t := range r.Tail {
		tail[i] = t.Template()
	}
	return &Rule{Head: r.Head.Template(), Tail: tail, SLG: r.SLG}
}

func (r *ASTRule) String() string {
	var sb strings.Builder
	sb.WriteString(r.Head.String())
	if len(r.Tail) > 0 {
		for i, t := range r.Tail {
			if i == 0 {
				sb.WriteString(" :- ")
			} else {
				sb.WriteString(", ")
			}
			sb.WriteString(t.String())
		}
	}
	sb.WriteRune('.')
	return sb.String()
}

// ASTExpr is an expression node.
type ASTExpr interface {
	AST
}

// ASTString is a string node.
type ASTString struct {
	Value string
	Loc   textkit.Location
}

func (s *ASTString) String() string { return strconv.Quote(s.Value) }

// ASTInteger is an integer node.
type ASTInteger struct {
	Value int
	Loc   textkit.Location
}

func (i *ASTInteger) String() string { return strconv.Itoa(i.Value) }

// ASTFloat is a float node.
type ASTFloat struct {
	Value float64
	Loc   textkit.Location
}

func (f *ASTFloat) String() string { return fmt.Sprintf("%f", f.Value) }

// ASTIdent is an identifier node.
type ASTIdent struct {
	Name string
	Loc  textkit.Location
}

func (i *ASTIdent) String() string { return i.Name }

// ASTKVPair is a key-value pair.
type ASTKVPair struct {
	Key   string
	Value ASTExpr
	Loc   textkit.Location
}

func (p *ASTKVPair) String() string { return p.Key + ":" + p.Value.String() }

// ASTAVM is an AVM.
type ASTAVM struct {
	Map map[string]ASTExpr
	Loc textkit.Location
}

func (a *ASTAVM) String() string { return fmt.Sprintf("%v", a.Map) }

// AsTerm returns the AVM as a term.
func (a *ASTAVM) AsTerm() *ASTTerm {
	args := make([]ASTExpr, 0, len(a.Map))
	for k, v := range a.Map {
		args = append(args, &ASTTerm{Functor: "_keyValue_", Args: []ASTExpr{&ASTIdent{Name: k}, v}})
	}
	return &ASTTerm{Functor: "_avm_", Args: args, Loc: a.Loc}
}

func parseCode(code string) (interface{}, error) {
	tok := textkit.Tokeniser{
		CommentPrefix: "#",
		StringRune:    '"',
		IdentChars:    "@$'_",
	}
	tokens := tok.Tokenise(code, "")
	tokens = lrparser.CoalesceSymbols(tokens, []string{":-"})
	return grammar.Parse(tokens)
}

// ASTSLGDirective is an SLG directive.
type ASTSLGDirective struct {
	Functor string
	Arity   int
	Loc     textkit.Location
}

func (d *ASTSLGDirective) String() string {
	return fmt.Sprintf("@table %s/%d.", strconv.Quote(d.Functor), d.Arity)
}
