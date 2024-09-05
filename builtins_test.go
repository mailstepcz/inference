package inference

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestBuiltins(t *testing.T) {
	req := require.New(t)

	e, err := NewEngineFromSymbolicExpression(`(
		((testVar X "free") (free X))
		((testVar X "ground") (ground X))
		((wihajster a))
		((wihajster b))
		((wihajster c))
		((list X) (call (wihajster X)))
	)`)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{
		Functor: "free",
		Arity:   1,
	}, BuiltinFree)
	e.AddRule(Signature{
		Functor: "ground",
		Arity:   1,
	}, BuiltinGround)
	e.AddRule(Signature{
		Functor: "call",
		Arity:   1,
	}, BuiltinCall)

	ctx := &EvalContext{
		Engine: e,
	}

	var v1, v2 Var

	for ctx := range e.Eval(ctx, "testVar", []Value{&v1, &v2}) {
		if s, ok := v2.Ground(ctx); !ok || s != String("free") {
			t.Errorf("evaluation of 'free' should return 'free'")
		}
	}

	for ctx := range v1.Unify(ctx, String("abcd")) {
		for ctx := range e.Eval(ctx, "testVar", []Value{&v1, &v2}) {
			if s, ok := v2.Ground(ctx); !ok || s != String("ground") {
				t.Errorf("evaluation of 'ground' should return 'ground'")
			}
		}
	}

	var r []string
	for ctx := range e.Eval(ctx, "list", []Value{&v1}) {
		v, _ := v1.Ground(ctx)
		r = append(r, string(v.(Atom)))
	}
	req.Equal([]string{"a", "b", "c"}, r)
}

func TestBagOf(t *testing.T) {
	req := require.New(t)

	e, err := NewEngineFromSymbolicExpression(`(
		((wihajster a))
		((wihajster b))
		((wihajster c))
		((list X) (bagOf X (wihajster Y)))
	)`)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{
		Functor: "bagOf",
		Arity:   2,
	}, BuiltinBagOf)

	ctx := &EvalContext{
		Engine: e,
	}

	var v1 Var

	var r []string
	for ctx := range e.Eval(ctx, "list", []Value{&v1}) {
		v, ok := v1.Ground(ctx)
		req.True(ok)
		r = append(r, v.(*CompoundTerm).String())
	}
	req.Equal([]string{"[wihajster(a)|[wihajster(b)|[wihajster(c)|[]]]]"}, r)
}

func TestListTermConversion(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		X test1 :- X termAsList: [a, b, c].
		X test2 :- (a sel1: b sel2: c) termAsList: X.
	`, false)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{
		Functor: "termAsList:",
		Arity:   2,
	}, BuiltinTermAsList)

	ctx := &EvalContext{
		Engine: e,
	}

	var v1 Var

	var r []string
	for ctx := range e.Eval(ctx, "test1", []Value{&v1}) {
		v, ok := v1.Ground(ctx)
		req.True(ok)
		r = append(r, v.(*CompoundTerm).String())
	}
	req.Equal([]string{"a(b, c)"}, r)

	r = nil
	for ctx := range e.Eval(ctx, "test2", []Value{&v1}) {
		v, ok := v1.Ground(ctx)
		req.True(ok)
		r = append(r, v.(*CompoundTerm).String())
	}
	req.Equal([]string{"[sel1:sel2:|[a|[b|[c|[]]]]]"}, r)
}
