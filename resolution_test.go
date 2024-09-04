package inference

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestVarStringUnification(t *testing.T) {
	req := require.New(t)

	var (
		v   Var
		ctx EvalContext
	)
	req.False(v.IsGround(&ctx))

	for ctx := range v.Unify(&ctx, String("Áth Cliath")) {
		req.True(v.IsGround(ctx))

		b := v.bottom(ctx)
		req.Equal(String("Áth Cliath"), b)
	}

	req.False(v.IsGround(&ctx))
}

func TestVarCompoundUnification(t *testing.T) {
	req := require.New(t)

	var (
		v1, v2 Var
		t1     = &CompoundTerm{Functor: "fn", Args: []Value{&v1, &v2}}
		ctx    EvalContext
	)
	req.False(t1.IsGround(&ctx))

	for ctx := range t1.Unify(&ctx, &CompoundTerm{Functor: "fn", Args: []Value{String("a1"), String("a2")}}) {
		req.True(t1.IsGround(ctx))

		t2, _ := t1.Ground(ctx)
		args := t2.(*CompoundTerm).Args
		req.Equal(String("a1"), args[0])
		req.Equal(String("a2"), args[1])
	}

	req.False(t1.IsGround(&ctx))
}

func TestNativeAVMUnification(t *testing.T) {
	req := require.New(t)

	avm1 := &AVM{Map: map[string]Value{
		"a": Atom("aa"),
	}}
	avm2 := &AVM{Map: map[string]Value{
		"b": Atom("bb"),
	}}

	var ctx EvalContext
	for ctx := range avm1.Unify(&ctx, avm2) {
		avm1, ok := avm1.Ground(ctx)
		req.True(ok)
		avm2, ok := avm2.Ground(ctx)
		req.True(ok)
		req.Equal(map[string]Value{
			"a": Atom("aa"),
			"b": Atom("bb"),
		}, avm1.(*AVM).Map)
		req.Equal(map[string]Value{
			"a": Atom("aa"),
			"b": Atom("bb"),
		}, avm2.(*AVM).Map)
	}

	req.Equal(map[string]Value{
		"a": Atom("aa"),
	}, avm1.Map)
	req.Equal(map[string]Value{
		"b": Atom("bb"),
	}, avm2.Map)
}
