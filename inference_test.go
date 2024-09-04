package inference

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestFacts(t *testing.T) {
	req := require.New(t)

	var e Engine

	f := &Rule{Head: &TermTemplate{Functor: "user", Args: []fmt.Stringer{Atom("u1")}}}
	e.AddRule(f.HeadSignature(), f.Func())
	f = &Rule{Head: &TermTemplate{Functor: "user", Args: []fmt.Stringer{Atom("u2")}}}
	e.AddRule(f.HeadSignature(), f.Func())
	f = &Rule{Head: &TermTemplate{Functor: "user", Args: []fmt.Stringer{Atom("u3")}}}
	e.AddRule(f.HeadSignature(), f.Func())

	var (
		ctx EvalContext
		x   Var
		r   []string
	)
	for ctx := range e.Eval(&ctx, "user", []Value{&x}) {
		req.True(x.IsGround(ctx))
		v, ok := x.Ground(ctx)
		req.True(ok)
		r = append(r, v.String())
	}
	req.Equal([]string{"u1", "u2", "u3"}, r)
}

func TestYAMLFacts(t *testing.T) {
	req := require.New(t)

	var e Engine

	err := e.LoadYAML(strings.NewReader(`predicates:
- functor: user
  args:
  - u1
- functor: user
  args:
  - u2
- functor: user
  args:
  - u3
`))
	req.NoError(err)

	var (
		ctx EvalContext
		x   Var
		r   []string
	)
	for ctx := range e.Eval(&ctx, "user", []Value{&x}) {
		req.True(x.IsGround(ctx))
		x, _ := x.Ground(ctx)
		r = append(r, string(x.(String)))
	}
	req.Equal([]string{"u1", "u2", "u3"}, r)
}

func TestSwapRule(t *testing.T) {
	req := require.New(t)

	var e Engine

	f := &Rule{Head: &TermTemplate{Functor: "pair1", Args: []fmt.Stringer{Atom("a"), Atom("b")}}}
	e.AddRule(f.HeadSignature(), f.Func())
	f = &Rule{Head: &TermTemplate{Functor: "pair1", Args: []fmt.Stringer{Atom("c"), Atom("d")}}}
	e.AddRule(f.HeadSignature(), f.Func())
	r1 := &Rule{Head: &TermTemplate{Functor: "pair2", Args: []fmt.Stringer{varSym{name: "x"}, varSym{name: "y"}}},
		Tail: []*TermTemplate{
			{Functor: "pair1", Args: []fmt.Stringer{varSym{name: "y"}, varSym{name: "x"}}},
		}}
	e.AddRule(r1.HeadSignature(), r1.Func())

	var (
		ctx  = EvalContext{Engine: &e}
		x, y Var
		r    []string
	)
	for ctx := range e.Eval(&ctx, "pair2", []Value{&x, &y}) {
		req.True(x.IsGround(ctx))
		req.True(y.IsGround(ctx))
		v1, _ := x.Ground(ctx)
		v2, _ := y.Ground(ctx)
		r = append(r, v1.String()+","+v2.String())
	}
	req.Equal([]string{"b,a", "d,c"}, r)
}

func TestEngineSexprParser(t *testing.T) {
	req := require.New(t)

	e, err := NewEngineFromSymbolicExpression(`(
		(# some comment)
		((edge a b))
		((edge b c))
		((edge c d))
		((twoedges X Y) (edge X Z) (edge Z Y))
	)`)
	req.NoError(err)
	req.NotNil(e)

	var (
		ctx  = EvalContext{Engine: e}
		x, y Var
		r    []string
	)
	for ctx := range e.Eval(&ctx, "twoedges", []Value{&x, &y}) {
		req.True(x.IsGround(ctx))
		req.True(y.IsGround(ctx))
		v1, _ := x.Ground(ctx)
		v2, _ := y.Ground(ctx)
		r = append(r, v1.String()+","+v2.String())
	}
	req.Equal([]string{"a,c", "b,d"}, r)
}

func TestEngineParser(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		# some comment
		a edge: b.
		b edge: c.
		c edge: d.
		X twoEdges: Y :- X edge: Z, Z edge: Y.
		[] length: 0.
		[X|L] length: Len :- L length: Len1, Len is: Len1 plus: 1.
		L test :- [1, 2, 3, 4, 5] length: L.
		X eq: X.
		X test2 :- (1234 pred) eq: (X pred).
	`, false)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{Functor: "is:plus:", Arity: 3}, BuiltinIsPlus)

	var (
		ctx  = EvalContext{Engine: e}
		x, y Var
		r    []string
	)
	for ctx := range e.Eval(&ctx, "twoEdges:", []Value{&x, &y}) {
		req.True(x.IsGround(ctx))
		req.True(y.IsGround(ctx))
		v1, _ := x.Ground(ctx)
		v2, _ := y.Ground(ctx)
		r = append(r, v1.String()+","+v2.String())
	}
	req.Equal([]string{"a,c", "b,d"}, r)

	r = nil
	for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
		req.True(x.IsGround(ctx))
		v1, _ := x.Ground(ctx)
		r = append(r, v1.String())
	}
	req.Equal([]string{"5"}, r)

	r = nil
	for ctx := range e.Eval(&ctx, "test2", []Value{&x}) {
		req.True(x.IsGround(ctx))
		v1, _ := x.Ground(ctx)
		r = append(r, v1.String())
	}
	req.Equal([]string{"1234"}, r)
}

func TestAVMMapConversion(t *testing.T) {
	t.Run("conversion both ways", func(t *testing.T) {
		req := require.New(t)

		m := map[string]Value{
			"a": String("abcd"),
			"b": Integer(1234),
		}
		avm, tail := AVMFromMap(m)
		for ctx := range tail.Unify(new(EvalContext), Nil{}) {
			avm, _ := avm.TryGround(ctx)
			m2, err := MapFromAVM(avm)
			req.Nil(err)
			req.Equal(2, len(m2))
			req.Equal(String("abcd"), m2["a"])
			req.Equal(Integer(1234), m2["b"])
		}
	})

	t.Run("parser check", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		X stripFreeTail: [] :- X free, !.
		[X|L] stripFreeTail: [X|K] :- L stripFreeTail: K.

		X test :- {a: 1, b: 2, c: 3} stripFreeTail: X.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		e.AddRule(Signature{Functor: "free", Arity: 1}, BuiltinFree)

		var (
			ctx = e.NewContext(nil, nil)
			x   Var
			r   []string
		)
		for ctx := range e.Eval(ctx, "test", []Value{&x}) {
			v1, ok := x.TryGround(ctx)
			req.True(ok)
			r = append(r, v1.String())
			m, err := MapFromAVM(v1)
			req.Nil(err)
			req.Equal(map[string]Value{"a": Integer(1), "b": Integer(2), "c": Integer(3)}, m)
		}
		req.Equal(1, len(r))
	})
}

func TestAVMUnification(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		X unify: X :- !.
		[K keyValue: V | Tail] unify: Dag :-
			Dag avmKey: K value: V stripDag: StripDag,
			Tail unify: StripDag.

		[K keyValue: V2 | Tail] avmKey: K value: V1 stripDag: Tail :-
			!,
			V1 unify: V2.
		[Dag | Tail] avmKey: K value: V stripDag: [Dag | NewTail] :-
			!,
			Tail avmKey: K value: V stripDag: NewTail.

		X eq: X.

		X stripFreeTail: [] :- X free, !.
		[X|L] stripFreeTail: [X|K] :- L stripFreeTail: K.

		X test :-
			AVM1 eq: {a: aa, c: cc},
			AVM2 eq: {c: cc, b: bb},
			AVM1 unify: AVM2,
			AVM1 stripFreeTail: X.
	`, false)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{Functor: "free", Arity: 1}, BuiltinFree)

	var (
		ctx = EvalContext{Engine: e}
		x   Var
		r   []string
	)
	for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
		v1, ok := x.TryGround(ctx)
		req.True(ok)
		r = append(r, v1.String())
	}
	req.Equal(1, len(r))
	req.Equal([]string{"[keyValue:(a, aa)|[keyValue:(c, cc)|[keyValue:(b, bb)|[]]]]"}, r)
}

func TestMacros(t *testing.T) {
	t.Run("isString predicate true", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		X test :- X eq: "abcd", X isString.

		X eq: X.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		e.AddRule(Signature{Functor: "isString", Arity: 1}, BuiltinIsString)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			v1, ok := x.TryGround(ctx)
			req.True(ok)
			r = append(r, v1.String())
		}
		req.Equal(1, len(r))
	})

	t.Run("isString predicate false", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		X test :- X eq: 1234, X isString.

		X eq: X.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		e.AddRule(Signature{Functor: "isString", Arity: 1}, BuiltinIsString)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			v1, ok := x.TryGround(ctx)
			req.True(ok)
			r = append(r, v1.String())
		}
		req.Equal(0, len(r))
	})

	t.Run("macro", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		Role permitsOperation: Op forScope: Scope :-
			[functor keyValue: RoleStr | _] unify: Role,
			[functor keyValue: ScopeStr | _] unify: Scope,
			RoleStr permitsOperation: Op forScope: ScopeStr.

		Role permitsOperation: Op forScope: Scope :-
			[functor keyValue: RoleStr, dcCode keyValue: DC | _] unify: Role,
			[functor keyValue: ScopeStr, dcCode keyValue: DC | _] unify: Scope,
			RoleStr permitsOperation: Op forScope: ScopeStr check: equalDC.

		"role1" permitsOperation: "op1" forScope: "scope1".
		"role2" permitsOperation: "op2" forScope: "scope2" check: equalDC.

		X unify: X :- !.
		[K keyValue: V | Tail] unify: Dag :-
			Dag avmKey: K value: V stripDag: StripDag,
			Tail unify: StripDag.

		[K keyValue: V2 | Tail] avmKey: K value: V1 stripDag: Tail :-
			!,
			V1 unify: V2.
		[Dag | Tail] avmKey: K value: V stripDag: [Dag | NewTail] :-
			!,
			Tail avmKey: K value: V stripDag: NewTail.

		[] test :- {functor: "role1"} permitsOperation: "op1" forScope: {functor: "scope1"}.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			v1, ok := x.TryGround(ctx)
			req.True(ok)
			r = append(r, v1.String())
		}
		req.Equal(1, len(r))
		req.Equal([]string{"[]"}, r)
	})

	t.Run("macro with DC check", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		Role permitsOperation: Op forScope: Scope :-
			[functor keyValue: RoleStr | _] unify: Role,
			[functor keyValue: ScopeStr | _] unify: Scope,
			RoleStr permitsOperation: Op forScope: ScopeStr.

		Role permitsOperation: Op forScope: Scope :-
			[functor keyValue: RoleStr, dcCode keyValue: DC | _] unify: Role,
			[functor keyValue: ScopeStr, dcCode keyValue: DC | _] unify: Scope,
			RoleStr permitsOperation: Op forScope: ScopeStr check: equalDC.

		"role1" permitsOperation: "op1" forScope: "scope1".
		"role2" permitsOperation: "op2" forScope: "scope2" check: equalDC.

		X unify: X :- !.
		[K keyValue: V | Tail] unify: Dag :-
			Dag avmKey: K value: V stripDag: StripDag,
			Tail unify: StripDag.

		[K keyValue: V2 | Tail] avmKey: K value: V1 stripDag: Tail :-
			!,
			V1 unify: V2.
		[Dag | Tail] avmKey: K value: V stripDag: [Dag | NewTail] :-
			!,
			Tail avmKey: K value: V stripDag: NewTail.

		[] test :- {functor: "role2", dcCode: dc1} permitsOperation: "op2" forScope: {functor: "scope2", dcCode: dc1}.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			v1, ok := x.TryGround(ctx)
			req.True(ok)
			r = append(r, v1.String())
		}
		req.Equal(1, len(r))
		req.Equal([]string{"[]"}, r)
	})
}

func TestListUnification(t *testing.T) {
	t.Run("open list element", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		X eq: X.

		X test :- [a, b, c | _] eq: [a, X, c | _].
	`, false)
		req.NoError(err)
		req.NotNil(e)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			req.True(x.IsGround(ctx))
			v1, _ := x.Ground(ctx)
			r = append(r, v1.String())
		}
		req.Equal([]string{"b"}, r)
	})

	t.Run("difference lists", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		X eq: X.

		X test :- X eq: ([a, b, c | L] diffList: L), L eq: [1, 2, 3 | K], K eq: [].
	`, false)
		req.NoError(err)
		req.NotNil(e)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			req.True(x.IsGround(ctx))
			v1, _ := x.Ground(ctx)
			r = append(r, v1.String())
		}
		req.Equal([]string{"diffList:([a|[b|[c|[1|[2|[3|[]]]]]]], [1|[2|[3|[]]]])"}, r)
	})
}

func TestSLG(t *testing.T) {
	t.Run("simple cycle", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		@table "cycle:"/2.

		a cycle: b.
		X cycle: Y :- Y cycle: X.

		[X, Y] test :- X cycle: Y.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			req.True(x.IsGround(ctx))
			v1, _ := x.Ground(ctx)
			r = append(r, v1.String())
		}
		req.Equal(2, len(r))
		req.Equal([]string{"[a|[b|[]]]", "[b|[a|[]]]"}, r)
	})

	t.Run("path from edges", func(t *testing.T) {
		req := require.New(t)

		e, err := NewEngine(`
		@table "path:"/2.

		a edge: b.
		b edge: c.
		c edge: a.

		X path: Y :- X edge: Y.
		X path: Z :- X edge: Y, Y path: Z, (X eq: Z) not.

		X not :- X call, !, fail.
		X not.

		X eq: X.

		[X, Y] test :- X path: Y.
	`, false)
		req.NoError(err)
		req.NotNil(e)

		e.AddRule(Signature{Functor: "call", Arity: 1}, BuiltinCall)
		e.AddRule(Signature{Functor: "fail", Arity: 0}, BuiltinFail)

		var (
			ctx = EvalContext{Engine: e}
			x   Var
			r   []string
		)
		for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
			req.True(x.IsGround(ctx))
			v1, _ := x.Ground(ctx)
			r = append(r, v1.String())
		}
		req.Equal([]string{
			"[a|[b|[]]]", "[b|[c|[]]]", "[c|[a|[]]]",
			"[a|[c|[]]]", "[b|[a|[]]]", "[c|[b|[]]]",
		}, r)
	})
}

func TestUnderscoreVar(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		X memberIn: [X|_].
		X memberIn: [_|L] :- X memberIn: L.
		X test :- X memberIn: [a, b, c].
	`, false)
	req.NoError(err)
	req.NotNil(e)

	var (
		ctx = EvalContext{Engine: e}
		x   Var
		r   []string
	)
	for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
		v1, ok := x.Ground(ctx)
		req.True(ok)
		r = append(r, v1.String())
	}
	req.Equal([]string{"a", "b", "c"}, r)
}

func TestChannelSend(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		X test :- 1 sendToChannel: X, 2 sendToChannel: X, 3 sendToChannel: X, X closeChannel.
	`, false)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{Functor: "sendToChannel:", Arity: 2}, BuiltinSendToChannel)
	e.AddRule(Signature{Functor: "closeChannel", Arity: 1}, BuiltinCloseChannel)

	ch := make(chan Value)

	go func() {
		ctx := EvalContext{Engine: e}
		for ctx := range e.Eval(&ctx, "test", []Value{&Channel{Ch: ch}}) {
			ctx.Dummy()
		}
	}()

	var r []string
	for x := range ch {
		r = append(r, x.String())
	}
	req.Equal([]string{"1", "2", "3"}, r)
}

func TestChannelReceive(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		X test: Y :- X receiveAllFromChannel: Y.
	`, false)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{Functor: "receiveAllFromChannel:", Arity: 2}, BuiltinReceiveAllFromChannel)

	ch := make(chan Value)

	go func() {
		ch <- Integer(1)
		ch <- Integer(2)
		ch <- Integer(3)
		close(ch)
	}()

	var (
		ctx = EvalContext{Engine: e}
		x   Var
		r   []string
	)
	for ctx := range e.Eval(&ctx, "test:", []Value{&x, &Channel{Ch: ch}}) {
		v1, ok := x.Ground(ctx)
		req.True(ok)
		r = append(r, v1.String())
	}
	req.Equal([]string{"1", "2", "3"}, r)
}

func TestCut(t *testing.T) {
	req := require.New(t)

	e, err := NewEngineFromSymbolicExpression(`(
		((p1 a))
		((p1 b))
		((p2 c))
		((p2 d))
		((p X Y) (p1 X) ! (p2 Y))
		((p X Y) (p2 X) ! (p1 Y))
	)`)
	req.NoError(err)
	req.NotNil(e)

	var (
		ctx  = EvalContext{Engine: e}
		x, y Var
		r    []string
	)
	for ctx := range e.Eval(&ctx, "p", []Value{&x, &y}) {
		req.True(x.IsGround(ctx))
		req.True(y.IsGround(ctx))
		v1, _ := x.Ground(ctx)
		v2, _ := y.Ground(ctx)
		r = append(r, v1.String()+","+v2.String())
	}
	req.Equal([]string{"a,c", "a,d"}, r)
}

var gr interface{}

func BenchmarkNativeAVMUnification(b *testing.B) {
	e, err := NewEngine(`
		X test :- X eq: <a: 1>, Y eq: <b: 2>, X eq: Y.

		X eq: X.
	`, false)
	if err != nil {
		b.Fatal(err)
	}
	b.ResetTimer()
	var lr interface{}
	for i := 0; i < b.N; i++ {
		ctx := &EvalContext{Engine: e}
		var x Var
		r := make([]interface{}, 0, 10)
		for ctx := range e.Eval(ctx, "test", []Value{&x}) {
			v1, _ := x.Ground(ctx)
			r = append(r, []interface{}{v1})
		}
		lr = r
	}
	gr = lr
}

func BenchmarkOpenAVMUnification(b *testing.B) {
	e, err := NewEngine(`
		X test :- X eq: {a: 1}, Y eq: {b: 2}, X unify: Y.

		X unify: X :- !.
		[K keyValue: V | Tail] unify: Dag :-
			Dag avmKey: K value: V stripDag: StripDag,
			Tail unify: StripDag.

		[K keyValue: V2 | Tail] avmKey: K value: V1 stripDag: Tail :-
			!,
			V1 unify: V2.
		[Dag | Tail] avmKey: K value: V stripDag: [Dag | NewTail] :-
			!,
			Tail avmKey: K value: V stripDag: NewTail.

		X eq: X.
	`, false)
	if err != nil {
		b.Fatal(err)
	}
	b.ResetTimer()
	var lr interface{}
	for i := 0; i < b.N; i++ {
		ctx := &EvalContext{Engine: e}
		var x Var
		r := make([]interface{}, 0, 10)
		for ctx := range e.Eval(ctx, "test", []Value{&x}) {
			v1, _ := x.Ground(ctx)
			r = append(r, []interface{}{v1})
		}
		lr = r
	}
	gr = lr
}

func BenchmarkNativeInference(b *testing.B) {
	p2 := func(ctx *EvalContext, x, y Value) func(func(*EvalContext) bool) {
		return func(yield func(*EvalContext) bool) {
			for ctx := range x.Unify(ctx, Atom("a1")) {
				for ctx := range y.Unify(ctx, Atom("a2")) {
					if !yield(ctx) {
						return
					}
				}
			}
			for ctx := range x.Unify(ctx, Atom("b1")) {
				for ctx := range y.Unify(ctx, Atom("b2")) {
					if !yield(ctx) {
						return
					}
				}
			}
			for ctx := range x.Unify(ctx, Atom("c1")) {
				for ctx := range y.Unify(ctx, Atom("c2")) {
					if !yield(ctx) {
						return
					}
				}
			}
			for ctx := range x.Unify(ctx, Atom("d1")) {
				for ctx := range y.Unify(ctx, Atom("d2")) {
					if !yield(ctx) {
						return
					}
				}
			}
		}
	}
	p1 := func(ctx *EvalContext, x, y Value) func(func(*EvalContext) bool) {
		return func(yield func(*EvalContext) bool) {
			for ctx := range p2(ctx, x, y) {
				if !yield(ctx) {
					return
				}
			}
		}
	}
	b.ResetTimer()
	var lr interface{}
	for i := 0; i < b.N; i++ {
		ctx := new(EvalContext)
		var x, y Var
		r := make([]interface{}, 0, 10)
		for ctx := range p1(ctx, &x, &y) {
			v1, _ := x.Ground(ctx)
			v2, _ := y.Ground(ctx)
			r = append(r, []interface{}{v1, v2})
		}
		lr = r
	}
	gr = lr
}

func BenchmarkCodeInference(b *testing.B) {
	e, err := NewEngineFromSymbolicExpression(`(
		((p1 X Y) (p2 X Y))
		((p2 a1 a2))
		((p2 b1 b2))
		((p2 c1 c2))
		((p2 d1 d2))
	)`)
	if err != nil {
		b.Fatal(err)
	}
	b.ResetTimer()
	var lr interface{}
	for i := 0; i < b.N; i++ {
		ctx := &EvalContext{Engine: e}
		var x, y Var
		r := make([]interface{}, 0, 10)
		for ctx := range e.Eval(ctx, "p1", []Value{&x, &y}) {
			v1, _ := x.Ground(ctx)
			v2, _ := y.Ground(ctx)
			r = append(r, []interface{}{v1, v2})
		}
		lr = r
	}
	gr = lr
}

func BenchmarkNumericRange(b *testing.B) {
	var lr interface{}
	for i := 0; i < b.N; i++ {
		var r []interface{}
		for i := 0; i < 1_000; i++ {
			r = append(r, i)
		}
		lr = r
	}
	gr = lr
}

func BenchmarkRangeFunc(b *testing.B) {
	rf := func() func(func(interface{}) bool) {
		return func(yield func(interface{}) bool) {
			for i := 0; i < 1_000; i++ {
				if !yield(i) {
					return
				}
			}
		}
	}
	var lr interface{}
	for i := 0; i < b.N; i++ {
		var r []interface{}
		for i := range rf() {
			r = append(r, i)
		}
		lr = r
	}
	gr = lr
}
