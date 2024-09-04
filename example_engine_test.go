package inference

import (
	"fmt"
)

func ExampleNewEngine() {
	e, err := NewEngine(`
		[] length: 0.
		[X|L] length: Len :- L length: Len1, Len is: Len1 plus: 1.
		L test :- [1, 2, 3, 4, 5] length: L.
	`, false)
	if err != nil {
		panic(err)
	}
	e.AddRule(Signature{Functor: "is:plus:", Arity: 3}, BuiltinIsPlus)
	var (
		x   Var
		ctx = EvalContext{Engine: e}
	)
	for ctx := range e.Eval(&ctx, "test", []Value{&x}) {
		x, ok := x.Ground(ctx)
		fmt.Println(x, ok)
	}
	// Output:
	// 5 true
}
