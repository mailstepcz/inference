package inference

import (
	"fmt"
)

func ExampleVar_Ground() {
	var (
		x   Var
		ctx EvalContext
	)
	for ctx := range x.Unify(&ctx, Atom("Áth Cliath")) {
		x, ok := x.Ground(ctx)
		fmt.Println(x, ok)
	}
	_, ok := x.Ground(&ctx)
	fmt.Println(ok)
	// Output:
	// Áth Cliath true
	// false
}
