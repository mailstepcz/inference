package inference

import "fmt"

// BuiltinSendToChannel is an in-built predicate for sending data to channels.
func BuiltinSendToChannel(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 2 {
			panic("bad number of arguments in call of 'sendToChannel/2'")
		}
		x, ok := args[1].Ground(ctx)
		if !ok {
			panic("channel argument must be ground")
		}
		ch, ok := x.(*Channel)
		if !ok {
			panic("channel argument must be a channel")
		}
		ch.Ch <- args[0]
		yield(ctx)
	}
}

// BuiltinReceiveFromChannel is an in-built predicate for receiving data from channels.
func BuiltinReceiveFromChannel(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 2 {
			panic("bad number of arguments in call of 'receiveFromChannel/2'")
		}
		x, ok := args[1].Ground(ctx)
		if !ok {
			panic("channel argument must be ground")
		}
		ch, ok := x.(*Channel)
		if !ok {
			panic("channel argument must be a channel")
		}
		v := <-ch.Ch
		for ctx := range v.Unify(ctx, args[0]) {
			yield(ctx)
		}
	}
}

// BuiltinReceiveAllFromChannel is an in-built predicate for receiving data from channels in a cycle.
func BuiltinReceiveAllFromChannel(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 2 {
			panic("bad number of arguments in call of 'receiveAllFromChannel/2'")
		}
		x, ok := args[1].Ground(ctx)
		if !ok {
			panic("channel argument must be ground")
		}
		ch, ok := x.(*Channel)
		if !ok {
			panic("channel argument must be a channel")
		}
		for v := range ch.Ch {
			for ctx := range v.Unify(ctx, args[0]) {
				if !yield(ctx) {
					return
				}
			}
		}
	}
}

// BuiltinCloseChannel is an in-built predicate for closing channels.
func BuiltinCloseChannel(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'closeChannel/1'")
		}
		x, ok := args[0].Ground(ctx)
		if !ok {
			panic("channel argument must be ground")
		}
		ch, ok := x.(*Channel)
		if !ok {
			panic("channel argument must be a channel")
		}
		close(ch.Ch)
		yield(ctx)
	}
}

// BuiltinWriteln is an in-built predicate for writing to the standard output.
func BuiltinWriteln(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'writeln/1'")
		}
		x, _ := args[0].TryGround(ctx)
		fmt.Println(x)
		yield(ctx)
	}
}

// BuiltinFail is an in-built predicate which always fails.
func BuiltinFail(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 0 {
			panic("bad number of arguments in call of 'fail/0'")
		}
	}
}

// BuiltinTermAsList is an in-built predicate for converting terms into lists and vice versa.
func BuiltinTermAsList(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 2 {
			panic("bad number of arguments in call of 'termsAsList/2'")
		}
		if t, ok := Bottom(ctx, args[0]).(*CompoundTerm); ok {
			list := append([]Value{Atom(t.Functor)}, t.Args...)
			for ctx := range listFromSlice(list, Nil{}).Unify(ctx, args[1]) {
				if !yield(ctx) {
					return
				}
			}
		} else if t, ok := Bottom(ctx, args[1]).(*CompoundTerm); ok {
			list, err := listFromTerm(t)
			if err != nil {
				panic(err)
			}
			if fnc, ok := list[0].Ground(ctx); ok {
				if fnc, ok := fnc.(Atom); ok {
					for ctx := range args[0].Unify(ctx, &CompoundTerm{Functor: string(fnc), Args: list[1:]}) {
						if !yield(ctx) {
							return
						}
					}
				}
			}
		}
	}
}

// BuiltinIsPlus is an in-built predicate for addition.
func BuiltinIsPlus(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 3 {
			panic("bad number of arguments in call of 'is:plus:/3'")
		}
		a1, ok := args[1].Ground(ctx)
		if !ok {
			panic("'is:plus:' second argument must be ground")
		}
		a2, ok := args[2].Ground(ctx)
		if !ok {
			panic("'is:plus:' third argument must be ground")
		}
		x, ok := a1.(Integer)
		if !ok {
			panic("'is:plus:' second argument must be integer")
		}
		y, ok := a2.(Integer)
		if !ok {
			panic("'is:plus:' third argument must be integer")
		}
		for ctx := range args[0].Unify(ctx, x+y) {
			if !yield(ctx) {
				return
			}
		}
	}
}

// BuiltinIsString is an in-built predicate for checking whether a value is a string.
func BuiltinIsString(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'isString/1'")
		}
		if x, ok := args[0].Ground(ctx); ok {
			if _, ok := x.(String); ok {
				yield(ctx)
			}
		}
	}
}

// BuiltinFree is an in-built predicate for checking whether a value is a free variable.
func BuiltinFree(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'free/1'")
		}
		if !args[0].IsGround(ctx) {
			yield(ctx)
		}
	}
}

// BuiltinGround is an in-built predicate for checking whether a value is ground.
func BuiltinGround(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'ground/1'")
		}
		if args[0].IsGround(ctx) {
			yield(ctx)
		}
	}
}

// BuiltinCall is an in-built predicate for calling dynamically built predicates.
func BuiltinCall(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'call/1'")
		}
		if t, ok := Bottom(ctx, args[0]).(*CompoundTerm); ok {
			for ctx := range ctx.Engine.Eval(ctx, t.Functor, t.Args) {
				if !yield(ctx) {
					return
				}
			}
		}
	}
}

// BuiltinNot is an in-built predicate for negation as failure.
func BuiltinNot(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 1 {
			panic("bad number of arguments in call of 'not/1'")
		}
		if t, ok := Bottom(ctx, args[0]).(*CompoundTerm); ok {
			for ctx := range ctx.Engine.Eval(ctx, t.Functor, t.Args) {
				ctx.Dummy() // placating the linter
				return
			}
			yield(ctx)
		}
	}
}

// BuiltinBagOf is an in-built predicate for collecting all the results of a goal.
func BuiltinBagOf(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if len(args) != 2 {
			panic("bad number of arguments in call of 'bagOf/1'")
		}
		if t, ok := Bottom(ctx, args[1]).(*CompoundTerm); ok {
			var bag []Value
			for ctx := range ctx.Engine.Eval(ctx, t.Functor, t.Args) {
				r, ok := t.Ground(ctx)
				if !ok {
					panic("non-ground value in 'bagOf' evaluation")
				}
				bag = append(bag, r)
			}
			for ctx := range args[0].Unify(ctx, listFromSlice(bag, Nil{})) {
				if !yield(ctx) {
					return
				}
			}
		}
	}
}
