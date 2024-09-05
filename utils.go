package inference

import (
	"fmt"
	"strings"
)

func unifyListsFrom(ctx *EvalContext, l1, l2 []Value, i int) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if i == len(l1) {
			yield(ctx)
		} else {
			for ctx := range l1[i].Unify(ctx, l2[i]) {
				for ctx := range unifyListsFrom(ctx, l1, l2, i+1) {
					yield(ctx)
				}
			}
		}
	}
}

func termFromList(l []ASTExpr, tail ASTExpr) ASTExpr {
	if len(l) == 0 {
		return tail
	}
	return &ASTTerm{Functor: ".", Args: []ASTExpr{l[0], termFromList(l[1:], tail)}}
}

// AVMFromMap ...
func AVMFromMap(m map[string]Value) (Value, *Var) {
	pairs := make([]Value, 0, len(m))
	for k, v := range m {
		pairs = append(pairs, &CompoundTerm{Functor: "keyValue:", Args: []Value{Atom(k), v}})
	}
	var tail Var
	return listFromSlice(pairs, &tail), &tail
}

// MapFromAVM ...
func MapFromAVM(avm Value) (map[string]Value, error) {
	pairs, err := listFromTerm(avm)
	if err != nil {
		return nil, err
	}
	m := make(map[string]Value, len(pairs))
	for _, p := range pairs {
		if t, ok := p.(*CompoundTerm); ok && t.Functor == "keyValue:" && len(t.Args) == 2 {
			if k, ok := t.Args[0].(Atom); ok {
				m[string(k)] = t.Args[1]
			} else {
				return nil, fmt.Errorf("invalid AVM pair key '%s'", t.Args[0])
			}
		} else {
			return nil, fmt.Errorf("invalid AVM pair '%s'", p)
		}
	}
	return m, nil
}

func listFromSlice(vals []Value, tail Value) Value {
	if len(vals) == 0 {
		return tail
	}
	return &CompoundTerm{Functor: ".", Args: []Value{vals[0], listFromSlice(vals[1:], tail)}}
}

func listFromTerm(v Value) ([]Value, error) {
	var list []Value
	for {
		switch x := v.(type) {
		case *CompoundTerm:
			if x.Functor == "." && len(x.Args) == 2 {
				list = append(list, x.Args[0])
				v = x.Args[1]
			} else {
				return nil, fmt.Errorf("invalid list value (bad functor or arity): %s", x)
			}
		case Nil:
			return list, nil
		default:
			return nil, fmt.Errorf("invalid list value (bad type): %s", v)
		}
	}
}
func columDataFromTerm(ctx *EvalContext, v Value) (string, string) {
	s, ok := Bottom(ctx, v).(String)
	if !ok {
		panic(fmt.Sprintf("invalid column definition (not string): %v", s))
	}
	col, typ, ok := strings.Cut(string(s), "::")
	if !ok {
		panic(fmt.Sprintf("invalid column definition (bad structure): %v", s))
	}

	return col, typ
}
