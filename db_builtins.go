package inference

import (
	"database/sql"
	"errors"
	"fmt"
	"strconv"
	"strings"
	"unsafe"

	"github.com/google/uuid"
	"github.com/mailstepcz/slice"
)

// GenericFetch provides a built-in predicate performing database queries.
func GenericFetch(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if ctx.DB == nil {
			panic("no associated database")
		}
		if len(args) != 3 {
			panic("bad number of arguments in call of 'genericFetch'")
		}

		table, ok := Bottom(ctx, args[0]).(String)
		if !ok {
			panic("no ground table name")
		}

		colsTerm, ok := args[1].Ground(ctx)
		if !ok {
			panic("no ground column list")
		}
		typedColumns, err := listFromTerm(colsTerm)
		if err != nil {
			panic(err)
		}
		columnNames, columnTypes := make([]string, len(typedColumns)), make([]string, len(typedColumns))
		for i, c := range typedColumns {
			n, t := columDataFromTerm(ctx, c)
			columnNames[i] = n
			columnTypes[i] = t
		}

		var (
			whereTail string
			queryArgs []interface{}
		)
		if values, ok := Bottom(ctx, args[2]).(*CompoundTerm); ok {
			values, err := listFromTerm(values)
			if err != nil {
				panic(err)
			}
			if len(values) != len(typedColumns) {
				panic("incompatible number of columns and values")
			}
			for i, name := range columnNames {
				if arg, ok := values[i].Ground(ctx); ok {
					if whereTail == "" {
						whereTail += " WHERE "
					} else {
						whereTail += " AND "
					}
					queryArgs = append(queryArgs, arg)
					whereTail += fmt.Sprintf("%q = $%d", name, len(queryArgs))
				}
			}
		}

		rows, err := ctx.DB.QueryContext(ctx.Context, `SELECT `+
			strings.Join(slice.Fmap(func(name string) string {
				return strconv.Quote(name)
			}, columnNames), ", ")+
			` FROM `+strconv.Quote(string(table))+whereTail, queryArgs...)
		if err != nil {
			panic(err)
		}
		defer rows.Close()

		r := make([]interface{}, len(typedColumns))

		for i, typ := range columnTypes {
			switch typ {
			case "string":
				r[i] = new(sql.Null[string])
			case "int":
				r[i] = new(sql.Null[int])
			case "float":
				r[i] = new(sql.Null[float64])
			default:
				panic("unknown column type: " + typ)
			}
		}

		for rows.Next() {
			if err := rows.Scan(r...); err != nil {
				panic(err)
			}
			mappedValues := slice.Fmap(func(x any) Value {
				switch x := x.(type) {
				case *sql.Null[string]:
					if !x.Valid {
						return Nil{}
					}
					return String(x.V)
				case *sql.Null[int]:
					if !x.Valid {
						return Nil{}
					}
					return Integer(x.V)
				case *sql.Null[float64]:
					if !x.Valid {
						return Nil{}
					}
					return Float(x.V)
				}

				panic("unknown value type")
			}, r)
			for ctx := range args[2].Unify(ctx, listFromSlice(mappedValues, Nil{})) {
				if !yield(ctx) {
					return
				}
			}
		}

		if err := rows.Err(); err != nil {
			panic(err)
		}
	}
}

// FetchUsers provides a built-in predicate performing user fetches.
func FetchUsers(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if ctx.DB == nil {
			panic("no associated database")
		}
		if len(args) != 4 {
			panic("bad number of arguments in call of 'fetchUsers'")
		}

		var (
			whereTail string
			queryArgs []interface{}
		)
		for i, col := range []string{"id", "first_name", "last_name", "login"} {
			if arg, ok := args[i].Ground(ctx); ok {
				if whereTail == "" {
					whereTail += " WHERE "
				} else {
					whereTail += " AND "
				}
				queryArgs = append(queryArgs, arg)
				whereTail += fmt.Sprintf("%q = $%d", col, len(queryArgs))
			}
		}
		rows, err := ctx.DB.QueryContext(ctx.Context, `SELECT id, first_name, last_name, login FROM users`+whereTail, queryArgs...)
		if err != nil {
			panic(err)
		}
		defer rows.Close()

		for rows.Next() {
			var (
				id                         uuid.UUID
				firstName, lastName, login string
			)
			if err := rows.Scan(&id, &firstName, &lastName, &login); err != nil {
				panic(err)
			}
			for ctx := range args[0].Unify(ctx, String(id.String())) {
				for ctx := range args[1].Unify(ctx, String(firstName)) {
					for ctx := range args[2].Unify(ctx, String(lastName)) {
						for ctx := range args[3].Unify(ctx, String(login)) {
							if !yield(ctx) {
								return
							}
						}
					}
				}
			}
		}

		if err := rows.Err(); err != nil {
			panic(err)
		}
	}
}

// TransitiveClosureOnGroups provides a built-in predicate performing recursive queries on subgroups.
func TransitiveClosureOnGroups(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if ctx.DB == nil {
			panic("no associated database")
		}
		if len(args) != 2 {
			panic("bad number of arguments in call of 'transitiveClosureOnGroups'")
		}

		var (
			whereTail string
			queryArgs []interface{}
		)
		for i, col := range []string{"subgroup", "supergroup"} {
			if arg, ok := args[i].Ground(ctx); ok {
				if whereTail == "" {
					whereTail += " WHERE "
				} else {
					whereTail += " AND "
				}
				queryArgs = append(queryArgs, arg)
				whereTail += fmt.Sprintf("%q = $%d", col, len(queryArgs))
			}
		}
		rows, err := ctx.DB.QueryContext(ctx.Context, `WITH RECURSIVE closure (subgroup, supergroup) AS (
			SELECT subgroup, supergroup FROM subgroups
			UNION ALL
			SELECT s.subgroup, c.supergroup FROM subgroups s INNER JOIN closure c ON s.supergroup = c.subgroup)
			SELECT subgroup, supergroup FROM closure`+whereTail, queryArgs...)
		if err != nil {
			panic(err)
		}
		defer rows.Close()

		for rows.Next() {
			var (
				subgroup, supergroup uuid.UUID
			)
			if err := rows.Scan(&subgroup, &supergroup); err != nil {
				panic(err)
			}
			for ctx := range args[0].Unify(ctx, String(subgroup.String())) {
				for ctx := range args[1].Unify(ctx, String(supergroup.String())) {
					if !yield(ctx) {
						return
					}
				}
			}
		}

		if err := rows.Err(); err != nil {
			panic(err)
		}
	}
}

// BeginTransaction provides a built-in predicate beginning a transaction.
func BeginTransaction(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if ctx.DB == nil {
			panic("no associated database")
		}
		if len(args) != 1 {
			panic("bad number of arguments in call of 'beginTransaction'")
		}

		tx, err := ctx.DB.BeginTx(ctx.Context, &sql.TxOptions{Isolation: sql.LevelSerializable})
		if err != nil {
			panic(err)
		}
		for ctx := range args[0].Unify(ctx, Pointer{ptr: unsafe.Pointer(tx)}) {
			yield(ctx)
		}
		if err := tx.Rollback(); err != nil && !errors.Is(err, sql.ErrTxDone) {
			panic(err)
		}
	}
}

// BeginReadOnlyTransaction provides a built-in predicate beginning a read-only transaction.
func BeginReadOnlyTransaction(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if ctx.DB == nil {
			panic("no associated database")
		}
		if len(args) != 1 {
			panic("bad number of arguments in call of 'beginTransaction'")
		}

		tx, err := ctx.DB.BeginTx(ctx.Context, &sql.TxOptions{ReadOnly: true, Isolation: sql.LevelRepeatableRead})
		if err != nil {
			panic(err)
		}
		for ctx := range args[0].Unify(ctx, Pointer{ptr: unsafe.Pointer(tx)}) {
			yield(ctx)
		}
		if err := tx.Rollback(); err != nil && !errors.Is(err, sql.ErrTxDone) {
			panic(err)
		}
	}
}

// CommitTransaction provides a built-in predicate committing a transaction.
func CommitTransaction(ctx *EvalContext, args []Value) func(func(*EvalContext) bool) {
	return func(yield func(*EvalContext) bool) {
		if ctx.DB == nil {
			panic("no associated database")
		}
		if len(args) != 1 {
			panic("bad number of arguments in call of 'commitTransaction'")
		}

		p, ok := Bottom(ctx, args[0]).(Pointer)
		if !ok {
			panic("non-ground transaction when committing")
		}
		if err := (*sql.Tx)(p.ptr).Commit(); err != nil {
			panic(err)
		}
		yield(ctx)
	}
}
