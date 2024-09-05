//go:build dbtest
// +build dbtest

package inference

import (
	"context"
	"database/sql"
	"fmt"
	"os"
	"testing"

	"github.com/google/uuid"
	"github.com/stretchr/testify/require"

	// import PG
	_ "github.com/lib/pq"
)

func TestGenericFetch(t *testing.T) {
	req := require.New(t)

	db, err := sql.Open("postgres", os.Getenv("DB_DSN"))
	req.NoError(err)
	defer db.Close()

	_, err = db.Exec(`DROP TABLE IF EXISTS dummy_relation`)
	req.NoError(err)
	_, err = db.Exec(`CREATE TABLE dummy_relation (name TEXT, age INTEGER, height REAL)`)
	req.NoError(err)
	_, err = db.Exec(`INSERT INTO dummy_relation (name, age, height) VALUES ('name1', 18, 1.6)`)
	req.NoError(err)
	_, err = db.Exec(`INSERT INTO dummy_relation (name, age, height) VALUES ('name2', 19, 1.7)`)
	req.NoError(err)
	_, err = db.Exec(`INSERT INTO dummy_relation (name, age, height) VALUES ('name3', 20, 1.8)`)
	req.NoError(err)

	e, err := NewEngineFromSymbolicExpression(`()`)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{
		Functor: "fetch",
		Arity:   3,
	}, genericFetch)

	ctx := &EvalContext{
		Engine:  e,
		DB:      db,
		Context: context.Background(),
	}

	x := new(Var)
	cols := listFromSlice([]Value{String("name::string"), String("age::int"), String("height::float")}, Nil{})
	var r []string
	for ctx := range e.Eval(ctx, "fetch", []Value{String("dummy_relation"), cols, x}) {
		x, ok := x.Ground(ctx)
		req.True(ok)
		r = append(r, x.String())
	}
	req.Equal(3, len(r))
	req.Equal([]string{
		`["name1"|[18|[1.600000|[]]]]`,
		`["name2"|[19|[1.700000|[]]]]`,
		`["name3"|[20|[1.800000|[]]]]`,
	}, r)
}

func TestSubgroups(t *testing.T) {
	req := require.New(t)

	db, err := sql.Open("postgres", os.Getenv("DB_DSN"))
	req.NoError(err)
	defer db.Close()

	_, err = db.Exec(`DELETE FROM subgroups`)
	req.NoError(err)
	_, err = db.Exec(`DELETE FROM groups`)
	req.NoError(err)

	var ids []uuid.UUID
	for i := 0; i < 10; i++ {
		ids = append(ids, uuid.New())
	}
	for i, id := range ids {
		_, err = db.Exec(`INSERT INTO groups (id, name) VALUES ($1, $2)`, id, fmt.Sprintf("group%d", i+1))
		req.NoError(err)
	}
	for i := 0; i < len(ids)-1; i++ {
		id1, id2 := ids[i], ids[i+1]
		_, err = db.Exec(`INSERT INTO subgroups (subgroup, supergroup) VALUES ($1, $2)`, id1, id2)
		req.NoError(err)
	}

	e, err := NewEngineFromSymbolicExpression(`()`)
	req.NoError(err)
	req.NotNil(e)

	e.AddRule(Signature{
		Functor: "closure",
		Arity:   2,
	}, transitiveClosureOnGroups)

	ctx := &EvalContext{
		Engine:  e,
		DB:      db,
		Context: context.Background(),
	}

	subgroup, supergroup := String(ids[0].String()), new(Var)
	var r []string
	for ctx := range e.Eval(ctx, "closure", []Value{subgroup, supergroup}) {
		req.True(subgroup.IsGround(ctx))
		req.True(supergroup.IsGround(ctx))
		id, _ := supergroup.Ground(ctx)
		r = append(r, string(id.(String)))
	}
	req.Equal(9, len(r))
	req.Equal(fmap(func(id uuid.UUID) string { return id.String() }, ids[1:]), r)
}

// func TestUserRule(t *testing.T) {
// 	type user struct {
// 		id        uuid.UUID
// 		firstName string
// 		lastName  string
// 		email     string
// 		password  string
// 		login     string
// 	}
// 	users := []user{
// 		user{
// 			id:        uuid.MustParse("d28fe830-9f6a-4307-bb98-b4393bd083ba"),
// 			firstName: "John",
// 			lastName:  "Doe",
// 			login:     "example@example.com",
// 		},
// 		user{
// 			id:        uuid.MustParse("c9147580-d18e-4472-ae05-0f8f5e5eac7b"),
// 			firstName: "Ada",
// 			lastName:  "Lovelace",
// 			login:     "a.l@example.com",
// 		},
// 	}
// 	req := require.New(t)

// 	// mock data
// 	db, err := sql.Open("postgres", os.Getenv("DB_DSN"))
// 	req.NoError(err)
// 	defer db.Close()
// 	_, err = db.Exec(`DELETE FROM "users"`)
// 	req.NoError(err)

// 	// apply migrations
// 	for _, m := range infrastructure.Migrations {
// 		db.Exec(m.Script)
// 	}
// 	// seed
// 	for _, u := range users {
// 		_, err = db.Exec(`INSERT INTO users (
// 			id,
// 			first_name,
// 			last_name,
// 			login,
// 			email,
// 			password,
// 			created_at,
// 			changed_at,
// 			is_active,
// 			last_signup
// 			)
// 			VALUES(
// 				$1,
// 				$2,
// 				$3,
// 				$4,
// 				$5,
// 				$6,
// 				$7,
// 				$8,
// 				$9,
// 				NULL
// 			)`, u.id, u.firstName, u.lastName, u.login, u.email, u.password, time.Now(), time.Now(), true)
// 		req.NoError(err)
// 	}

// 	e, err := NewEngineFromSymbolicExpression(`()`)

// 	e.AddRule(Signature{
// 		Functor: "user",
// 		Arity:   4,
// 	}, fetchUsers)

// 	req.NoError(err)
// 	req.NotNil(e)

// 	ctx := &EvalContext{
// 		Engine:  e,
// 		DB:      db,
// 		Context: context.Background(),
// 	}

// 	id, firstName, lastName, login := new(Var), new(Var), new(Var), new(Var)

// 	t.Run("Test all free", func(t *testing.T) {
// 		resCnt := 0
// 		for ctx := range e.Eval(ctx, "user", []Value{id, firstName, lastName, login}) {
// 			resCnt++
// 			req.True(id.IsGround(ctx))
// 			req.True(firstName.IsGround(ctx))
// 			req.True(lastName.IsGround(ctx))
// 			req.True(login.IsGround(ctx))
// 		}
// 		req.Equal(2, resCnt)
// 	})

// 	t.Run("Test all assigned", func(t *testing.T) {
// 		resCnt := 0
// 		u := users[0]
// 		for ctx := range e.Eval(ctx, "user", []Value{String(u.id.String()), String(u.firstName), String(u.lastName), String(u.login)}) {
// 			resCnt++
// 			req.False(id.IsGround(ctx))
// 			req.False(firstName.IsGround(ctx))
// 			req.False(lastName.IsGround(ctx))
// 			req.False(login.IsGround(ctx))

// 		}
// 		req.Equal(1, resCnt)
// 	})

// 	t.Run("Test mix", func(t *testing.T) {
// 		resCnt := 0
// 		u := users[0]
// 		for ctx := range e.Eval(ctx, "user", []Value{String(u.id.String()), firstName, String(u.lastName), login}) {
// 			resCnt++
// 			req.False(id.IsGround(ctx))
// 			req.True(firstName.IsGround(ctx))
// 			req.False(lastName.IsGround(ctx))
// 			req.True(login.IsGround(ctx))

// 		}
// 		req.Equal(1, resCnt)
// 	})

// }
