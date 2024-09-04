package inference

import (
	"testing"

	"github.com/stretchr/testify/require"
)

func TestTypeParser(t *testing.T) {
	req := require.New(t)

	r, err := parseCode(`% pred ~ string .`)
	req.NoError(err)
	stmts, ok := r.([]AST)
	req.True(ok)
	req.Equal(1, len(stmts))
	req.Equal(`pred ~ string`, stmts[0].String())

	r, err = parseCode(`% pred: ~ string * integer .`)
	req.NoError(err)
	stmts, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(stmts))
	req.Equal(`pred: ~ string * integer`, stmts[0].String())

	r, err = parseCode(`% pred:sel: ~ string * integer * float .`)
	req.NoError(err)
	stmts, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(stmts))
	req.Equal(`pred:sel: ~ string * integer * float`, stmts[0].String())
}

func TestTypeCheck(t *testing.T) {
	req := require.New(t)

	e, err := NewEngine(`
		% personAged: ~ string * integer.
		"Máire" personAged: 25.
		"Saoirse" personAged: 30.
	`, true)
	req.NoError(err)
	req.NotNil(e)
}

func TestParser(t *testing.T) {
	req := require.New(t)

	r, err := parseCode(`fail.`)
	req.NoError(err)
	rules, ok := r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`fail.`, rules[0].String())

	r, err = parseCode(`"abcd" sel.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel("abcd").`, rules[0].String())

	r, err = parseCode(`[] sel.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel([]).`, rules[0].String())

	r, err = parseCode(`[a] sel.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel([a|[]]).`, rules[0].String())

	r, err = parseCode(`([a, b]) sel.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel([a|[b|[]]]).`, rules[0].String())

	r, err = parseCode(`[a, b | L] sel.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel([a|[b|L]]).`, rules[0].String())

	r, err = parseCode(`"abcd" sel: "efgh".`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel:("abcd", "efgh").`, rules[0].String())

	r, err = parseCode(`"abcd" sel1: "efgh" sel2: "ijkl".`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`sel1:sel2:("abcd", "efgh", "ijkl").`, rules[0].String())

	r, err = parseCode(`X pred1.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`pred1(X).`, rules[0].String())

	r, err = parseCode(`(X pred1) pred2: (Y pred3: Z).`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`pred2:(pred1(X), pred3:(Y, Z)).`, rules[0].String())

	r, err = parseCode(`X pred1 :- X pred2.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`pred1(X) :- pred2(X).`, rules[0].String())

	r, err = parseCode(`X pred1 :- X pred2, Y pred3.`)
	req.NoError(err)
	rules, ok = r.([]AST)
	req.True(ok)
	req.Equal(1, len(rules))
	req.Equal(`pred1(X) :- pred2(X), pred3(Y).`, rules[0].String())
}
