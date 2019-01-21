# Propositional-Logic-Parser
A parser that checks human readable equations, builds a structure form them, can query them for true/false values and can print them out
in human readable form.

The challenge for me was implementing it in a functional style in ML.

It takes in input such as `inputString  "!a&b|c<->!d";`
Turns this into its abstract syntax tree:
`> val it =
   [Prop (Iff (Or (And (Not (Lit "a"), Lit "b"), Lit "c"), Not (Lit "d")))]:
   builder list`
   
And then can for example, convert it back to a string, convert it to NNF etc:

`> outputProposition it;`

`proposition: (!a & b) | c <-> !d`

`val it = (): ?.unit`

In NNF:

`> convertToNNF (inputString  "!a&b|c<->!d");`
`val it =`
 `  And`
   ` (Or (Not (Or (And (Not ..., Lit "b"), Lit "c")), Not (Lit "d")),`
    ` Or (Not (Not (Lit "d")), Or (And (Not (Lit "a"), Lit "b"), Lit "c"))):`
   `prop`
`> printout it;`
``
`proposition: (!((!a & b) | c) | !d) & (!d | (!a & b) | c)`
``
`val it = (): ?.unit`


If you were to implement an incorrect function, that has say unbalanced/incorrectly placed brackets or an incorrect symbol,
you would get and exception:

`> inputString "(a&)(b";`
`Exception- malformedInput raised `
