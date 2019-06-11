This guide contains instrucitons on how to use the DSL

You compile it by typing "fsharpc functions.fsx"
This creates an executable that you run with "mono functions.exe"

The program now reads from input and below are some examples showing the different semantics

IsValid returns true only if the regex given contains probabilities strictly between 0 and 1 and and no Kleene-star expression is nested within another.

IsValid "a|(0.5)b"
IsValid "\Eps*(0.5)"
IsValid "(a*(0.5))*(0.5)"

The call, Generate regex n, returns n strings matching regex, distributed with respect to the probability 

Generate "a|(0.5)b" 2
Generate "a*(0.5)" 50

The call, Prop regex s, returns the probability of generating s with regex on the first try

Prob "a|(0.5)b" "a"
Prob "(a|(0.2)b|(0.3)c|(0.4)d|(0.5)r)*(0.2)" "abracadabra"

If you wish to see the parse-tree, NFA and DFA that's constructed from the regular expression, write "verbose=true" (not including quotation marks)
If you wish to turn verbose output off again, write "verbose=false"
Verbose output is false by default.
