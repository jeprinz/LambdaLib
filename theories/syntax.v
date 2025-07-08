(*
I'm working here on the underlying proofs for the lambda calculus.
One idea is to formalize syntax with binding with my particular variable representaiton,
which is what this file is for.

Another idea (that I'm going to try first) is to build lambda-FP with autosubst, and map
my variable representation into that.
The idea is to build up an environment which remembers what the bound variables map to,
and then map free variables to constants in lambda-FP.
*)
