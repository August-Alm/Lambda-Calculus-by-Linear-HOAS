# Lambda-Calculus-by-Linear-HOAS
An interpreter of lambda calculus in ATS2 that uses a HOAS encoding in linear types.

A small and efficient program to compute (normalize) terms in the untyped λ-calculus.
The interpreter uses a higher order abstract syntax (HOAS) encoding with linear
ATS-types, a little bit of hand-rolled, primitive reference counting and requires no
garbage collection.

Closely based on the Javascript algorithm here:
https://github.com/MaiaVictor/lambda-calculus/issues/1


At the moment it typechecks but does not compile. I don't think I'm doing the compilation
correctly...

And yes, the code deserves to be split into multiple bite-sized files and equipped with a
proper Makefile.
