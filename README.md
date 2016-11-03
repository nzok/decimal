# decimal

Some years ago I wrote a paper that argued that programming standards should be
machine-checked, using binary and decimal fixed point arithmetic (with scales
in types or in values) as a case study.  The specification is written as literate
Haskell, so that one level of "machine checking" is Haskell type checking, and
checked using QuickCheck, so another level is "testing with automatic test case
generation".  I am still trying to get this work published.  This is where I am
going to put the code.
