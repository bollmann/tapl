% Types and Programming Languages -- Independence Study Report
% Dominik Bollmann
% April 27th, 2016

During the last four months, I've deeply dived into studying
Prof. Pierce's book "Types and Programming Languages" (TAPL). As part
of my independent study, I accomplished reading the entire book except
chapters 28, 31, and the case study chapters (18, 19, 27, 32). While
reading the book, I solved all the recommended as well as the "quick
check" exercises (and in many occasions I also solved some of a
chapter's additionally given problem sets). To complement my
theoretical studies of the TAPL content, I furthermore implemented
most of the calculi under discussion in Haskell. In particular, I
implemented the pure untyped lambda calculus, the simply typed lambda
calculus (including full type inference!), the lambda calculus with
subtyping, as well as the polymorphic lambda calculus (System F). For
an additional challenge, I formalized all these calculi in Haskell
without prior reading of TAPL's corresponding implementation
chapters. Moreover, I encoded parts of the calculi using deviating
techniques. Most notably, I implemented substitution by means of a
monadic computation in Haskell's \texttt{State} monad in addition to
using de Brujin indices.

Finally, for testing the implemented calculi, I wrote extensive test
suites consisting of both traditional unit tests as well as quickcheck
properties. I am particular proud of my quickcheck property
formalizations, which either equate different implementations of the
same concept or which encode some property for the calculi under
discussion. For example, to test the monadic substitution, I
quickchecked it to be equivalent with substitution based on de Brujin
indices. In the same vain, I tested type inference for the simply
typed lambda calculus to behave the same for two related, but
different implementations. Similarly, I tested several sample programs
written in the calculi under discussion to deliver the expected
results wrt. to a corresponding Haskell implementation. Finally, for
the type inference algorithms, I formalized the type reconstruction
algorithm's soundness and completeness properties and quickchecked
them to hold on a large number of randomly generated test cases.

Studying the TAPL book has been quite a bit of work but at the same
time a lot of fun! I especially enjoyed the good mix of theory and
practice throughout the book.

On the theory front, I think I've particularly learned how to
formalize programming language theory and how to reason about it. Most
notably, I have internalized the inductive reasoning techniques used
throughout the book. While Penn's CIS 500 Software Foundations course
already was a great introduction to inductive reasoning, I really
liked to prove the same or related concepts manually with just pen and
paper this time. I think the manual approach without any machine
support has made me yet better at defining inductive relations and
then inductively proving properties about them. To this end, I
particularly appreciated the sample solutions provided at the end of
the book, which enabled me to easily compare my solutions to the
book's problems with the reference solutions.

On the practical side, I've gotten a good grip on how to turn the
theoretic discussion of a programming language theory into an
executable interpreter and typechecker for that programming
language. Implementing TAPL's concepts in Haskell has furthermore
fostered my functional programming skills and has served me as a good
practical sequel to Penn's CIS 552 Advanced Programming course. I've
particullary gotten exposed to defining embedded domain specific
languages (i.e., the different calculi) inside of the Haskell host
language. Furthermore, I've very much liked to improve my
understanding of property-based testing by using Haskell's
\texttt{quickcheck} library.

Concluding, the study of Types and Programming Languages was a very
rewarding and worthwile effort. It has fostered my understanding of
the foundations of functional programming and the underlying type
theory significantly. As such, I've very much enjoyed this independent
study!
