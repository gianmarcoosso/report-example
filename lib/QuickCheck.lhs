\begin{code}
module Solve where
import Formulas
import Tableau
import Step
import Solve
import Test.QuickCheck
\end{code}

The project includes a method for generating random formulas, which are then used to test the prover. This is done as follows (these lines are essentially taken from lecture slides): \\

\begin{code}
atoms :: [Int]    
atoms = [1..9]
instance Arbitrary Frm where
  arbitrary = sized randomForm where
    randomForm :: Int -> Gen Frm
    randomForm 0 = P <$> elements atoms
    randomForm n = oneof [ P <$> elements atoms , N <$> randomForm (n `div` 2), C <$> randomForm (n `div` 2) <*> randomForm (n `div` 2), D <$> randomForm (n `div` 2) <*> randomForm (n `div` 2)  ]
\end{code}
 
(the dollar sign is not preceded by a backslash in the original code, here a backslash is added so that it is possible to show the code).\

Once this is settled, one can define the property corresponding to Glivenko's theorem, which states that for every propositional formula $\varphi$, 

\[\varphi \text{ is classically valid } \iff \neg \neg \varphi \text{ is intuitionistically valid } \]

This is done as \\

\begin{code}
glivenko :: Frm -> Bool                                      
glivenko f = classthm f == intuitthm (N (N f))
\end{code}

which then makes it possible to run the test the validity of Glivenko's theorem on 100 randomly generated propositional formulas.

In our attempts, the prover passed these tests, so for every formula $\varphi$ generated, it has given the same answer to the two questions \say{is $\varphi$ a theorem of classical logic?} and \say{is $\neg \neg \varphi$ a theorem of intuitionistic logic?}.
