\section{Implementation}

The ideas presented above have been implemented in Haskell as is explained below. The original plan was to adapt the prover developed by Jan Van Eijck which can be found at \cite{slide}, but in reality we ended up writing almost everything from scratch. We only comment the interesting parts of our implementation and the full code can be found in the GitHub repository of the project under the name SourceCode.

\subsection{Basic types}

We represent indices and formulas as \\
\begin{code}
type Index = [Int]

data Frm =  P Int
         | N Frm
         | C Frm Frm
         | D Frm Frm
     deriving (Eq,Ord)

data Sign = T | F | Fc deriving Eq

newtype SFrm = S (Sign, Frm)
\end{code}

We represent a node in the following way. Each node is composed of six lists, the list of true atoms ($T p$), of false atoms ($F p$), of refuted atoms ($F_C p$), the list of pending formulas that don't lead to any deletion of $F$ formulas in the set $S$; the last two lists are a list of pending formulas with the shape $F(\neg \varphi)$ and a list that only contains pending formulas with the shape $F_C(\neg \varphi)$ and $F_C(\varphi \wedge \psi)$. A tableau is then just a list of nodes: in particular, they are stored as the list corresponding to their \say{leaf level}, as that encodes all the necessary information.\\

\begin{code}
data Node  = Nd Index [Frm] [Frm] [Frm] [SFrm] [SFrm] [Sfrm] 
type Tableau = [Node]
\end{code}

The reason for having three separate lists of pending formulas is that we want to distinguish them based on how tricky their associated rule is. In particular, we know that applying the rules to formulas of the form $F \neg$, $F_C \neg$ and $F_C \land$ leads to cancellation of all remaining $F$ formulas and need to be treated carefully in order to preserve completeness of the system.

\subsection{The step rule}
The step rule is what allows us to develop our tableau in that it tells us what to do based on what we have inside the lists of a specific node. However, it is very long and cumbersome, so we only explain the most important parts of it.

As we have seen, a node is composed of six lists, and the step rule is essentially divided into three parts accordingly: the first acts on the list of pending formulas that don’t lead to any deletion of $F$ formulas (i), the second one on the list of pending formulas with the shape $F(\neg \varphi)$ (ii) and finally the third one on the last list, i.e. the list that only contains pending formulas with the shape $F_C(\neg \varphi)$ and $F_C(\varphi \wedge \psi)$ (iii). The rule then behaves in the following way: it first tries to develop all formulas in (i). Then, when (i) is empty, it switches to (ii), and when (ii) is empty as well it switches to (iii). The reason for this is that we want to avoid trying all possible combinations of rule application (which might be necessary since we have rules that, when applied, delete all $F$ formulae), therefore we want to develop every unproblematic $F$ formula before we turn to formulas whose treatment might delete other $F$ formulas. 

The following is part of the code that is used to treat the list (i). Let's take the case in which $f$ is a true atom, as an example. What the rule does is: we add $f$ to the list of true atoms only if it is not part of $F$ atoms or $F_C$ atoms. Obviously, if this is not the case, we have a contradiction, and we get a tableau containing just the empty list. This will come in handy later.\\ 
\begin{code}
step :: Node  -> [Tableau]
step (Nd i positives negatives falses (f:fs) fnegpending fcpending)
step (Nd i positives negatives falses (f:fs) fnegpending fcpending)
  | tlit  f = [[Nd i (removesign f:positives) negatives falses fs fnegpending fcpending | not (elem (removesign f) negatives || elem (removesign f) falses)]]
\end{code}

Let's take a more complicated case. We make a case distinction: we can either have a true conjunction, a false disjunction or a provably false disjunction. In the last two cases there is a technicality, i.e. we have to make sure that we put the components in the right list. Take the last case, as an example. The subformulas can either lead to no deletion or -- because they are either of the shape $F_C(\varphi \wedge \psi)$ or of the shape $F_C(\neg \varphi)$ -- to a deletion. Hence we have to put them in the proper list accordingly.\\

\newpage

\begin{code}
step :: Node  -> [Tableau]
step (Nd i positives negatives falses (f:fs) fnegpending fcpending)
| rule1 f = if signof f == T then      [[Nd i positives negatives falses
                                        [maketrue y | y <-subf \$ removesign f]++fs fnegpending fcpending]]
            else if signof f == F then [[Nd i positives negatives falses
                                        [makenegative y | y <-subf \$ removesign f,
                                        not (deletewarning (makenegative y))]++fs
                                        [makenegative y | y <-subf \$ removesign f,
                                        deletewarning (makenegative y )]++fnegpending
                                        fcpending]]
            else                       [[Nd i positives negatives falses 
                                        [makefalse y | y <-subf \$ removesign f, 
                                        not (deletewarning (makefalse y)) ]++fs
                                        fnegpending [makefalse y | y <-subf \$
                                        removesign f, deletewarning  (makefalse y)]++fcpending]]
\end{code}

What the step rule does on (ii) is slightly different, because -- given that (ii) is a list of formulas $\varphi_1,\dots,\varphi_n$, where $\varphi_i$ has the shape $F(\neg \varphi)$ -- it outputs two tableaux: the first one is the result of applying the $F\neg$ rule to $\varphi_1$, while the second one is the list containing the original node in which $\varphi_1$ has been deleted from (ii), i.e. (ii) consists of $\varphi_2, \dots, \varphi_n$. Of course this behaviour is repeated similarly for this last list, so we again generate two tableaux, one for $\varphi_2$ and another one for $\varphi_3, \dots, \varphi_n$, and so on. The reason is that, whenever we develop one of these $\varphi_i$'s, we automatically lose all the others in the list, as well as all $F$ literals (after all, they are all $F$ formulae), hence -- for a list of $n$ formulas -- there are exactly $n$ cases to explore, which are the $n$ cases where one deletes $\varphi_i$ first. \\
\begin{code}
step (Nd i positives _ falses [] (f:fs) fcpending)
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))]
                  [] fcpending ] , [Nd i positives [] falses [] fs fcpending]]
\end{code}

Lastly, the step rule works on list (iii), i.e. a list that only contains either formulae of shape $F_C(\varphi \wedge \psi)$ or of shape $F_C(\neg \varphi)$. Because when we arrive at this stage we have no formulae in (ii) and we can only delete $F$ literals, and moreover the rules for $F_C(\varphi \wedge \psi)$ and $F_C(\neg \varphi)$ don't lead to any deletion of formulae inside (iii), in this case we don't need the machinery we saw in (ii), we can just tackle them sequentially as we have seen for (i). Besides, this is also the reason why we kept this kind of formulae as the last \say{kind} to be treated by the algorithm. 

So, this is the last part of the step rule:\\

\begin{code}
step (Nd i positives _ falses [] [] (f:fs))
  | falseneg f    = [[Nd i positives [] falses 
                     [maketrue (head (subf (removesign f)))] [] fs ]]
  | prfalseconj f = [[Nd (i++[0]) positives [] falses 
                     [makefalse (head (subf (removesign f))) | 
                     not (deletewarning (makefalse (head (subf (removesign f)))) )]
                     [] ([makefalse (head (subf (removesign f))) | 
                     deletewarning (makefalse (head (subf (removesign f)))) ]++ fs ),
                     Nd (i++[1]) positives [] falses 
                     [makefalse (last (subf (removesign f))) |
                     not (deletewarning (makefalse (last (subf (removesign f)))) )]
                     [] ([makefalse (last (subf (removesign f))) |
                     deletewarning (makefalse (last (subf (removesign f)))) ]++fs) ]]
\end{code}

\subsection{The solve function}

The solve function is the function that we use to determine theoremhood of a formula. Since the rules for the implication-free fragments of intuitionistic logic and classical logic coincide, it can be used for determining theoremhood of formulas in any of the two systems. Its first component is the function expand, which roughly corresponds to a \say{one step expansion} of a given tableau, and is given by \\

\begin{code}
    expand :: Tableau -> [Tableau]                         
    expand tab | not (badTab tab) = [concatMap (head . step) tab]  
               | otherwise        = [ head (step (firstbad tab)) ++ removebad tab,
                                    last (step (firstbad tab)) ++ removebad tab ]
\end{code}

where a tableau is considered \say{bad} if it has at least one \say{bad} node, i.e. a node which has empty (i) and nonempty (ii)\\
In the first case, if the tableau in question is not a bad one, then the output of expand is a list containing a single tableau, which is obtained by expanding every node on the leaf level by one step.\\
In the second case, so if the tableau has at least one bad node $n$, the expand function returns two tableaux, each of them differing from the original by an application of the step rule on $n$ according to the nondeterministic behaviour of step on bad nodes.\

One then needs the additional helper function \\

\begin{code}
pairify :: [Tableau] -> [(Tableau, Tableau)]                 
pairify = map \x-> (filter (not . expanded) x , filter expanded x)
\end{code}

which takes a list of tableaux and splits every tableau contained in it into its expanded and nonexpanded parts, yielding a list of pairs of tableaux. Note that, in accordance to the behaviour of our step function, expanded nodes are only stored if they correspond to open branches, therefore, as soon as a tableau has an expanded node, one can be certain that it will not develop into a closed tableau.\

The two functions above are then incorporated in the recursive behaviour of solve, which is given by \\

\begin{code}
solve :: [(Tableau, Tableau)] -> Bool                        
solve []          = False                               
solve (p:pairs) | null (snd p) && not (null (fst p)) 
                    = solve (pairify (expand(fst p))++ pairs)
                | null (snd p) && null (fst p) = True
                | otherwise = solve pairs || False
\end{code}

The idea behind it is the following: given a formula $\varphi$ one starts with a list containing just the pair (T, [ ]) where T corresponds to the initial tableau associated to $\varphi$ (which is different depending on whether one wants to check intuitionistic or classical validity of $\varphi$, and is given by functions which are present in the code) and applies the recursion in solve.\\
The first calculation step will look like
\[\text{solve[(T, [ ])]} \implies \text{solve (pairify (expand(T))}\]
now, if expand(T) has expanded nodes (i.e. fully expanded open branches), then solve will go into its third case and output solve [ ] || False, which yields False. Otherwise, it will continue to operate recursively, generating potentially more than one tableau. The reason why solve takes a list of pairs of tableaux as opposed to a list of tableaux is that one wants to check whether a tableau has fully expanded open branches at each step of the recursion, so that the procedure of expanding a tableau can short-circuit in case it is certain that the tableau will never close. Since the step rule is designed so that a branch is cancelled as soon as it closes, a closing tableau is one that eventually becomes the empty list, therefore our solve function yields True only when given a pair of empty tableaux.\

Note that, given the way the solve function is written, it will work \say{depth-first} in the following sense : if, during the \say{solving}, a list of pairs of tableaux has been generated, the solve function will work by expanding the tableau corresponding to the first pair as much as possible until it either yields a closing tableau (in which case the entire function stops and yields True) or it yields a non-closing tableau, in which case the solve function will turn to expanding the other tableaux in the list.


\subsection{QuickCheck}

The project includes a method for generating random formulas, which are then used to test the prover. This is done as follows (these lines are essentially taken from lecture slides): \\

\begin{code}
atoms :: [Int]    
atoms = [1..9]
instance Arbitrary Frm where
  arbitrary = sized randomForm where
    randomForm :: Int -> Gen Frm
    randomForm 0 = P <\$> elements atoms
    randomForm n = oneof [ P <\$> elements atoms , N <\$> randomForm (n `div` 2), C <\$> randomForm (n `div` 2) <*> randomForm (n `div` 2), D <\$> randomForm (n `div` 2) <*> randomForm (n `div` 2)  ]


\end{code}
 
(the dollar sign is not preceded by a backslash in the original code, here a backslash is added so that it is possible to show the code).\

Once this is settled, one can define the property corresponding to Glivenko's theorem, which states that for every propositional formula $\varphi$, 

\[\varphi \text{ is classically valid } \iff \neg \neg \varphi \text{ is intuitionistically valid } \]

This is done as \\

\begin{code}
glivenko :: Frm -> Bool                                      
glivenko f = classthm f == intuitthm (N (N f))
\end{code}

which then makes it possible to run the test \\

\begin{code}
 >quickCheck (\f -> glivenko f)
\end{code}

In our attempts, the prover passed these tests, so for every formula $\varphi$ generated, it has given the same answer to the two questions \say{is $\varphi$ a theorem of classical logic?} and \say{is $\neg \neg \varphi$ a theorem of intuitionistic logic?}.

