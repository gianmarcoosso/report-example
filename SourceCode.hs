{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

import Data.List
import Test.QuickCheck


type Index = [Int]

data Frm =  P Int
         | N Frm
         | C Frm Frm
         | D Frm Frm
     deriving (Eq,Ord)

instance Show Frm where
  show (P x)      = show x
  show (N form)   = '-': show form
  show (C f1 f2)  = "(" ++ show f1 ++ "*" ++ show f2 ++ ")"
  show (D f1 f2)     = "(" ++ show f1 ++ "+" ++ show f2 ++ ")"


atoms :: [Int]    --defines an instance of arbitrary for formulas. this is needed to use quickcheck 
atoms = [1..9]
instance Arbitrary Frm where
  arbitrary = sized randomForm where
    randomForm :: Int -> Gen Frm
    randomForm 0 = P <$> elements atoms
    randomForm n = oneof [ P <$> elements atoms , N <$> randomForm (n `div` 2), C <$> randomForm (n `div` 2) <*> randomForm (n `div` 2), D <$> randomForm (n `div` 2) <*> randomForm (n `div` 2)  ]


data Sign = T | F | Fc deriving Eq

newtype SFrm = S (Sign, Frm)

instance Eq SFrm where
  S (x,y) == S (z,v) = (x,y)==(z,v)

instance Show SFrm where
  show (S (T, f))  = "T" ++ show f
  show (S (F, f))  = "F" ++ show f
  show (S (Fc, f)) = "Fc" ++ show f


subf :: Frm -> [Frm] -- for every composite formula, it gives the list of arguments of its main connective. useless for atoms
subf (P x) = [P x]
subf (N f) = [f]
subf (C f g) = [f,g]
subf (D f g) = [f,g]


data Node  = Nd Index [Frm] [Frm] [Frm] [SFrm] [SFrm] [SFrm] deriving Show --a node is stored as an index (a binary sequence saying where in the binary tree it is)
                                                                           --followed by 6 lists of formulas/signed formulas. the first three lists are meant to contain,
                                                                           --respectively, all true, false and provably false literals generated so far.
                                                                           --the remaining three lists contain pending formulas, organized based on theirs structure:
                                                                           --the first contains unproblematic formulas which don't lead to any cancellation,
                                                                           --the second contains problematic false negations, which lead to cancellation of other false formulas
                                                                           --the third contains problematic provably false formulas, which also lead to cancellation
instance Eq Node where
  Nd i p n f tp fp fcp == Nd j d s a ta fa fca = i==j && p==d && n==s && f==a && tp==ta && fp==fa && fcp ==fca


type Tableau = [Node]

--Specification of types of rules

rule1 :: SFrm -> Bool                  --rules of type 1 are those which don't lead to splitting and such that the formula is decomposed into its 
rule1 (S (T, C _ _))  = True         --subformulas, which keep the same sign
rule1 (S (F, D _ _))  = True
rule1 (S (Fc, D _ _)) = True
rule1 _                 = False

rule2 :: SFrm -> Bool                  --rules of type 2 are those which lead to splitting and such that each of the resulting branches keeps one 
rule2 (S (T, D _ _))  = True         --of the two subformulas, with the same sign
rule2 (S (F, C _ _))  = True
rule2 _                 = False

falseneg :: SFrm -> Bool               --rules for false negation, they lead to no splitting, cancellation of previous false formulas and they 
falseneg (S (F, N _))  = True        --turn the sign of the formula into a T
falseneg (S (Fc, N _)) = True
falseneg _               = False

prfalseconj :: SFrm -> Bool            --rule for provably false conjunction, leads to splitting and cancellation of previous false formulas
prfalseconj (S (Fc, C _ _)) = True   -- the subformulas keep their sign
prfalseconj _                 = False

trueneg :: SFrm -> Bool                --rule for true negation
trueneg (S (T, N _)) = True
trueneg _              = False


deletewarning :: SFrm -> Bool          -- function which tells you which rules lead to deletion of previous formulas and are dangerous 
deletewarning (S (x, y)) = prfalseconj (S (x, y)) || falseneg (S (x, y))


-- these are functions which determine whether a formula is a true/false/provably false literal
tlit, flit, fclit :: SFrm -> Bool
tlit (S (T, P _))    = True
tlit _                 = False
flit (S (F, P _))   = True
flit _                 = False
fclit (S (Fc, P _)) = True
fclit _                = False

-- functions which add signs to formulas
makesign :: Sign -> Frm -> SFrm
makesign x y = S (x,y)
makenegative :: Frm -> SFrm
makenegative f = S (F,f)
maketrue :: Frm -> SFrm
maketrue f = S (T,f)
makefalse :: Frm -> SFrm
makefalse f= S (Fc, f)
--function which strips the sign off a signed formula
removesign :: SFrm -> Frm
removesign (S (_, f)) = f
--function which detects the sign of a formula
signof:: SFrm -> Sign
signof (S (T, _ )) = T
signof (S (F, _ )) = F
signof (S (Fc, _)) = Fc

--the function "step" which takes a node of a tableau and outputs a list of tableaux (one or two depending on the rule)
--we iterate the step to expand a given tableau fully. this may lead to more than one tableaux, if there are rules which involve 
--deletion of formulas as, in order to achieve completeness, one has to explore all "options of precedence"

step :: Node  -> [Tableau]
step (Nd i positives negatives falses [] [] []) = [[Nd i positives negatives falses [] [] []]]
step (Nd i positives negatives falses (f:fs) fnegpending fcpending)
  | tlit  f = [[Nd i (removesign f:positives) negatives falses fs fnegpending fcpending | not (elem (removesign f) negatives || elem (removesign f) falses)]]
  | flit  f = [[Nd i positives (removesign f :negatives) falses fs fnegpending fcpending | removesign f `notElem` positives]]
  | fclit  f = [[Nd i positives negatives (removesign f :falses) fs fnegpending fcpending |  removesign f `notElem` positives]]
  | rule1 f = if signof f == T then [[Nd i positives negatives falses ([maketrue y | y <-subf $ removesign f]++fs) fnegpending fcpending]]
              else if signof f == F then [[Nd i positives negatives falses ([makenegative y | y <-subf $ removesign f, not (deletewarning ( makenegative y))]++fs) ([makenegative y | y <-subf $ removesign f, deletewarning (makenegative y ) ]++fnegpending) fcpending]]
              else [[Nd i positives negatives falses ([makefalse y | y <-subf $ removesign f, not (deletewarning (makefalse y)) ]++fs) fnegpending ([makefalse y | y <-subf $ removesign f, deletewarning  (makefalse y) ]++fcpending)]]
  | rule2 f = if signof f == T then [[Nd (i++[0]) positives negatives falses (maketrue (head (subf $ removesign f)): fs) fnegpending fcpending, Nd (i++[1]) positives negatives falses (map maketrue (tail (subf (removesign f))) ++ fs) fnegpending fcpending ]]
              else [[Nd (i++[0]) positives negatives falses ([makenegative (head (subf (removesign f))) | not (deletewarning (makenegative (head (subf (removesign f))))) ]++fs) ([makenegative (head (subf (removesign f))) | deletewarning (makenegative (head (subf (removesign f)))) ]++fnegpending) fcpending, Nd (i++[1]) positives negatives falses ([makenegative (last (subf (removesign f))) | not (deletewarning (makenegative (last (subf (removesign f))))) ]++fs) ([makenegative (last (subf (removesign f))) | deletewarning (makenegative (last (subf (removesign f)))) ]++fnegpending) fcpending]]
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))] [] fcpending ]]
  | prfalseconj f = [[Nd (i++[0]) positives [] falses [makefalse (head (subf (removesign f))) | not (deletewarning (makefalse (head (subf (removesign f)))) )] [] ([makefalse (head (subf (removesign f))) | deletewarning (makefalse (head (subf (removesign f)))) ]++ fs ), Nd (i++[1]) positives [] falses [makefalse (last (subf (removesign f))) | not (deletewarning (makefalse (last (subf (removesign f)))) )] [] ([makefalse (last (subf (removesign f))) | deletewarning (makefalse (last (subf (removesign f)))) ]++fs) ]]
  | trueneg f = [[Nd i positives negatives falses ([makefalse (head (subf (removesign f))) | not (deletewarning (makefalse (head (subf (removesign f)))) )]++fs) fnegpending ([makefalse (head (subf (removesign f))) | deletewarning (makefalse (head (subf (removesign f)))) ]++fcpending) ]]
step (Nd i positives _ falses [] (f:fs) fcpending)
  | tlit  f = undefined
  | flit  f = undefined
  | fclit  f = undefined
  | rule1 f = undefined
  | rule2 f = undefined
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))] [] fcpending ] , [Nd i positives [] falses [] fs fcpending]]
  | prfalseconj f = undefined
  | trueneg f = undefined
step (Nd i positives _ falses [] [] (f:fs))
  | tlit  f = undefined
  | flit  f = undefined
  | fclit  f = undefined
  | rule1 f = undefined
  | rule2 f = undefined
  | falseneg f = [[Nd i positives [] falses [maketrue (head (subf (removesign f)))] [] fs ]]
  | prfalseconj f = [[Nd (i++[0]) positives [] falses [makefalse (head (subf (removesign f))) | not (deletewarning (makefalse (head (subf (removesign f)))) )] [] ([makefalse (head (subf (removesign f))) | deletewarning (makefalse (head (subf (removesign f)))) ]++ fs ), Nd (i++[1]) positives [] falses [makefalse (last (subf (removesign f))) | not (deletewarning (makefalse (last (subf (removesign f)))) )] [] ([makefalse (last (subf (removesign f))) | deletewarning (makefalse (last (subf (removesign f)))) ]++fs) ]]
  | trueneg f = undefined

expanded :: Node -> Bool                             --function which checks whether a node is expanded
expanded (Nd _ _ _ _ [] [] [])  = True
expanded  _                                = False

badNode :: Node -> Bool                              --function which checks whether a node will be expanded in a way that leads to a cancellation of formulas
badNode (Nd _ _ _ _ [] x _) | not(null x) = True              --these nodes must be treated differently
                            | otherwise   = False
badNode _                                 = False

badTab :: Tableau -> Bool                            --function which checks whether a tableau has at least one bad node
badTab = any badNode

firstbad :: Tableau -> Node                          --function which detects the first bad node of a tableau, if there is one, and is undefined otherwise
firstbad [] = undefined
firstbad (n : ns)
  | not (badTab (n:ns)) = undefined
  | badNode n = n
  | otherwise = firstbad ns

removebad :: Tableau -> Tableau                      --function which removes the first bad node out of a bad tableau
removebad tab | badTab tab = tab \\ [firstbad tab]
              | otherwise = tab

expand :: Tableau -> [Tableau]                                  --function which, given a tableau, outputs its "one step" nondeterministic expansion
expand tab | not (badTab tab) = [concatMap (head . step) tab]
           | otherwise = [ head (step (firstbad tab)) ++ removebad tab, last (step (firstbad tab)) ++ removebad tab ]

pairify :: [Tableau] -> [(Tableau, Tableau)]                        --function which splits a given tableau in its expanded and nonexpanded sections
pairify = map \x-> (filter (not . expanded) x , filter expanded x)

solve :: [(Tableau, Tableau)] -> Bool                               --recursive function which expands a tableau fully until a decision on the validity
solve []        = False                                             --of the formula in question can be made
solve (p:pairs) | null (snd p) && not (null (fst p)) = solve (pairify (expand(fst p))++ pairs)
                | null (snd p) && null (fst p) = True
                | otherwise = solve pairs || False

initintuitTab :: Frm -> Tableau                                     --function which, given a formula, initializes the corresponding intuitionistic tableau
initintuitTab  f = [Nd [] [] [] [] [S (F, f)] [] []]                --which will later be fed to solve

intuitthm :: Frm -> Bool                                            --function which determines theoremhood for an intuitionistic formula
intuitthm f = solve [(initintuitTab f, [])]

intuitsat :: Frm -> Bool                                            --function which determines satisfiability of an intuitionistic formula
intuitsat f = not ( intuitthm (N f))

initclassTab:: Frm -> Tableau                                       --function which, given a formula, initializes the corresponding classical tableau
initclassTab  f = [Nd [] [] [] [] [S (Fc, f)] [] []]              --which will later be fed to solve

classthm :: Frm -> Bool                                             --function which determines theoremhood for an classical formula
classthm f = solve [(initclassTab f, [])]

classsat :: Frm -> Bool                                             --function which determines satisfiability of an classical formula
classsat f = not (classthm (N f))

glivenko :: Frm -> Bool                                             --property which encodes glivenko's theorem. can be used with quickCheck
glivenko f = classthm f == intuitthm (N (N f))                      --as quickCheck (\f -> glivenko f)
