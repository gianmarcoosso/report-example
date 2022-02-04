\subsection{Formulas}

\begin{code}
module Formulas where

import.Data.List
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

\end{code}


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

instance Eq SFrm where
  S (x,y) == S (z,v) = (x,y)==(z,v)
  
subf :: Frm -> [Frm]
subf (P x) = [P x]
subf (N f) = [f]
subf (C f g) = [f,g]
subf (D f g) = [f,g]

\end{code}
The subf function is a tool that will be needed for tableau expansion.
