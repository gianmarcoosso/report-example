\subsection{Tableaux}

\begin{code}
module Tableau where

import Formulas

\end{code}

We represent a node in the following way. Each node is composed of six lists, the list of true atoms ($T p$), of false atoms ($F p$), of refuted atoms ($F_C p$), the list of pending formulas that don't lead to any deletion of $F$ formulas in the set $S$; the last two lists are a list of pending formulas with the shape $F(\neg \varphi)$ and a list that only contains pending formulas with the shape $F_C(\neg \varphi)$ and $F_C(\varphi \wedge \psi)$. A tableau is then just a list of nodes: in particular, they are stored as the list corresponding to their \say{leaf level}, as that encodes all the necessary information.\\

\begin{code}
data Node  = Nd Index [Frm] [Frm] [Frm] [SFrm] [SFrm] [Sfrm]
instance Eq Node where
  Nd i p n f tp fp fcp == Nd j d s a ta fa fca = i==j && p==d && n==s && f==a && tp==ta && fp==fa && fcp ==fca
type Tableau = [Node]
\end{code}

The reason for having three separate lists of pending formulas is that we want to distinguish them based on how tricky their associated rule is. In particular, we know that applying the rules to formulas of the form $F \neg$, $F_C \neg$ and $F_C \land$ leads to cancellation of all remaining $F$ formulas and need to be treated carefully in order to preserve completeness of the system.

