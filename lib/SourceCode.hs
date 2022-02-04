\subsection{Helper functions for step}

The following are helper functions which are needed in the definition of step, they are pretty much self explainatory

\begin{code}

rule1 :: SFrm -> Bool                  
rule1 (S (T, C _ _))  = True         
rule1 (S (F, D _ _))  = True
rule1 (S (Fc, D _ _)) = True
rule1 _               = False

rule2 :: SFrm -> Bool                  
rule2 (S (T, D _ _))  = True        
rule2 (S (F, C _ _))  = True
rule2 _               = False

falseneg :: SFrm -> Bool               
falseneg (S (F, N _))  = True        
falseneg (S (Fc, N _)) = True
falseneg _             = False

prfalseconj :: SFrm -> Bool            
prfalseconj (S (Fc, C _ _)) = True   
prfalseconj _               = False

trueneg :: SFrm -> Bool                
trueneg (S (T, N _)) = True
trueneg _            = False


deletewarning :: SFrm -> Bool         
deletewarning (S (x, y)) = prfalseconj (S (x, y)) || falseneg (S (x, y))

tlit, flit, fclit :: SFrm -> Bool
tlit (S (T, P _))    = True
tlit _               = False
flit (S (F, P _))    = True
flit _               = False
fclit (S (Fc, P _))  = True
fclit _              = False

makesign :: Sign -> Frm -> SFrm
makesign x y = S (x,y)
makenegative :: Frm -> SFrm
makenegative f = S (F,f)
maketrue :: Frm -> SFrm
maketrue f = S (T,f)
makefalse :: Frm -> SFrm
makefalse f= S (Fc, f)

removesign :: SFrm -> Frm
removesign (S (_, f)) = f

signof:: SFrm -> Sign
signof (S (T, _ )) = T
signof (S (F, _ )) = F
signof (S (Fc, _)) = Fc
\end{code}
