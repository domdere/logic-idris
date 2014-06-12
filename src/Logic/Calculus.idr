module Logic.Calculus

import Logic.Types.Conjunction
import Logic.Types.Disjunction
import Logic.Types.Implication
import Logic.Types.Not

%access public

total
modusPonens : ((a ==> b) /\ a) -> b
modusPonens (Split (Implies f) x) = f x

total
modusTollens : ((a ==> b) /\ ((~) b)) -> ((~) a)
modusTollens (Split (Implies f) (Not g)) = Not (g . f)

total
hypotheticalSyllogism : ((a ==> b) /\ (b ==> c)) -> (a ==> c)
hypotheticalSyllogism (Split (Implies f) (Implies g)) = Implies (g . f)

total
disjunctiveSyllogism : ((a \/ b) /\ ((~) a)) -> b
disjunctiveSyllogism (Split (LeftP x) (Not f))  = absurd (f x)
disjunctiveSyllogism (Split (RightP y) (Not f)) = y

total
composition : ((a ==> b) /\ (a ==> c)) -> a ==> (b /\ c)
composition (Split (Implies fb) (Implies fc)) = Implies go
    where
        go : a -> (b /\ c)
        go x = Split (fb x) (fc x)

total
cocomposition : ((a ==> c) /\ (b ==> c)) -> (a \/ b) ==> c
cocomposition (Split (Implies fa) (Implies fb)) = Implies (go fa fb)
    where
        go : (a -> c) -> (b -> c) -> (a \/ b) -> c
        go f g (LeftP x)  = f x
        go f g (RightP x) = g x

total
constructiveDilemma : ((a ==> c) /\ (b ==> d) /\ (a \/ b)) -> (c \/ d)
constructiveDilemma x = ?constructiveDilemma_rhs

total
destructiveDilemma : ((a ==> c) /\ (b ==> d) /\ (((~) c) \/ ((~) d))) -> (((~) a) \/ ((~) b))
destructiveDilemma h = ?destructiveDilemma_rhs

total
bidirectionalDilemma : ((a ==> b) /\ (c ==> d) /\ (a \/ ((~) d))) -> (b \/ ((~) c))
bidirectionalDilemma h = ?bidirectionalDilemma_rhs

total
simplificationLeft : (a /\ b) -> a
simplificationLeft (Split x y) = x

total
simplificationRight : (a /\ b) -> b
simplificationRight (Split x y) = y

total
deMorgansConj : (((~) a) \/ ((~) b)) -> (~) (a /\ b)
deMorgansConj h = Not (go h)
    where
        go : (((~) a) \/ ((~) b)) -> (a /\ b) -> _|_
        go (LeftP (Not abs)) (Split x y) = abs x
        go (RightP (Not abs)) (Split x y) = abs y

total
deMorgansDisj : ((~) (a \/ b)) <=> (((~) a) /\ ((~) b))
deMorgansDisj = Iff (Implies deMorgansDisjl) (Implies deMorgansDisjr)
    where
        deMorgansDisjl : (~) (a \/ b) -> (((~) a) /\ ((~) b))
        deMorgansDisjl (Not abs) = Split (Not (abs . LeftP)) (Not (abs . RightP))

        deMorgansDisjr : (((~) a) /\ ((~) b)) -> (~) (a \/ b)
        deMorgansDisjr (Split (Not notA) (Not notB)) = Not (go notA notB)
            where
                go : (a -> _|_) -> (b -> _|_) -> (a \/ b) -> _|_
                go f g (LeftP x) = f x
                go f g (RightP y) = g y

||| A <=> B is equivalent to B <=> A
|||
total
commuteIff : (a <=> b) -> (b <=> a)
commuteIff (Iff x y) = Iff y x

total
commuteConjunction : (a /\ b) -> (b /\ a)
commuteConjunction (Split x y) = Split y x

total
commuteDisjunction : (a \/ b) -> (b \/ a)
commuteDisjunction (LeftP x)  = RightP x
commuteDisjunction (RightP y) = LeftP y

total
associativeConjunction : (a /\ b /\ c) -> (a /\ b) /\ c
associativeConjunction (Split x (Split y z)) = Split (Split x y) z

total
associativeDisjunction : (a \/ b \/ c) -> (a \/ b) \/ c
associativeDisjunction (LeftP x)            = LeftP (LeftP x)
associativeDisjunction (RightP (LeftP y))   = LeftP (RightP y)
associativeDisjunction (RightP (RightP z))  = RightP z

total
distributeConjunction : (a /\ (b \/ c)) -> (a /\ b) \/ (a /\ c)
distributeConjunction (Split x (LeftP y))   = LeftP (Split x y)
distributeConjunction (Split x (RightP z))  = RightP (Split x z)

total
doubleNegation : a -> (~) ((~) a)
doubleNegation h = Not go
    where
        go : (~) a -> _|_
        go (Not abs) = abs h


total
transposition : (a ==> b) -> (((~) b) ==> ((~) a))
transposition h = ?transposition_rhs

total
materialEquivalence1 : (a <=> b) -> (a ==> b) /\ (b ==> a)
materialEquivalence1 (Iff f g) = Split f g

total
exportation : (a /\ b) ==> c -> a ==> b ==> c
exportation h = ?exportation_rhs

---------- Proofs ----------

exportation_rhs = proof
  intros
  induction h
  intro hf
  refine Implies
  intro x
  refine Implies
  intro y
  let z = hf (Split x y)
  refine z


transposition_rhs = proof
  intros
  refine Implies
  intro notB
  induction h
  intro h1
  induction notB
  intro f
  let notA = Logic.Types.Not.Not (f . h1)
  refine notA


bidirectionalDilemma_rhs = proof
  intros
  induction h
  intro h1
  intro h2
  induction h2
  intro h3
  intro h4
  induction h4
  intro x
  let h1Andx = Split h1 x
  let modusponens = modusPonens h1Andx
  refine LeftP
  refine modusponens
  intro h5
  let h3Andh5 = Split h3 h5
  let modustollens = modusTollens h3Andh5
  refine RightP
  refine modustollens


destructiveDilemma_rhs = proof
  intros
  induction h
  intro h1
  intro h2
  induction h2
  intro h3
  intro h4
  induction h4
  intro notC
  let h1AndNotC = Split h1 notC
  let modustollens = modusTollens h1AndNotC
  refine LeftP
  refine modustollens
  intro notD
  let h3AndNotD = Split h3 notD
  let modustollens1 = modusTollens h3AndNotD
  refine RightP
  refine modustollens1


constructiveDilemma_rhs = proof
  intros
  induction x
  intro h
  intro h2
  induction h2
  intro h3
  intro h4
  induction h2
  intro h5
  intro h6
  induction h6
  intro u
  induction h
  intro f
  refine LeftP
  refine f
  refine u
  intro v
  induction h5
  intro g
  refine RightP
  refine g
  refine v


