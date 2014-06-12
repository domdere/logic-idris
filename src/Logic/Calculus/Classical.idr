module Logic.Calculus.Classical

import Logic.Calculus

import Logic.Types.Conjunction
import Logic.Types.Disjunction
import Logic.Types.Implication
import Logic.Types.Not

%access public

||| Can't prove this with Constructivist logic either,
||| we are give a function (a /\\ b) -> False but no
||| way to produce an a /\\b to make use of it
|||
total
unsafeDeMorgansConj : (~) (a /\ b) -> ((~) a) \/ ((~) b)
unsafeDeMorgansConj = believe_me

total
unsafeMaterialImplication : (a ==> b) -> (((~) a) \/ b)
unsafeMaterialImplication = believe_me

total
materialEquivalence2 : (a <=> b) -> (a /\ b) \/ (((~) a) /\ ((~) b))
materialEquivalence2 = believe_me

total
materialEquivalence3 : (a <=> b) -> (a \/ ((~) b)) /\ (((~) a) \/ b)
materialEquivalence3 = believe_me


-- or at least i havent been able to prove these things


