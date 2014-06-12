module Implication

infixr 4 ==>

||| Implication
||| An Implication relation A -> B
||| Is equivalent to a function that takes a proof
||| of A to a proof of B.
||| This type is essentially a newtype for
||| the (->) operator
|||
%elim data (==>) a b =
    ||| A function that takes a proof of A
    ||| to a proof of B
    |||
    Implies (a -> b)

infixr 4 <=>

||| iff
||| if A ==> B and B ==> A then we have (A <=> B) or B iff A
|||
%elim data (<=>) : Type -> Type -> Type where
    Iff : (a ==> b) -> (b ==> a) -> (a <=> b)

||| ==> functions

||| All impliclations (A ==> B) have a function (A -> B) on proofs
|||
implicationFunction : (a ==> b) -> a -> b
implicationFunction (Implies f) = f

||| "refine implicationAssumption"
||| will refine a goal of the form ((a ==> b) ==> c)
||| into the form (a -> b) ==> c
|||
implicationAssumption : ((a -> b) ==> c) -> ((a ==> b) ==> c)
implicationAssumption (Implies f) = Implies (f . implicationFunction)

implicationTransitivity : (a ==> b) -> (b ==> c) -> (a ==> c)
implicationTransitivity (Implies f) (Implies g) = Implies (g . f)

||| <=> functions

||| with A <=> B you can infer B from A
|||
inferToRight : a <=> b -> a -> b
inferToRight (Iff (Implies f) (Implies g)) x = f x

||| with A <=> B you can infer A from B
|||
inferToLeft : a <=> b -> b -> a
inferToLeft (Iff (Implies f) (Implies g)) y = g y

