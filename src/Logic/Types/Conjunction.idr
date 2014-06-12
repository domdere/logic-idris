module Conjunction

infixr 3 /\

||| A conjunction of propositions,
||| A /\\ B implies that both A and B are true,
||| So proofs for both cases are required to prove the
||| the case for A /\\ B.
|||
%elim data (/\) a b =
    ||| Proofs for both A and B are required to prove A /\\ B.
    |||
    ||| "refine Split" will split a goal of the form A /\\ B into
    ||| two separate goals A and B that will both have to be proven
    |||
    ||| @ a A proof for A
    ||| @ b A proof for B
    |||
    Split a b


