module Disjunction

infixr 2 \/

||| A disjunction of propositions,
||| A \\/ B implies that at least one of either
||| A or B is true, i.e a proof for either A
||| of B is a necessary and sufficient condition
||| to prove A \\/ B.
|||
||| A Proof for A is sufficient to prove A \\/ B (LeftP)
||| "refine LeftP" in the interactive prover will refine a goal of the form
||| A \\/ B into A
|||
||| A Proof for B is also sufficient to prove A \\/ B (RightP)
||| "refine RightP" in the interactive prover will refine a goal of the form
||| A \\/ B into B
|||
%elim data (\/) a b =
        LeftP a
    |   RightP b


