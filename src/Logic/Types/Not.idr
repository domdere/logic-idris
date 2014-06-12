module Logic.Types.Not

||| Declares A as False
|||
%elim data (~) a =
    ||| You can infer False from A if ~A
    Not (a -> _|_)
