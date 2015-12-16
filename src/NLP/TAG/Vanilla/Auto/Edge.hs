module NLP.TAG.Vanilla.Auto.Edge
( Edge (..)
) where


-- | A datatype to distinguish head non-terminals from body
-- non-terminals.
data Edge a
    = Head a
    | Body a
    deriving (Show, Eq, Ord)
