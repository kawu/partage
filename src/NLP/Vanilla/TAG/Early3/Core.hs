{- 
 - Early parser for TAGs: Core Types.
 -}


module NLP.LTAG.Early3.Core where


-- | Position in the sentence.
type Pos = Int


-- | Additional identifier.
type ID = Int


-- | Symbol: a (non-terminal, maybe identifier) pair.
type Sym n = (n, Maybe ID)


-- | Label: either a symbol or a terminal.
type Lab n t = Either (Sym n) t
