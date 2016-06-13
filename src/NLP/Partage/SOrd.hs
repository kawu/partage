{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}


-- | Internal typeclass representing `Show` + `Ord`.


module NLP.Partage.SOrd
( HOrd
, SOrd
) where


-- import qualified Data.Hashable              as H


-- | 'Ord' + 'Hashable'
-- class (Ord a, H.Hashable a) => HOrd a where
-- instance (Ord a, H.Hashable a) => HOrd a where
class (Ord a) => HOrd a where
instance (Ord a) => HOrd a where


-- | 'Show' + 'Ord'
#ifdef DebugOn
class (Show a, HOrd a) => SOrd a where
instance (Show a, HOrd a) => SOrd a where
#else
class HOrd a => SOrd a where
instance HOrd a => SOrd a where
#endif
