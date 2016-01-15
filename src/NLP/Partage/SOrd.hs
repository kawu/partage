{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE CPP #-}


-- | Internal typeclass representing `Show` + `Ord`.


module NLP.Partage.SOrd
( SOrd
) where


-- | 'Show' + 'Ord'
#ifdef Debug
class (Show a, Ord a) => SOrd a where
instance (Show a, Ord a) => SOrd a where
#else
class Ord a => SOrd a where
instance Ord a => SOrd a where
#endif
