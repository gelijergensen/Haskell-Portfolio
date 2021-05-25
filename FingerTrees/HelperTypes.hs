{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{- Helper types and functions for Finger Trees -}
module HelperTypes where

data Digit a
  = One a
  | Two a a
  | Three a a a
  | Four a a a a
  deriving (Eq, Show)

data Node v a
  = Node2 v a a
  | Node3 v a a a
  deriving (Eq, Show)

data Split f a
  = Single a
  | First a (f a)
  | Last (f a) a
  | Middle (f a) a (f a)
  deriving (Eq, Show)

newtype LookUp v a = LookUp
  { getLookUp :: (v, a)
  }
  deriving (Eq, Show)

class
  Monoid v =>
  Measured a v
  where
  measure :: a -> v

instance (Measured a v) => Measured (Digit a) v where
  measure (One a) = measure a
  measure (Two a b) = measure a <> measure b
  measure (Three a b c) = measure a <> measure b <> measure c
  measure (Four a b c d) = measure a <> measure b <> measure c <> measure d

instance (Monoid v) => Measured (Node v a) v where
  measure (Node2 v _ _) = v
  measure (Node3 v _ _ _) = v

instance Foldable Digit where
  foldr f z (One a) = f a z
  foldr f z (Two a b) = f a $ f b z
  foldr f z (Three a b c) = f a $ f b $ f c z
  foldr f z (Four a b c d) = f a $ f b $ f c $ f d z
  foldl f z (One a) = f z a
  foldl f z (Two b a) = f (f z b) a
  foldl f z (Three c b a) = f (f (f z c) b) a
  foldl f z (Four d c b a) = f (f (f (f z d) c) b) a

instance Foldable (Node v) where
  foldr f z (Node2 _ a b) = f a $ f b z
  foldr f z (Node3 _ a b c) = f a $ f b $ f c z
  foldl f z (Node2 _ b a) = f (f z b) a
  foldl f z (Node3 _ c b a) = f (f (f z c) b) a

node2 :: (Measured a v) => a -> a -> Node v a
node2 x y = Node2 (measure x <> measure y) x y

node3 :: (Measured a v) => a -> a -> a -> Node v a
node3 x y z = Node3 (measure x <> measure y <> measure z) x y z

unpackNode :: Node v a -> Digit a
unpackNode (Node2 _ a b) = Two a b
unpackNode (Node3 _ a b c) = Three a b c

decrL :: Digit a -> (a, Digit a)
decrL (Two a b) = (a, One b)
decrL (Three a b c) = (a, Two b c)
decrL (Four a b c d) = (a, Three b c d)

decrR :: Digit a -> (Digit a, a)
decrR (Two a b) = (One a, b)
decrR (Three a b c) = (Two a b, c)
decrR (Four a b c d) = (Three a b c, d)

incrL :: a -> Digit a -> Digit a
incrL a (One b) = Two a b
incrL a (Two b c) = Three a b c
incrL a (Three b c d) = Four a b c d

incrR :: Digit a -> a -> Digit a
incrR (One b) a = Two b a
incrR (Two c b) a = Three c b a
incrR (Three d c b) a = Four d c b a

{- Assumptions:
  p i == False
  p (i <> measure x) == True
  in
    splitDigit p i x
-}
splitDigit :: (Measured a v) => (v -> Bool) -> v -> Digit a -> Split Digit a
splitDigit _ _ (One a) = Single a
splitDigit p i (Two a b) =
  if p (i <> measure a)
    then First a (One b)
    else Last (One a) b
splitDigit p i (Three a b c)
  | p iab =
    if p ia
      then First a (Two b c)
      else Middle (One a) b (One c)
  | otherwise = Last (Two a b) c
  where
    ia = i <> measure a
    iab = ia <> measure b
splitDigit p i (Four a b c d)
  | p iab =
    if p ia
      then First a (Three b c d)
      else Middle (One a) b (Two c d)
  | otherwise =
    if p iabc
      then Middle (Two a b) c (One d)
      else Last (Three a b c) d
  where
    ia = i <> measure a
    iab = ia <> measure b
    iabc = iab <> measure c

lookupDigit :: (Measured a v) => (v -> Bool) -> v -> Digit a -> LookUp v a
lookupDigit _ i (One a) = LookUp (i, a)
lookupDigit p i (Two a b)
  | p ia = LookUp (i, a)
  | otherwise = LookUp (ia, b)
  where
    ia = i <> measure a
lookupDigit p i (Three a b c)
  | p iab =
    if p ia
      then LookUp (i, a)
      else LookUp (ia, b)
  | otherwise = LookUp (iab, c)
  where
    ia = i <> measure a
    iab = ia <> measure b
lookupDigit p i (Four a b c d)
  | p iab =
    if p ia
      then LookUp (i, a)
      else LookUp (ia, b)
  | otherwise =
    if p iabc
      then LookUp (iab, c)
      else LookUp (iabc, d)
  where
    ia = i <> measure a
    iab = ia <> measure b
    iabc = iab <> measure c

lookupNode :: (Measured a v) => (v -> Bool) -> v -> Node v a -> LookUp v a
lookupNode p i (Node2 _ a b)
  | p ia = LookUp (i, a)
  | otherwise = LookUp (ia, b)
  where
    ia = i <> measure a
lookupNode p i (Node3 _ a b c)
  | p iab =
    if p ia
      then LookUp (i, a)
      else LookUp (ia, b)
  | otherwise = LookUp (iab, c)
  where
    ia = i <> measure a
    iab = ia <> measure b

-- Ugly function for merging 2 or three digits
mergeDigits ::
  (Measured a v) => Digit a -> Maybe (Digit a) -> Digit a -> Digit (Node v a)
mergeDigits (One a) Nothing (One b) = One (node2 a b)
mergeDigits (One a) Nothing (Two b c) = One (node3 a b c)
mergeDigits (One a) Nothing (Three b c d) = Two (node2 a b) (node2 c d)
mergeDigits (One a) Nothing (Four b c d e) = Two (node3 a b c) (node2 d e)
mergeDigits (Two a b) Nothing (One c) = One (node3 a b c)
mergeDigits (Two a b) Nothing (Two c d) = Two (node2 a b) (node2 c d)
mergeDigits (Two a b) Nothing (Three c d e) = Two (node3 a b c) (node2 d e)
mergeDigits (Two a b) Nothing (Four c d e f) = Two (node3 a b c) (node3 d e f)
mergeDigits (Three a b c) Nothing (One d) = Two (node2 a b) (node2 c d)
mergeDigits (Three a b c) Nothing (Two d e) = Two (node3 a b c) (node2 d e)
mergeDigits (Three a b c) Nothing (Three d e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Three a b c) Nothing (Four d e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Four a b c d) Nothing (One e) = Two (node3 a b c) (node2 d e)
mergeDigits (Four a b c d) Nothing (Two e f) = Two (node3 a b c) (node3 d e f)
mergeDigits (Four a b c d) Nothing (Three e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Four a b c d) Nothing (Four e f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (One a) (Just (One b)) (One c) = One (node3 a b c)
mergeDigits (One a) (Just (One b)) (Two c d) = Two (node2 a b) (node2 c d)
mergeDigits (One a) (Just (One b)) (Three c d e) = Two (node3 a b c) (node2 d e)
mergeDigits (One a) (Just (One b)) (Four c d e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (One a) (Just (Two b c)) (One d) = Two (node2 a b) (node2 c d)
mergeDigits (One a) (Just (Two b c)) (Two d e) = Two (node3 a b c) (node2 d e)
mergeDigits (One a) (Just (Two b c)) (Three d e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (One a) (Just (Two b c)) (Four d e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (One a) (Just (Three b c d)) (One e) = Two (node3 a b c) (node2 d e)
mergeDigits (One a) (Just (Three b c d)) (Two e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (One a) (Just (Three b c d)) (Three e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (One a) (Just (Three b c d)) (Four e f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (One a) (Just (Four b c d e)) (One f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (One a) (Just (Four b c d e)) (Two f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (One a) (Just (Four b c d e)) (Three f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (One a) (Just (Four b c d e)) (Four f g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Two a b) (Just (One c)) (One d) = Two (node2 a b) (node2 c d)
mergeDigits (Two a b) (Just (One c)) (Two d e) = Two (node3 a b c) (node2 d e)
mergeDigits (Two a b) (Just (One c)) (Three d e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Two a b) (Just (One c)) (Four d e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Two a b) (Just (Two c d)) (One e) = Two (node3 a b c) (node2 d e)
mergeDigits (Two a b) (Just (Two c d)) (Two e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Two a b) (Just (Two c d)) (Three e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Two a b) (Just (Two c d)) (Four e f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Two a b) (Just (Three c d e)) (One f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Two a b) (Just (Three c d e)) (Two f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Two a b) (Just (Three c d e)) (Three f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Two a b) (Just (Three c d e)) (Four f g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Two a b) (Just (Four c d e f)) (One g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Two a b) (Just (Four c d e f)) (Two g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Two a b) (Just (Four c d e f)) (Three g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Two a b) (Just (Four c d e f)) (Four g h i j) =
  Four (node3 a b c) (node3 d e f) (node2 g h) (node2 i j)
mergeDigits (Three a b c) (Just (One d)) (One e) = Two (node3 a b c) (node2 d e)
mergeDigits (Three a b c) (Just (One d)) (Two e f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Three a b c) (Just (One d)) (Three e f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Three a b c) (Just (One d)) (Four e f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Three a b c) (Just (Two d e)) (One f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Three a b c) (Just (Two d e)) (Two f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Three a b c) (Just (Two d e)) (Three f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Three a b c) (Just (Two d e)) (Four f g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Three a b c) (Just (Three d e f)) (One g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Three a b c) (Just (Three d e f)) (Two g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Three a b c) (Just (Three d e f)) (Three g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Three a b c) (Just (Three d e f)) (Four g h i j) =
  Four (node3 a b c) (node3 d e f) (node2 g h) (node2 i j)
mergeDigits (Three a b c) (Just (Four d e f g)) (One h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Three a b c) (Just (Four d e f g)) (Two h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Three a b c) (Just (Four d e f g)) (Three h i j) =
  Four (node3 a b c) (node3 d e f) (node2 g h) (node2 i j)
mergeDigits (Three a b c) (Just (Four d e f g)) (Four h i j k) =
  Four (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k)
mergeDigits (Four a b c d) (Just (One e)) (One f) =
  Two (node3 a b c) (node3 d e f)
mergeDigits (Four a b c d) (Just (One e)) (Two f g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Four a b c d) (Just (One e)) (Three f g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Four a b c d) (Just (One e)) (Four f g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Four a b c d) (Just (Two e f)) (One g) =
  Three (node3 a b c) (node2 d e) (node2 f g)
mergeDigits (Four a b c d) (Just (Two e f)) (Two g h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Four a b c d) (Just (Two e f)) (Three g h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Four a b c d) (Just (Two e f)) (Four g h i j) =
  Four (node3 a b c) (node3 d e f) (node2 g h) (node2 i j)
mergeDigits (Four a b c d) (Just (Three e f g)) (One h) =
  Three (node3 a b c) (node3 d e f) (node2 g h)
mergeDigits (Four a b c d) (Just (Three e f g)) (Two h i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Four a b c d) (Just (Three e f g)) (Three h i j) =
  Four (node3 a b c) (node3 d e f) (node2 g h) (node2 i j)
mergeDigits (Four a b c d) (Just (Three e f g)) (Four h i j k) =
  Four (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k)
mergeDigits (Four a b c d) (Just (Four e f g h)) (One i) =
  Three (node3 a b c) (node3 d e f) (node3 g h i)
mergeDigits (Four a b c d) (Just (Four e f g h)) (Two i j) =
  Four (node3 a b c) (node3 d e f) (node2 g h) (node2 i j)
mergeDigits (Four a b c d) (Just (Four e f g h)) (Three i j k) =
  Four (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k)
mergeDigits (Four a b c d) (Just (Four e f g h)) (Four i j k l) =
  Four (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l)
