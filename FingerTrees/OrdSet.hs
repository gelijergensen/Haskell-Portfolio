{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- An implementation of Ordered Sets -}
module OrdSet
  ( OrdSet (Empty),
    empty,
    singleton,
    null,
    size,
    toList,
    fromList,
    fromAscList,
    fromDescList,
    fromDistinctAscList,
    fromDistinctDescList,
    insert,
    delete,
    member,
    union,
    intersection,
    difference,
    isDisjointFrom,
    isSubsetOf,
    isSupsetOf,
    smallestElem,
    kthSmallestElem,
    largestElem,
    kthLargestElem,
    fromFoldable,
    fromAscFoldable,
    fromDescFoldable,
    fromDistinctAscFoldable,
    fromDistinctDescFoldable,
  )
where

import qualified FingerTree as Base
import Prelude hiding (null)

newtype OrdSet a
  = OrdSet (Base.FingerTree (SizeMax a) (Elem a))

newtype Elem a = Elem
  { getElem :: a
  }
  deriving (Eq, Show)

newtype SizeMax a = SizeMax
  { unSizeMax :: (Size, Max a)
  }
  deriving (Eq, Show)

data Max a
  = NegInfinity
  | Max
      { unMax :: a
      }
  deriving (Eq, Ord, Show)

newtype Size = Size
  { unSize :: Integer
  }
  deriving (Eq, Ord, Show)

instance Semigroup (SizeMax a) where
  SizeMax x <> SizeMax y = SizeMax (x <> y)

instance Monoid (SizeMax a) where
  mempty = SizeMax mempty

instance Semigroup Size where
  Size x <> Size y = Size (x + y)

instance Monoid Size where
  mempty = Size 0

instance Semigroup (Max a) where
  x <> NegInfinity = x
  _ <> x = x

instance Monoid (Max a) where
  mempty = NegInfinity

instance Base.Measured (Elem a) (SizeMax a) where
  measure (Elem x) = SizeMax (Size 1, Max x)

instance Foldable OrdSet where
  foldr f z (OrdSet xs) = foldr f' z xs
    where
      f' a b = f (getElem a) b
  foldl f z (OrdSet xs) = foldl f' z xs
    where
      f' a b = f a (getElem b)

instance (Show a) => Show (OrdSet a) where
  showsPrec p xs =
    showParen (p > 10) $ showString "fromList " . shows (toList xs)

instance (Ord a) => Eq (OrdSet a) where
  xs == ys = xs `isSubsetOf` ys && ys `isSubsetOf` xs

empty :: OrdSet a
empty = OrdSet Base.Empty

singleton :: a -> OrdSet a
singleton = OrdSet . Base.singleton . Elem

pattern Empty :: OrdSet a
pattern Empty = OrdSet Base.Empty

{- O(1) -}
null :: OrdSet a -> Bool
null Empty = True
null _ = False

{- O(1) -}
size :: OrdSet a -> Integer
size (OrdSet xs) = size' xs

{- O(n) -}
toList :: OrdSet a -> [a]
toList = foldr (:) []

{- See fromFoldable -}
fromList :: Ord a => [a] -> OrdSet a
fromList = fromFoldable

{- See fromAscFoldable -}
fromAscList :: Eq a => [a] -> OrdSet a
fromAscList = fromAscFoldable

{- See fromDescFoldable -}
fromDescList :: Eq a => [a] -> OrdSet a
fromDescList = fromDescFoldable

{- See fromDistinctAscFoldable -}
fromDistinctAscList :: [a] -> OrdSet a
fromDistinctAscList = fromDistinctAscFoldable

{- See fromDistinctDescFoldable -}
fromDistinctDescList :: [a] -> OrdSet a
fromDistinctDescList = fromDistinctDescFoldable

{- O(log(i)), where i <= n/2 is distance from
   insert point to nearest end -}
insert :: (Ord a) => a -> OrdSet a -> OrdSet a
insert a Empty = singleton a
insert a ordset@(OrdSet xs) =
  case r of
    Base.Empty -> OrdSet $ l Base.:|> Elem a
    x Base.:<| _ ->
      if a == getElem x
        then ordset
        else OrdSet $ l Base.>< (Elem a Base.:<| r)
  where
    (l, r) = Base.split ((Max a <=) . getMax) xs

{- O(log(i)), where i <= n/2 is distance from
   delete point to nearest end -}
delete :: (Ord a) => a -> OrdSet a -> OrdSet a
delete a Empty = Empty
delete a ordset@(OrdSet xs) =
  case r of
    Base.Empty -> ordset
    x Base.:<| r' ->
      if a == getElem x
        then OrdSet $ l Base.>< r'
        else ordset
  where
    (l, r) = Base.split ((Max a <=) . getMax) xs

{- O(log(i)), where i <= n/2 is distance from
   member location to nearest end -}
member :: (Ord a) => a -> OrdSet a -> Bool
member a (OrdSet xs) =
  case Base.lookup ((Max a <=) . getMax) xs of
    Nothing -> False
    Just (Elem x) -> a == x

-- Set theoretic functions
{- Probably amortized O(m log(n/m + 1),
   where m <= n lengths of xs and ys -}
union :: (Ord a) => OrdSet a -> OrdSet a -> OrdSet a
union (OrdSet xs) (OrdSet ys) = OrdSet $ _union xs ys
  where
    _union Base.Empty bs = bs
    _union as Base.Empty = as
    _union as bs@(b Base.:<| bs') =
      case r of
        Base.Empty -> l Base.>< bs
        x Base.:<| r' ->
          if x == b
            then (l Base.:|> b) Base.>< _union bs' r'
            else (l Base.:|> b) Base.>< _union bs' r
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as

{- Probably amortized O(m log(n/m + 1),
   where m <= n lengths of xs and ys -}
intersection :: (Ord a) => OrdSet a -> OrdSet a -> OrdSet a
intersection (OrdSet xs) (OrdSet ys) = OrdSet $ _intersection xs ys
  where
    _intersection Base.Empty _ = Base.Empty
    _intersection _ Base.Empty = Base.Empty
    _intersection as (b Base.:<| bs') =
      case r of
        Base.Empty -> Base.Empty
        x Base.:<| r' ->
          if x == b
            then b Base.:<| _intersection bs' r'
            else _intersection bs' r'
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as

{- Probably amortized O(m log(n/m + 1),
   where m <= n lengths of xs and ys -}
difference :: (Ord a) => OrdSet a -> OrdSet a -> OrdSet a
difference (OrdSet xs) (OrdSet ys) = OrdSet $ _difference xs ys
  where
    _difference Base.Empty _ = Base.Empty
    _difference as Base.Empty = as
    _difference as (b Base.:<| bs') =
      case r of
        Base.Empty -> l
        x Base.:<| r' ->
          if x == b
            then l Base.>< differenceRest
            else differenceRest
          where
            differenceRest = _differenceReversed bs' r'
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as
    _differenceReversed Base.Empty bs = bs
    _differenceReversed _ Base.Empty = Base.Empty
    _differenceReversed as bs@(b Base.:<| bs') =
      case r of
        Base.Empty -> bs
        x Base.:<| r' ->
          if x == b
            then differenceRest
            else b Base.:<| differenceRest
          where
            differenceRest = _difference bs' r'
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as

{- Probably amortized O(m log(n/m + 1),
   where m <= n lengths of xs and ys -}
isDisjointFrom :: (Ord a) => OrdSet a -> OrdSet a -> Bool
isDisjointFrom (OrdSet xs) (OrdSet ys) = _isDisjointFrom xs ys
  where
    _isDisjointFrom Base.Empty _ = True
    _isDisjointFrom _ Base.Empty = True
    _isDisjointFrom as (b Base.:<| bs') =
      case r of
        Base.Empty -> True
        x Base.:<| r' -> x /= b && _isDisjointFrom bs' r
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as

{- Probably amortized O(m log(n/m + 1),
   where m <= n lengths of xs and ys -}
isSubsetOf :: (Ord a) => OrdSet a -> OrdSet a -> Bool
isSubsetOf (OrdSet xs) (OrdSet ys) = _isSubsetOf xs ys
  where
    _isSubsetOf Base.Empty _ = True
    _isSubsetOf _ Base.Empty = False
    _isSubsetOf as bs@(b Base.:<| bs') =
      size' as <= size' bs && Base.null l && isSubsetRest
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as
        isSubsetRest =
          case r of
            Base.Empty -> True
            x Base.:<| r' ->
              if x == b
                then _isSupsetOf bs' r'
                else _isSupsetOf bs' r
    _isSupsetOf _ Base.Empty = True
    _isSupsetOf Base.Empty _ = False
    _isSupsetOf as bs@(b Base.:<| bs') = size' as >= size' bs && isSupsetRest
      where
        (l, r) = Base.split (onMax (<=) $ Base.measure b) as
        isSupsetRest =
          case r of
            Base.Empty -> False
            (x Base.:<| r') -> x == b && _isSubsetOf bs' r

{- Probably amortized O(m log(n/m + 1),
   where m <= n lengths of xs and ys -}
isSupsetOf :: (Ord a) => OrdSet a -> OrdSet a -> Bool
isSupsetOf = flip isSubsetOf

-- Order statistics
{- O(1) -}
smallestElem :: OrdSet a -> Maybe a
smallestElem (OrdSet xs) =
  case xs of
    Base.Empty -> Nothing
    (a Base.:<| _) -> Just $ getElem a

{- O(log(min(k, n-k))) -}
kthSmallestElem :: Integer -> OrdSet a -> Maybe a
kthSmallestElem k (OrdSet xs)
  | k < 1 = Nothing
  | otherwise = getElem <$> Base.lookup ((Size k <=) . getSize) xs

{- O(1) -}
largestElem :: OrdSet a -> Maybe a
largestElem (OrdSet xs) =
  case xs of
    Base.Empty -> Nothing
    (_ Base.:|> a) -> Just $ getElem a

{- O(log(min(k, n-k))) -}
kthLargestElem :: Integer -> OrdSet a -> Maybe a
kthLargestElem k xs = kthSmallestElem (size xs - k + 1) xs

-- Generalized functions
{- O(nlog(n)) -}
fromFoldable :: (Foldable f, Ord a) => f a -> OrdSet a
fromFoldable = foldr insert empty

{- O(n) -}
fromAscFoldable :: (Foldable f, Eq a) => f a -> OrdSet a
fromAscFoldable =
  OrdSet . fst . foldr _maybeInsertElemLeft (Base.empty, Nothing)
  where
    _maybeInsertElemLeft a (_, Nothing) = (Base.singleton $ Elem a, Just a)
    _maybeInsertElemLeft a acc@(xs, Just lastA) =
      if a == lastA
        then acc
        else (Elem a Base.:<| xs, Just a)

{- O(n) -}
fromDescFoldable :: (Foldable f, Eq a) => f a -> OrdSet a
fromDescFoldable =
  OrdSet . fst . foldr _maybeInsertElemRight (Base.empty, Nothing)
  where
    _maybeInsertElemRight a (_, Nothing) = (Base.singleton $ Elem a, Just a)
    _maybeInsertElemRight a acc@(xs, Just lastA) =
      if a == lastA
        then acc
        else (xs Base.:|> Elem a, Just a)

{- O(n) -}
fromDistinctAscFoldable :: Foldable f => f a -> OrdSet a
fromDistinctAscFoldable = OrdSet . foldr _insertElemLeft Base.empty
  where
    _insertElemLeft a xs = Elem a Base.:<| xs

{- O(n) -}
fromDistinctDescFoldable :: Foldable f => f a -> OrdSet a
fromDistinctDescFoldable = OrdSet . foldr _insertElemRight Base.empty
  where
    _insertElemRight a xs = xs Base.:|> Elem a

-- Helper functions
size' :: forall a. Base.FingerTree (SizeMax a) (Elem a) -> Integer
size' xs =
  let meas = Base.measure xs :: SizeMax a
   in unSize . getSize $ meas

getSize :: SizeMax a -> Size
getSize = fst . unSizeMax

getMax :: SizeMax a -> Max a
getMax = snd . unSizeMax

onSize :: (Size -> Size -> b) -> SizeMax a -> SizeMax a -> b
onSize f (SizeMax (x, _)) (SizeMax (y, _)) = f x y

onMax :: (Max a -> Max a -> b) -> SizeMax a -> SizeMax a -> b
onMax f (SizeMax (_, x)) (SizeMax (_, y)) = f x y
