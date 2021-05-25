{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{- An implementation of Finger Trees following
   http://www.staff.city.ac.uk/~ross/papers/FingerTree.pdf -}
module FingerTree
  ( FingerTree (Empty, (:<|), (:|>)),
    Measured (..), -- pulled up from HelperTypes
    empty,
    singleton,
    null,
    (><),
    fromFoldable,
    split,
    lookup,
  )
where

import HelperTypes
import Prelude hiding (lookup, null)

data FingerTree v a
  = Empty
  | Shallow a
  | Deep v (Digit a) (FingerTree v (Node v a)) (Digit a)
  deriving (Eq, Show)

data ViewL s a
  = NilL
  | ConsL a (s a)
  deriving (Eq, Show)

data ViewR s a
  = NilR
  | ConsR (s a) a
  deriving (Eq, Show)

instance (Measured a v) => Measured (FingerTree v a) v where
  measure Empty = mempty
  measure (Shallow a) = measure a
  measure (Deep v _ _ _) = v

instance Foldable (FingerTree v) where
  foldr _ z Empty = z
  foldr f z (Shallow a) = f a z
  foldr f z (Deep _ a b c) = foldr f (foldr f' (foldr f z c) b) a
    where
      f' = flip $ foldr f

  --f'' = flip $ foldr f'
  foldl _ z Empty = z
  foldl f z (Shallow a) = f z a
  foldl f z (Deep _ c b a) = foldl f (foldl f' (foldl f z c) b) a
    where
      f' = foldl f

empty :: FingerTree v a
empty = Empty

singleton :: (Measured a v) => a -> FingerTree v a
singleton = Shallow

{- O(1) -}
null :: FingerTree v a -> Bool
null Empty = True
null _ = False

{- Bidirectional pattern. See viewL and <| -}
infixr 5 :<|

pattern (:<|) ::
  (Measured a v) =>
  a ->
  FingerTree v a ->
  FingerTree v a
pattern x :<| xs <-
  (viewL -> ConsL x xs)
  where
    x :<| xs = x <| xs

{- Bidirectional pattern. See viewR and |> -}
infixl 5 :|>

pattern (:|>) ::
  (Measured a v) =>
  FingerTree v a ->
  a ->
  FingerTree v a
pattern xs :|> x <-
  (viewR -> ConsR xs x)
  where
    xs :|> x = xs |> x

{-# COMPLETE (:<|), Empty #-}

{-# COMPLETE (:|>), Empty #-}

{- O(1) amortized / O(log(n)) worst case -}
infixr 5 <|

(<|) :: (Measured a v) => a -> FingerTree v a -> FingerTree v a
a <| Empty = Shallow a
a <| Shallow b = deep (One a) Empty (One b)
a <| Deep _ (Two b c) Empty (One d) = deep (Two a b) Empty (Two c d) -- only to ensure some balancing
a <| Deep _ (Four b c d e) mid rear = deep (Two a b) (node3 c d e :<| mid) rear
a <| Deep _ front mid rear = deep (incrL a front) mid rear

{- O(1) amortized / O(log(n)) worst case -}
infixl 5 |>

(|>) :: (Measured a v) => FingerTree v a -> a -> FingerTree v a
Empty |> a = Shallow a
Shallow b |> a = deep (One b) Empty (One a)
Deep _ (One a) Empty (Two b c) |> d = deep (Two a b) Empty (Two c d) -- only to ensure some balancing
Deep _ front mid (Four e d c b) |> a =
  deep front (mid :|> node3 e d c) (Two b a)
Deep _ front mid rear |> a = deep front mid (incrR rear a)

{- O(log(m)) catenation,
   where m <= n lengths of xs and ys -}
infixr 5 ><

(><) :: (Measured a v) => FingerTree v a -> FingerTree v a -> FingerTree v a
xs >< ys = append xs Nothing ys

fromFoldable :: (Foldable f, Measured a v) => f a -> FingerTree v a
fromFoldable = foldr (:<|) Empty

{- Enables O(1) worst case time to the head and
   O(1) amortized / O(log(n)) worst case to the tail -}
viewL :: (Measured a v) => FingerTree v a -> ViewL (FingerTree v) a
viewL Empty = NilL
viewL (Shallow a) = ConsL a Empty
viewL (Deep _ (One f) mid rear) = ConsL f $ deepL mid rear
viewL (Deep _ digit mid rear) =
  let (f, fs) = decrL digit
   in ConsL f $ deep fs mid rear

{- Enables O(1) worst case time to the last and
   O(1) amortized / O(log(n)) worst case to the init -}
viewR :: (Measured a v) => FingerTree v a -> ViewR (FingerTree v) a
viewR Empty = NilR
viewR (Shallow a) = ConsR Empty a
viewR (Deep _ front mid (One r)) = ConsR (deepR front mid) r
viewR (Deep _ front mid digit) =
  let (rs, r) = decrR digit
   in ConsR (deep front mid rs) r

append ::
  (Measured a v) =>
  FingerTree v a ->
  Maybe (Digit a) ->
  FingerTree v a ->
  FingerTree v a
append Empty Nothing xs = xs
append xs Nothing Empty = xs
append Empty (Just x) xs = foldr (:<|) xs x
append xs (Just x) Empty = foldl (:|>) xs x
append (Shallow y) x xs = y :<| append Empty x xs
append xs x (Shallow y) = append xs x Empty :|> y
append (Deep _ front1 mid1 rear1) x (Deep _ front2 mid2 rear2) =
  let mergedMiddle = Just (mergeDigits rear1 x front2)
   in deep front1 (append mid1 mergedMiddle mid2) rear2

-- Several convenience methods for efficiently constructing FTs
deep ::
  (Measured a v) =>
  Digit a ->
  FingerTree v (Node v a) ->
  Digit a ->
  FingerTree v a
deep front mid rear =
  Deep (measure front <> measure mid <> measure rear) front mid rear

deepL :: (Measured a v) => FingerTree v (Node v a) -> Digit a -> FingerTree v a
deepL mid rear =
  case viewL mid of
    NilL -> digitToTree rear
    ConsL m ms -> deep (unpackNode m) ms rear

deepR :: (Measured a v) => Digit a -> FingerTree v (Node v a) -> FingerTree v a
deepR front mid =
  case viewR mid of
    NilR -> digitToTree front
    ConsR ms m -> deep front ms (unpackNode m)

digitToTree :: (Measured a v) => Digit a -> FingerTree v a
digitToTree (One a) = Shallow a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

digitPairToTree :: (Measured a v) => Digit a -> Digit a -> FingerTree v a
digitPairToTree x@(One _) y@(One _) = deep x Empty y
digitPairToTree x@(One _) y@(Two _ _) = deep x Empty y
digitPairToTree (One a) (Three b c d) = deep (Two a b) Empty (Two c d)
digitPairToTree (One a) (Four b c d e) = deep (Three a b c) Empty (Two d e)
digitPairToTree x@(Two _ _) y@(One _) = deep x Empty y
digitPairToTree x@(Two _ _) y@(Two _ _) = deep x Empty y
digitPairToTree x@(Two _ _) y@Three {} = deep x Empty y
digitPairToTree (Two a b) (Four c d e f) =
  deep (Three a b c) Empty (Three d e f)
digitPairToTree (Three a b c) (One d) = deep (Two a b) Empty (Two c d)
digitPairToTree x@Three {} y@(Two _ _) = deep x Empty y
digitPairToTree x@Three {} y@Three {} = deep x Empty y
digitPairToTree (Three a b c) (Four d e f g) =
  deep (Two a b) (Shallow (node3 c d e)) (Two f g)
digitPairToTree (Four a b c d) (One e) = deep (Two a b) Empty (Three c d e)
digitPairToTree (Four a b c d) (Two e f) =
  deep (Three a b c) Empty (Three d e f)
digitPairToTree (Four a b c d) (Three e f g) =
  deep (Two a b) (Shallow (node3 c d e)) (Two f g)
digitPairToTree (Four a b c d) (Four e f g h) =
  deep (Three a b c) (Shallow (node2 d e)) (Three f g h)

{- O(log(i)), where i <= n/2 is distance from
   split point to nearest end -}
split ::
  (Measured a v) =>
  (v -> Bool) ->
  FingerTree v a ->
  (FingerTree v a, FingerTree v a)
split _ Empty = (Empty, Empty)
split p xs
  | p (measure xs) =
    case splitTree p mempty xs of
      Single _ -> (Empty, xs)
      First _ _ -> (Empty, xs)
      Middle left a right -> (left, a :<| right)
      Last left a -> (left, Shallow a)
  | otherwise = (xs, Empty)

{- O(log(i)), where i <= n/2 is distance from
   lookup point to nearest end -}
lookup :: (Measured a v) => (v -> Bool) -> FingerTree v a -> Maybe a
lookup _ Empty = Nothing
lookup p tree =
  let LookUp (v, a) = lookupTree p mempty tree
   in if p (v <> measure a)
        then Just a
        else Nothing

-- Fairly ugly function, since we have so many cases,
-- but each case is straight-forward
splitTree ::
  (Measured a v) =>
  (v -> Bool) ->
  v ->
  FingerTree v a ->
  Split (FingerTree v) a
splitTree _ _ Empty = error "Empty Tree at FingerTree.splitTree"
splitTree _ _ (Shallow a) = Single a
splitTree p i (Deep _ front mid rear)
  | p ifront =
    case splitDigit p i front of
      Single a -> First a (deepL mid rear)
      First a fRight -> First a (deep fRight mid rear)
      Middle fLeft a fRight ->
        Middle (digitToTree fLeft) a (deep fRight mid rear)
      Last fLeft a -> Middle (digitToTree fLeft) a (deepL mid rear)
  | p ifrontmid =
    case splitTree p ifront mid of
      Single nodeA ->
        case splitDigit p ifront (unpackNode nodeA) of
          Single _ ->
            error
              "Single returned from splitDigit . unpackNode in FingerTree.splitTree"
          First a nRight ->
            Middle (digitToTree front) a (digitPairToTree nRight rear)
          Middle nLeft a nRight ->
            Middle (digitPairToTree front nLeft) a (digitPairToTree nRight rear)
          Last nLeft a ->
            Middle (digitPairToTree front nLeft) a (digitToTree rear)
      First nodeA mRight ->
        case splitDigit p ifront (unpackNode nodeA) of
          Single _ ->
            error
              "Single returned from splitDigit . unpackNode in FingerTree.splitTree"
          First a nRight ->
            Middle (digitToTree front) a (deep nRight mRight rear)
          Middle nLeft a nRight ->
            Middle (digitPairToTree front nLeft) a (deep nRight mRight rear)
          Last nLeft a ->
            Middle (digitPairToTree front nLeft) a (deepL mRight rear)
      Middle mLeft nodeA mRight ->
        case splitDigit p (ifront <> measure mLeft) (unpackNode nodeA) of
          Single _ ->
            error
              "Single returned from splitDigit . unpackNode in FingerTree.splitTree"
          First a nRight ->
            Middle (deepR front mLeft) a (deep nRight mRight rear)
          Middle nLeft a nRight ->
            Middle (deep front mLeft nLeft) a (deep nRight mRight rear)
          Last nLeft a -> Middle (deep front mLeft nLeft) a (deepL mRight rear)
      Last mLeft nodeA ->
        case splitDigit p (ifront <> measure mLeft) (unpackNode nodeA) of
          Single _ ->
            error
              "Single returned from splitDigit . unpackNode in FingerTree.splitTree"
          First a nRight ->
            Middle (deepR front mLeft) a (digitPairToTree nRight rear)
          Middle nLeft a nRight ->
            Middle (deep front mLeft nLeft) a (digitPairToTree nRight rear)
          Last nLeft a -> Middle (deep front mLeft nLeft) a (digitToTree rear)
  | otherwise =
    case splitDigit p ifrontmid rear of
      Single a -> Last (deepR front mid) a
      First a rRight -> Middle (deepR front mid) a (digitToTree rRight)
      Middle rLeft a rRight ->
        Middle (deep front mid rLeft) a (digitToTree rRight)
      Last rLeft a -> Last (deep front mid rLeft) a
  where
    ifront = i <> measure front
    ifrontmid = ifront <> measure mid

lookupTree :: (Measured a v) => (v -> Bool) -> v -> FingerTree v a -> LookUp v a
lookupTree _ _ Empty = error "Empty Tree at FingerTree.lookupTree"
lookupTree _ i (Shallow a) = LookUp (i, a)
lookupTree p i (Deep _ front mid rear)
  | p ifront = lookupDigit p i front
  | p ifrontmid =
    let LookUp (i', nodeA) = lookupTree p ifront mid
     in lookupNode p i' nodeA
  | otherwise = lookupDigit p ifrontmid rear
  where
    ifront = i <> measure front
    ifrontmid = ifront <> measure mid
