-- {-@ LIQUID "--ple" @-}
module Ack where
import Language.Haskell.Liquid.ProofCombinators

{-@ (=>>) :: x:a -> {y:a | x > y } -> {v:a| v = y} @-}
(=>>) :: a -> a -> a
(=>>) _ y = y
infixl 3 =>>

{-@ reflect ack @-}
{-@ ack :: m:Nat -> n:Nat -> Nat / [m,n] @-}
ack :: Int -> Int -> Int
ack 0 n = n + 1
ack m 0 = ack (m-1) 1
ack m n = ack (m-1) (ack m (n-1))

{-@ ack_gt_snd :: m:Nat -> n:Nat -> {ack m n > n} / [m,n] @-}
ack_gt_snd :: Int -> Int -> Proof
ack_gt_snd 0 n = -- ()
  ack 0 n *** QED
ack_gt_snd m 0 = -- ack_gt_snd (m - 1) 1
  ack m 0 === ack (m-1) 1 ? ack_gt_snd (m - 1) 1 =>> 1 =>> 0 *** QED
ack_gt_snd m n = -- ack_gt_snd (m - 1) (ack m (n-1)) ? ack_gt_snd m (n-1)
      ack m n
  === ack (m-1) (ack m (n-1))
    ? ack_gt_snd (m - 1) (ack m (n-1))
  =>> ack m (n-1)
    ? ack_gt_snd m (n-1)
  =>= n
  *** QED

{-@ ack_snd_plus_one :: m:Nat -> n:Nat -> {ack m (n+1) > ack m n} @-}
ack_snd_plus_one 0 n =
  ack 0 (n+1) =>> ack 0 n *** QED
ack_snd_plus_one m n =
      ack m (n+1)
  === ack (m-1) (ack m n)
    ? ack_gt_snd (m-1) (ack m n)
  =>> ack m n
  *** QED

{-@ ack_mon_snd :: m:Nat -> n:Nat -> {p:Nat|n>p} -> {ack m n > ack m p} /[n] @-}
ack_mon_snd m n p
  | n == p + 1 = ack_snd_plus_one m p
  | otherwise  =
      ack m n ? ack_snd_plus_one m (n-1)
  =>> ack m (n-1)
    ? ack_mon_snd m (n-1) p
  =>> ack m p
  *** QED

{-@ ack_mon_eq_snd :: m:Nat -> n:Nat -> {p:Nat | n >= p} -> {ack m n >= ack m p} @-}
ack_mon_eq_snd m n p
  | n == p = ack m n *** QED
  | otherwise = ack_mon_snd m n p

{-@ ack_plus_one_fst_snd :: m:Nat -> n:Nat -> {ack (m+1) n >= ack m (n+1)} /[n] @-}
ack_plus_one_fst_snd :: Int -> Int -> Proof
ack_plus_one_fst_snd m 0 = ack (m+1) 0 === ack m 1 *** QED
ack_plus_one_fst_snd m n =
      ack (m+1) n
  === ack m (ack (m+1) (n-1))
    ? ack_plus_one_fst_snd m (n-1)
    ? ack_mon_eq_snd m (ack (m+1) (n-1)) (ack m n)
  =>= ack m (ack m n)
    ? ack_gt_snd m n
    ? ack_mon_eq_snd m (ack m n) (n+1)
  =>= ack m (n+1)
  *** QED

{-@ ack_geq_sum :: m:Nat -> n:Nat -> {ack m n >= m + n + 1} @-}
ack_geq_sum :: Int -> Int -> Proof
ack_geq_sum 0 n = ack 0 n *** QED
ack_geq_sum m n =
      ack m n
    ? ack_plus_one_fst_snd (m-1) n
  =>= ack (m-1) (n+1)
    ? ack_geq_sum (m-1) (n+1)
  *** QED

{-@ ack_mon_fst :: m:Nat -> n:Nat -> {p:Nat | m > p} -> {ack m n >= ack p n} @-}
ack_mon_fst :: Int -> Int -> Int -> Proof
ack_mon_fst m n p
  | m == p + 1 =
      ack (p+1) n
    ? ack_plus_one_fst_snd p n
  =>= ack p (n+1)
    ? ack_mon_snd p (n+1) n
  =>= ack p n
  *** QED
  | otherwise =
      ack m n
    ? ack_plus_one_fst_snd (m-1) n
  =>= ack (m-1) (n+1)
    ? ack_mon_snd (m-1) (n+1) n
  =>= ack (m-1) n
    ? ack_mon_fst (m-1) n p
  =>= ack p n
  *** QED

{-@ ack_fst_plus_two :: m:Nat -> n:Nat -> {ack (m+2) n > ack m (2*n)} / [n] @-}
ack_fst_plus_two :: Int -> Int -> Proof
ack_fst_plus_two m 0 =
      ack (m+2) 0
  === ack (m+1) 1
  === ack m (ack (m+1) 0)
  === ack m (ack m 1)
    ? ack_gt_snd m (ack m 1)
  =>> ack m 1
    ? ack_mon_snd m 1 0
  =>> ack m 0
  *** QED
ack_fst_plus_two m n =
      ack (m+2) n
  === ack (m+1) (ack (m+2) (n-1))
    ? ack_fst_plus_two m (n-1)
    ? ack_mon_snd (m+1) (ack (m+2) (n-1)) (ack m (2*n - 2))
  =>> ack (m+1) (ack m (2*n -2))
    ? ack_geq_sum m (2*n - 2)
    ? ack_mon_eq_snd (m+1) (ack m (2*n -2)) (m + 2*n -1)
  =>= ack (m+1) (m + 2 * n - 1)
    ? ack_mon_eq_snd (m+1) (m + 2*n -1) (2*n -1)
  =>= ack (m+1) (2 * n - 1)
    ? ack_plus_one_fst_snd m (2*n - 1)
  =>= ack m (2*n)
  *** QED
{- HLINT ignore -}
