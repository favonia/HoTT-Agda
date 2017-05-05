{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module _ {i} where

Skeleton : ℕ → Type (lsucc i)
Realizer : {n : ℕ} → Skeleton n → Type i

record AttachedSkeleton (n : ℕ) : Type (lsucc i) where
  inductive
  constructor attached-skeleton
  field
    skel : Skeleton n
    cells : hSet i
    attaching : fst cells → Sphere n → Realizer skel

Skeleton O = Σ (Type i) is-set
Skeleton (S n) = AttachedSkeleton n

Realizer {n = O} A = fst A
Realizer {n = S n} (attached-skeleton skel cells α) =
  Pushout (span
    (Realizer skel) (fst cells) (fst cells × Sphere n)
    (uncurry α) fst)

cw-init : ∀ {n} → Skeleton (S n) → Skeleton n
cw-init (attached-skeleton skel _ _) = skel

cw-incl-last : ∀ {n} (skel : Skeleton (S n))
  → (Realizer (cw-init skel) → Realizer skel)
cw-incl-last (attached-skeleton _ _ _) = left
