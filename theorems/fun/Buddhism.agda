open import HoTT

-- See Appendix B of favonia's thesis.

module fun.Buddhism {i} {Obj : Type i} where

  concept : ∀ j → Type (lmax i (lsucc j))
  concept j = Obj → Type j

  is-non-dual : ∀ {j} (P : concept j) → Type (lmax i (lsucc j))
  is-non-dual P = ∀ o₁ o₂ → P o₁ == P o₂

  all-non-dual-implies-all-paths : ((P : concept i) → is-non-dual P) → has-all-paths Obj
  all-non-dual-implies-all-paths nd o₁ o₂ = coe (nd (λ o₂ → o₁ == o₂) o₁ o₂) idp

  all-paths-implies-non-dual : ∀ {j} → has-all-paths Obj → ((P : concept j) → is-non-dual P)
  all-paths-implies-non-dual allpath P o₁ o₂ = ap P (allpath o₁ o₂)
