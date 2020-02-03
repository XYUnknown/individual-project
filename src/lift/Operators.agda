{-# OPTIONS --without-K --safe #-}
module lift.Operators where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Data.Vec
  import Data.Nat.Properties as ℕ▯

  record CommAssocMonoid (A : Set) : Set₁ where
    field
      ε     : A
      _⊕_   : A → A → A
      idˡ   : ∀ x → ε ⊕ x ≡ x
      idʳ   : ∀ x → x ⊕ ε ≡ x
      assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
      comm  : ∀ x y → x ⊕ y ≡ y ⊕ x
  open CommAssocMonoid

  ADDITION : CommAssocMonoid ℕ
  ε ADDITION = 0
  _⊕_ ADDITION = _+_
  idˡ ADDITION = ℕ▯.+-identityˡ
  idʳ ADDITION = ℕ▯.+-identityʳ
  assoc ADDITION = ℕ▯.+-assoc
  comm ADDITION = ℕ▯.+-comm

  MULTIPLICATION : CommAssocMonoid ℕ
  ε MULTIPLICATION = 1
  _⊕_ MULTIPLICATION = _*_
  idˡ MULTIPLICATION = ℕ▯.*-identityˡ
  idʳ MULTIPLICATION = ℕ▯.*-identityʳ
  assoc MULTIPLICATION = ℕ▯.*-assoc
  comm MULTIPLICATION = ℕ▯.*-comm

  foobar : ∀ {n} (M : CommAssocMonoid ℕ) (xs : Vec ℕ n)
           → let _⊕_ = _⊕_ M; ε = ε M in
           map (λ x → x ⊕ ε) xs ≡ xs
  foobar M [] = refl
  foobar M (x ∷ xs) = cong₂ _∷_ (idʳ M x) (foobar M xs)

