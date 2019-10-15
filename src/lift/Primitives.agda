{-# OPTIONS --allow-unsolved-metas #-} 
{- TODO: remove the pragma when all the holes are filled -}
module lift.Primitives where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribˡ-+; *-identityʳ)
  open import Function using (_∘_)

  {- lemmas -}
  zero-mul : ∀ (m : ℕ) → m * zero ≡ zero
  zero-mul zero = refl
  zero-mul (suc m) = zero-mul m

  empty-vecʳ : (m : ℕ) → {t : Set} → Vec t (zero * m) ≡ Vec t zero
  empty-vecʳ zero {t} = refl
  empty-vecʳ (suc m) {t} = empty-vecʳ m {t}

  empty-vecˡ : (m : ℕ) → {t : Set} → Vec t (m * zero) ≡ Vec t zero
  empty-vecˡ zero {t} = refl
  empty-vecˡ (suc m) {t} = empty-vecˡ m {t}

  distrib-suc : (m : ℕ) → (n : ℕ) → n * (suc m) ≡ n + n * m
  distrib-suc m n =
    begin
       n * (suc m)
     ≡⟨⟩
       n * (1 + m)
     ≡⟨ *-distribˡ-+ n 1 m ⟩
       n * 1 + n * m
     ≡⟨ cong (_+ n * m) (*-identityʳ n)⟩
       n + n * m
     ∎

  {- primitive map -}
  map : {n : ℕ} -> {s : Set} -> {t : Set} -> (s -> t) -> Vec s n → Vec t n
  map {.0} {s} {t} f [] = []
  map {.(suc _)} {s} {t} f (x ∷ xs) = (f x) ∷ (map f xs)

  {- primitive id -}
  id : {T : Set} → T → T
  id t = t

  {- primitive split -}
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
  split zero {zero} [] = []
  split zero {suc m} [] = [] ∷ split zero {m} []
  split (suc n) {zero} xs = []
  -- TODO
  split (suc n) {suc m} xs = {!!}

  {- primitive join -}
  join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (n * m)
  -- join [] = []
  -- join (xs ∷ xs₁) = xs ++ join xs₁
  -- join {n} [] rewrite zero-mul n = []
  join {n} {zero} [] rewrite *-comm n zero = []
  -- TODO
  join {n} {suc m} (xs ∷ xs₁) = {!!}
