module lift.Primitives where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)

  {- primitive map -}
  map : {n : ℕ} -> {s : Set} -> {t : Set} -> (s -> t) -> Vec s n → Vec t n
  map {.0} {s} {t} f [] = []
  map {.(suc _)} {s} {t} f (x ∷ xs) = (f x) ∷ (map f xs)

  {- primitive id -}
  id : {T : Set} → T → T
  id t = t

  {- lemma 1 -}
  zero-mul : ∀ (m : ℕ) → m * zero ≡ zero
  zero-mul zero =  refl
  zero-mul (suc m) = zero-mul m

  {- lemma 2 -}
  empty-vecʳ : (m : ℕ) → {t : Set} → Vec t (zero * m) ≡ Vec t zero
  empty-vecʳ zero {t} =  refl
  empty-vecʳ (suc m) {t} = empty-vecʳ m {t}

  {- lemma 3-}
  empty-vecˡ : (m : ℕ) → {t : Set} → Vec t (m * zero) ≡ Vec t zero
  empty-vecˡ zero {t} =  refl
  empty-vecˡ (suc m) {t} =  empty-vecˡ m {t}

  {- primitive split -}
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
  split zero {zero} {t} [] = []
  split zero {suc m} {t} [] = [] ∷ (split zero {m} {t} [])
  split (suc n) {zero} {t} _ = []
  -- TODO
  split (suc n) {suc m} {t} xs = {!!}

  {- primitive join -}
  join : {m n : ℕ} → {t : Set} → Vec (Vec t m) n → Vec t (n * m)
  join {m} {.0} {t} [] = []
  join {m} {.(suc _)} {t} (xs ∷ xs₁) =  xs ++ join xs₁
