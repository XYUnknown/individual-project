{-# OPTIONS --allow-unsolved-metas #-} 
module lift.AlgorithmicRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)
  import lift.Primitives as Pm
  open Pm


  {- lemmas -}
  map-id : {n : ℕ} → {s : Set} → (xs : Vec s n ) → Pm.map Pm.id xs ≡ xs
  map-id [] =  refl
  map-id (x ∷ xs) =
    begin
      Pm.map Pm.id (x ∷ xs)
    ≡⟨⟩
      x ∷ (Pm.map Pm.id xs)
    ≡⟨ cong (x ∷_) (map-id xs) ⟩
      x ∷ xs
    ∎

  {- identity rule -}
  identity : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n -> Vec t n) → (xs : Vec s n) → (f ∘ Pm.map Pm.id) xs ≡ f xs
  identity {n} {s} {t} f xs =
    begin
      (f ∘ Pm.map Pm.id) xs
    ≡⟨⟩
      f (Pm.map Pm.id xs)
    ≡⟨ cong f (map-id xs) ⟩
      f xs
    ∎
