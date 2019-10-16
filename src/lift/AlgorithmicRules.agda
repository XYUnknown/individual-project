{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
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
  map-id [] = refl
  map-id (x ∷ xs) =
    begin
      Pm.map Pm.id (x ∷ xs)
    ≡⟨⟩
      x ∷ (Pm.map Pm.id xs)
    ≡⟨ cong (x ∷_) (map-id xs) ⟩
      x ∷ xs
    ∎

  map-split : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
              Pm.map (Pm.map f) (Pm.split n xs) ≡ Pm.split n ( Pm.map f xs)
  -- TODO
  map-split = {!!}

  join-split : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n * m)) →
               Pm.join (Pm.split n xs) ≡ xs
  -- TODO
  join-split = {!!}

  {- identity rules -}
  identity₁ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n -> Vec t n) → (xs : Vec s n) → (f ∘ Pm.map Pm.id) xs ≡ f xs
  identity₁ f xs =
    begin
      (f ∘ Pm.map Pm.id) xs
    ≡⟨⟩
      f (Pm.map Pm.id xs)
    ≡⟨ cong f (map-id xs) ⟩
      f xs
    ∎

  identity₂ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n -> Vec t n) → (xs : Vec s n) → (Pm.map Pm.id ∘ f) xs ≡ f xs
  identity₂ f xs =
    begin
      (Pm.map Pm.id ∘ f) xs
    ≡⟨⟩
      Pm.map Pm.id (f xs)
    ≡⟨ map-id (f xs) ⟩
      f xs
    ∎

  {- split-join rule -}
  splitJoin : {m : ℕ} → {s : Set} → {t : Set} →
              (n : ℕ) → (f : s → t) → (xs : Vec s (n * m)) →
              (Pm.join ∘ Pm.map (Pm.map f) ∘ Pm.split n) xs ≡ Pm.map f xs
  splitJoin n f xs =
    begin
      (Pm.join ∘ Pm.map (Pm.map f) ∘ Pm.split n) xs
    ≡⟨⟩
      Pm.join (Pm.map (Pm.map f) (Pm.split n xs))
    ≡⟨ cong Pm.join (map-split n f xs) ⟩
      Pm.join (Pm.split n (Pm.map f xs))
    ≡⟨ join-split n (Pm.map f xs) ⟩
      Pm.map f xs
    ∎