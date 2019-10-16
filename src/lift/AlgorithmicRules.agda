{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
module lift.AlgorithmicRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+; *-identityʳ; *-identityˡ; +-assoc)
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

  -- TODO
  {- I assume this need to be proven -}
  map-splitAt : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
                ∃₂ λ (xs₁ : Vec s n) (xs₂ : Vec s m) → xs ≡ xs₁ ++ xs₂ → Pm.map f xs ≡ Pm.map f xs₁ ++ Pm.map f xs₂
  map-splitAt zero f xs = {!!}
  map-splitAt (suc n) f (x ∷ xs) = {!!}

  --TODO
  {- I assume proving map-take and map-drop reuires map-splitAt -}
  map-take : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             Pm.map f (Pm.take n xs) ≡ (Pm.take n (Pm.map f xs))
  map-take n f xs = {!!}

  map-drop : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             Pm.map f (Pm.drop n xs) ≡ (Pm.drop n (Pm.map f xs ))
  map-drop n f xs = {!!}

  {- proving this lemma requires proving map-drop and map-take -}
  map-split : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
              Pm.map (Pm.map f) (Pm.split n xs) ≡ Pm.split n (Pm.map f xs)

  map-split n {zero} f xs = refl
  map-split n {suc m} f xs rewrite distrib-suc m n =
    begin
      Pm.map f (Pm.take n xs) ∷ Pm.map (Pm.map f) (Pm.split n (Pm.drop n xs))
    ≡⟨ cong ( Pm.map f (Pm.take n xs) ∷_) (map-split n f (Pm.drop n xs)) ⟩
      Pm.map f (Pm.take n xs) ∷ Pm.split n (Pm.map f (Pm.drop n xs))
    ≡⟨ cong (_∷ Pm.split n (Pm.map f (Pm.drop n xs))) (map-take n f xs) ⟩
      Pm.take n (Pm.map f xs) ∷ Pm.split n (Pm.map f (Pm.drop n xs))
    ≡⟨ cong (Pm.take n (Pm.map f xs) ∷_) (cong (Pm.split n) (map-drop n f xs)) ⟩
      Pm.take n (Pm.map f xs) ∷ Pm.split n (Pm.drop n (Pm.map f xs))
    ∎

  {- this is weird, basically it required me explicitly reasoning about Vec t zero is [] -}
  empty : {t : Set} → (xs : Vec t zero) → xs ≡ []
  empty [] = refl

  join-split : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n * m)) →
               Pm.join (Pm.split n xs) ≡ xs
  join-split n {zero} {t} xs rewrite *-comm n zero =
    begin
      []
    ≡⟨ sym (empty xs) ⟩
      xs
    ∎

  -- TODO
  -- the rewrite used in proving primitives makes this become difficult
  join-split n {suc m} xs = {!!}

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

  {- Fusion rules -}
  fusion₁ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} → (f : t → r) → (g : s → t) → (xs : Vec s n) →
            (Pm.map f ∘ Pm.map g) xs ≡ Pm.map (f ∘ g) xs
  fusion₁ f g [] =
    begin
      (Pm.map f ∘ Pm.map g) []
    ≡⟨⟩
      Pm.map f (Pm.map g [])
    ≡⟨⟩
      Pm.map f []
    ≡⟨⟩
      []
    ≡⟨⟩
      Pm.map (f ∘ g) []
    ∎
  fusion₁ f g (x ∷ xs) =
    begin
      (Pm.map f ∘ Pm.map g) (x ∷ xs)
    ≡⟨⟩
      Pm.map f (Pm.map g (x ∷ xs))
    ≡⟨⟩
      Pm.map f (g x ∷ Pm.map g xs)
    ≡⟨⟩
      f (g x) ∷ Pm.map f (Pm.map g xs)
    ≡⟨⟩
      (f ∘ g) x ∷ Pm.map f (Pm.map g xs)
    ≡⟨ cong ((f ∘ g) x ∷_ ) (fusion₁ f g xs) ⟩
      (f ∘ g) x ∷ Pm.map (f ∘ g) xs
    ∎
