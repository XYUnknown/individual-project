{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.MovementRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (*-distribʳ-+)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)
  import lift.Primitives as Pm
  open Pm
  open import lift.Helpers

  {- lemmas -}
  map-fill-empty : {s t : Set} → (m : ℕ) → (f : s → t) →
                   Pm.map (Pm.map f) (Pm.fill m []) ≡ Pm.fill m []
  map-fill-empty zero f = refl
  map-fill-empty (suc m) f =
    begin
      [] ∷ Pm.map (Pm.map f) (Pm.fill m [])
    ≡⟨ cong ([] ∷_) (map-fill-empty m f) ⟩
      refl

  {- rules -}
  {- Transpose -}
  mapMapFBeforeTranspose : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s m) n) →
                           Pm.map (Pm.map f) (Pm.transpose xss) ≡ Pm.transpose (Pm.map (Pm.map f) xss)
  mapMapFBeforeTranspose {zero} {m} f [] =
    begin
      Pm.map (Pm.map f) (Pm.fill m [])
    ≡⟨ map-fill-empty m f ⟩
      refl
  mapMapFBeforeTranspose {suc n} {zero} f xss = refl
  mapMapFBeforeTranspose {suc n} {suc m} f ((x ∷ xs) ∷ xss) =
    begin
      (f x ∷ Pm.map f (Pm.map Pm.head xss)) ∷
      Pm.map (Pm.map f) (Pm.transpose (xs ∷ Pm.map Pm.tail xss))
    ≡⟨ cong ((f x ∷ Pm.map f (Pm.map Pm.head xss)) ∷_) (mapMapFBeforeTranspose f (xs ∷ Pm.map Pm.tail xss)) ⟩
      (f x ∷ Pm.map f (Pm.map Pm.head xss)) ∷
      Pm.transpose (Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map tail xss))
    ≡⟨ cong (_∷ Pm.transpose (Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map tail xss)))
       (cong (f x ∷_) (map-head f xss)) ⟩
      (f x ∷ Pm.map head (Pm.map (Pm.map f) xss)) ∷
      Pm.transpose (Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map Pm.tail xss))
    ≡⟨ cong (λ yss → (f x ∷ Pm.map head (Pm.map (Pm.map f) xss)) ∷
       Pm.transpose (Pm.map f xs ∷ yss)) (map-tail f xss) ⟩
      refl

  {- Slide -}
  slideBeforeMapMapF : {n : ℕ} → (sz : ℕ) → (sp : ℕ) → {s t : Set} →
                       (f : s → t) → (xs : Vec s (sz + n * (suc sp))) →
                       Pm.map (Pm.map f) (Pm.slide {n} sz sp xs) ≡ Pm.slide {n} sz sp (Pm.map f xs)
  slideBeforeMapMapF {zero} sz sp f xs = refl
  slideBeforeMapMapF {suc n} sz sp f xs =
    begin
      Pm.map f (take sz xs) ∷
      Pm.map (Pm.map f) (Pm.slide {n} sz sp (Pm.drop (suc sp) xs))
    ≡⟨ cong (_∷ Pm.map (Pm.map f) (Pm.slide {n} sz sp (Pm.drop (suc sp) xs))) (map-take sz f xs) ⟩
      Pm.take sz (Pm.map f xs) ∷
      Pm.map (Pm.map f) (Pm.slide sz sp (Pm.drop (suc sp) xs))
    ≡⟨ cong (Pm.take sz (Pm.map f xs) ∷_) (slideBeforeMapMapF {n} sz sp f (Pm.drop (suc sp) xs))⟩
      Pm.take sz (Pm.map f xs) ∷ Pm.slide sz sp (Pm.map f (Pm.drop (suc sp) xs))
    ≡⟨ cong (λ ys → Pm.take sz (Pm.map f xs) ∷ Pm.slide sz sp ys) (map-drop (suc sp) f xs) ⟩
      refl






