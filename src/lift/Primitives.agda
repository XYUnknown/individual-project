{-# OPTIONS --allow-unsolved-metas #-} 
{- TODO: remove the pragma when all the holes are filled -}
module lift.Primitives where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribʳ-+; *-distribˡ-+; *-identityʳ; *-identityˡ; +-assoc)
  open import Function using (_∘_)

  {- lemmas -}
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

  {- primitive take -}
  take :  (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t n
  take zero xs = []
  take (suc n) (x ∷ xs) = x ∷ (take n xs)

  {- primitive drop -}
  drop : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t m
  drop zero xs = xs
  drop (suc n) (x ∷ xs) = drop n xs

  {- primitive split -}
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
  split n {zero} xs = []
  split n {suc m} xs rewrite distrib-suc m n = take n xs ∷ split n (drop n xs)

  {- primitive join -}
  join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (n * m)
  join {n} {zero} [] rewrite *-comm n zero = []
  join {n} {suc m} {t} (xs ∷ xs₁) rewrite distrib-suc m n = xs ++ join xs₁
  -- join {n} {suc m} {t} (xs ∷ xs₁) = subst (Vec t) (sym (distrib-suc m n)) (xs ++ join xs₁)

  {- unused and alternative definitions -}
  {- alternative semantics for take and drop -}
  splitAt : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n + m)) →
            ∃₂ λ (xs₁ : Vec t n) (xs₂ : Vec t m) → xs ≡ xs₁ ++ xs₂
  splitAt zero xs =  ([] , xs , refl)
  splitAt (suc n) (x ∷ xs)            with splitAt n xs
  splitAt (suc n) (x ∷ .(xs₁ ++ xs₂)) | (xs₁ , xs₂ , refl) = ((x ∷ xs₁) , xs₂ , refl)

  take′ : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t n
  take′ n xs            with splitAt n xs
  take′ n .(xs₁ ++ xs₂) | (xs₁ , xs₂ , refl) = xs₁

  drop′ : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t m
  drop′ n xs            with splitAt n xs
  drop′ n .(xs₁ ++ xs₂) | (xs₁ , xs₂ , refl) = xs₂

