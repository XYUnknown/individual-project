{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.Helpers where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (*-distribʳ-+; +-assoc; *-distribˡ-+)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_;  _∎ to _h∎)
  open import lift.HeterogeneousHelpers using (hcong′)
  import lift.Primitives as Pm
  open Pm

  -- a vector with size zero is empty
  empty : {t : Set} → (xs : Vec t zero) → xs ≡ []
  empty [] = refl

  ++-[] : {n : ℕ} → {t : Set} → (xs : Vec t n) →
    xs ++ [] ≡ xs
  ++-[] [] = refl
  ++-[] (x ∷ xs) =
    begin
      x ∷ xs ++ []
    ≡⟨ cong (x ∷_)(++-[] xs) ⟩
      refl

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

  map-++ : {n m : ℕ} → {s t : Set} → (f : s → t) → (xs₁ : Vec s n) → (xs₂ : Vec s m) →
           Pm.map f (xs₁ ++ xs₂) ≡ Pm.map f xs₁ ++ Pm.map f xs₂
  map-++ f [] xs₂ = refl
  map-++ f (x ∷ xs₁) xs₂ =
    begin
      f x ∷ Pm.map f (xs₁ ++ xs₂)
    ≡⟨ cong (f x  ∷_) (map-++ f xs₁ xs₂) ⟩
      refl

  take-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t n) → (xs₁ : Vec t m) →
            Pm.take n {m} (xs ++ xs₁) ≡ xs
  take-++ zero [] xs₁ = refl
  take-++ (suc n) {m} (x ∷ xs) xs₁ =
    begin
      x ∷ Pm.take n {m} (xs ++ xs₁)
    ≡⟨ cong (x ∷_) (take-++ n {m} xs xs₁) ⟩
      refl

  drop-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t n) → (xs₁ : Vec t m) →
            Pm.drop n (xs ++ xs₁) ≡ xs₁
  drop-++ zero [] xs₁ = refl
  drop-++ (suc n) (x ∷ xs) xs₁ =
    begin
      Pm.drop n (xs ++ xs₁)
    ≡⟨ drop-++ n xs xs₁ ⟩
      refl

  transpose-++ : {n m : ℕ} → {t : Set} → (xs : Vec (Vec t zero) n) → (ys : Vec (Vec t zero) m) →
                 Pm.transpose (xs ++ ys) ≡ []
  transpose-++ [] ys =
    begin
      Pm.transpose ys
    ≡⟨ empty (Pm.transpose ys) ⟩
      refl
  transpose-++ (x ∷ xs) ys = refl

  ++-assoc : {n m o : ℕ} → {t : Set} → (xs : Vec t n) → (ys : Vec t m) → (zs : Vec t o) →
             (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = Heq.refl
  ++-assoc {suc n} {m} {o} {t} (x ∷ xs) ys zs = hcong′ (Vec t) (+-assoc n m o) (λ l → x ∷ l) (++-assoc xs ys zs)

  join-++ : {n m o : ℕ} → {t : Set} → (xs₁ : Vec (Vec t o) n) → (xs₂ : Vec (Vec t o) m) →
            Pm.join (xs₁ ++ xs₂) ≅ Pm.join xs₁ ++ Pm.join xs₂
  join-++ [] xs₂ = Heq.refl
  join-++ {suc n} {m} {o} {t} (xs ∷ xs₁) xs₂ =
    hbegin
      xs ++ join (xs₁ ++ xs₂)
    ≅⟨ hcong′ (Vec t) (*-distribˡ-+ o n m) (λ y → xs ++ y) (join-++ xs₁ xs₂) ⟩
      xs ++ join xs₁ ++ join xs₂
    ≅⟨ hsym (++-assoc xs (join xs₁) (join xs₂)) ⟩
      (xs ++ join xs₁) ++ join xs₂
    h∎

  take-all : (n : ℕ) → {t : Set} → (xs : Vec t n) →
             Pm.take n {zero} xs ≡ xs
  take-all zero [] = refl
  take-all (suc n) (x ∷ xs) =
    begin
      x ∷ Pm.take n xs
    ≡⟨ cong (x ∷_) (take-all n xs) ⟩
      refl

  map-take : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             Pm.map f (Pm.take n {m} xs) ≡ (Pm.take n {m} (Pm.map f xs))
  map-take zero f xs = refl
  map-take (suc n) {m} f (x ∷ xs) =
    begin
      f x ∷ Pm.map f (Pm.take n {m} xs)
    ≡⟨ cong (f x ∷_) (map-take n {m} f xs) ⟩
      refl

  map-drop : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             Pm.map f (Pm.drop n {m} xs) ≡ (Pm.drop n {m} (Pm.map f xs))
  map-drop zero f xs = refl
  map-drop (suc n) f (x ∷ xs) = map-drop n f xs

  map-split : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
              Pm.map (Pm.map f) (Pm.split n {m} xs) ≡ Pm.split n {m} (Pm.map f xs)
  map-split n {zero} f xs = refl
  map-split n {suc m} f xs =
    begin
      Pm.map f (Pm.take n xs) ∷ Pm.map (Pm.map f) (Pm.split n (Pm.drop n xs))
    ≡⟨ cong (Pm.map f (Pm.take n xs) ∷_) (map-split n f (Pm.drop n xs)) ⟩
      Pm.map f (Pm.take n xs) ∷ Pm.split n (Pm.map f (Pm.drop n xs))
    ≡⟨ cong (_∷ Pm.split n (Pm.map f (Pm.drop n xs))) (map-take n f xs) ⟩
      Pm.take n (Pm.map f xs) ∷ Pm.split n (Pm.map f (Pm.drop n xs))
    ≡⟨ cong (Pm.take n (Pm.map f xs) ∷_) (cong (Pm.split n) (map-drop n f xs)) ⟩
      Pm.take n (Pm.map f xs) ∷ Pm.split n (Pm.drop n (Pm.map f xs))
    ∎

  take-drop : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n + m)) →
              Pm.take n {m} xs ++ Pm.drop n {m} xs ≡ xs
  take-drop zero xs = refl
  take-drop (suc n) (x ∷ xs) =
    begin
      x ∷ Pm.take n xs ++ Pm.drop n xs
    ≡⟨ cong (x ∷_) (take-drop n xs) ⟩
      refl

  map-head : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             Pm.map f (Pm.map Pm.head xss) ≡ Pm.map Pm.head (Pm.map (Pm.map f) xss)
  map-head f [] = refl
  map-head f ((x ∷ xs) ∷ xss) =
    begin
      f x ∷ Pm.map f (Pm.map Pm.head xss)
    ≡⟨ cong (f x ∷_) (map-head f xss) ⟩
      refl

  map-tail : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             Pm.map (Pm.map f) (Pm.map Pm.tail xss) ≡ Pm.map Pm.tail (Pm.map (Pm.map f) xss)
  map-tail f [] = refl
  map-tail f ((x ∷ xs) ∷ xss) =
    begin
      Pm.map f xs ∷ Pm.map (Pm.map f) (Pm.map Pm.tail xss)
    ≡⟨ cong (Pm.map f xs ∷_) (map-tail f xss) ⟩
      refl

