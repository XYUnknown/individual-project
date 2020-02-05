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
  open import lift.Primitives using (map; id; take; drop; split; join; fill; head; tail; transpose; slide; reduceSeq; reduce; partRed)

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

  map-id : {n : ℕ} → {s : Set} → (xs : Vec s n ) → map id xs ≡ xs
  map-id [] = refl
  map-id (x ∷ xs) =
    begin
      map id (x ∷ xs)
    ≡⟨⟩
      x ∷ (map id xs)
    ≡⟨ cong (x ∷_) (map-id xs) ⟩
      x ∷ xs
    ∎

  map-++ : {n m : ℕ} → {s t : Set} → (f : s → t) → (xs₁ : Vec s n) → (xs₂ : Vec s m) →
           map f (xs₁ ++ xs₂) ≡ map f xs₁ ++ map f xs₂
  map-++ f [] xs₂ = refl
  map-++ f (x ∷ xs₁) xs₂ =
    begin
      f x ∷ map f (xs₁ ++ xs₂)
    ≡⟨ cong (f x  ∷_) (map-++ f xs₁ xs₂) ⟩
      refl

  take-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t n) → (xs₁ : Vec t m) →
            take n {m} (xs ++ xs₁) ≡ xs
  take-++ zero [] xs₁ = refl
  take-++ (suc n) {m} (x ∷ xs) xs₁ =
    begin
      x ∷ take n {m} (xs ++ xs₁)
    ≡⟨ cong (x ∷_) (take-++ n {m} xs xs₁) ⟩
      refl

  drop-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t n) → (xs₁ : Vec t m) →
            drop n (xs ++ xs₁) ≡ xs₁
  drop-++ zero [] xs₁ = refl
  drop-++ (suc n) (x ∷ xs) xs₁ =
    begin
      drop n (xs ++ xs₁)
    ≡⟨ drop-++ n xs xs₁ ⟩
      refl

  transpose-++ : {n m : ℕ} → {t : Set} → (xs : Vec (Vec t zero) n) → (ys : Vec (Vec t zero) m) →
                 transpose (xs ++ ys) ≡ []
  transpose-++ [] ys =
    begin
      transpose ys
    ≡⟨ empty (transpose ys) ⟩
      refl
  transpose-++ (x ∷ xs) ys = refl

  ++-assoc : {n m o : ℕ} → {t : Set} → (xs : Vec t n) → (ys : Vec t m) → (zs : Vec t o) →
             (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
  ++-assoc [] ys zs = Heq.refl
  ++-assoc {suc n} {m} {o} {t} (x ∷ xs) ys zs = hcong′ (Vec t) (+-assoc n m o) (λ l → x ∷ l) (++-assoc xs ys zs)

  join-++ : {n m o : ℕ} → {t : Set} → (xs₁ : Vec (Vec t o) n) → (xs₂ : Vec (Vec t o) m) →
            join (xs₁ ++ xs₂) ≅ join xs₁ ++ join xs₂
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
             take n {zero} xs ≡ xs
  take-all zero [] = refl
  take-all (suc n) (x ∷ xs) =
    begin
      x ∷ take n xs
    ≡⟨ cong (x ∷_) (take-all n xs) ⟩
      refl

  map-take : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             map f (take n {m} xs) ≡ (take n {m} (map f xs))
  map-take zero f xs = refl
  map-take (suc n) {m} f (x ∷ xs) =
    begin
      f x ∷ map f (take n {m} xs)
    ≡⟨ cong (f x ∷_) (map-take n {m} f xs) ⟩
      refl

  map-drop : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             map f (drop n {m} xs) ≡ (drop n {m} (map f xs))
  map-drop zero f xs = refl
  map-drop (suc n) f (x ∷ xs) = map-drop n f xs

  map-split : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n * m)) →
              map (map f) (split n {m} xs) ≡ split n {m} (map f xs)
  map-split n {zero} f xs = refl
  map-split n {suc m} f xs =
    begin
      map f (take n xs) ∷ map (map f) (split n (drop n xs))
    ≡⟨ cong (map f (take n xs) ∷_) (map-split n f (drop n xs)) ⟩
      map f (take n xs) ∷ split n (map f (drop n xs))
    ≡⟨ cong (_∷ split n (map f (drop n xs))) (map-take n f xs) ⟩
      take n (map f xs) ∷ split n (map f (drop n xs))
    ≡⟨ cong (take n (map f xs) ∷_) (cong (split n) (map-drop n f xs)) ⟩
      take n (map f xs) ∷ split n (drop n (map f xs))
    ∎

  take-drop : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n + m)) →
              take n {m} xs ++ drop n {m} xs ≡ xs
  take-drop zero xs = refl
  take-drop (suc n) (x ∷ xs) =
    begin
      x ∷ take n xs ++ drop n xs
    ≡⟨ cong (x ∷_) (take-drop n xs) ⟩
      refl

  map-head : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             map f (map head xss) ≡ map head (map (map f) xss)
  map-head f [] = refl
  map-head f ((x ∷ xs) ∷ xss) =
    begin
      f x ∷ map f (map head xss)
    ≡⟨ cong (f x ∷_) (map-head f xss) ⟩
      refl

  map-tail : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             map (map f) (map tail xss) ≡ map tail (map (map f) xss)
  map-tail f [] = refl
  map-tail f ((x ∷ xs) ∷ xss) =
    begin
      map f xs ∷ map (map f) (map tail xss)
    ≡⟨ cong (map f xs ∷_) (map-tail f xss) ⟩
      refl

