{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop  --confluence-check #-}
module lift.Helpers where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; pred)
  open import Data.Nat.Properties using (*-distribʳ-+; +-assoc; *-distribˡ-+)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  import Relation.Binary.HeterogeneousEquality as Heq
  open Heq using (_≅_; icong) renaming (sym to hsym; trans to htrans; cong to hcong; subst to hsubst)
  open Heq.≅-Reasoning using (_≅⟨_⟩_) renaming (begin_ to hbegin_; _≡⟨⟩_ to _h≡⟨⟩_; _≡⟨_⟩_ to _h≡⟨_⟩_;  _∎ to _h∎)
  open import lift.HeterogeneousHelpers using (hcong′)
  open import lift.Primitives using (cast; map; id; take; drop; split; join; fill; head; tail; transpose; slide; reduceSeq; reduce; partRed)

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
  map-++ f (x ∷ xs₁) xs₂ = cong (f x  ∷_) (map-++ f xs₁ xs₂)

  take-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t n) → (xs₁ : Vec t m) →
            take n {m} (xs ++ xs₁) ≡ xs
  take-++ zero [] xs₁ = refl
  take-++ (suc n) {m} (x ∷ xs) xs₁ = cong (x ∷_) (take-++ n {m} xs xs₁)

  drop-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t n) → (xs₁ : Vec t m) →
            drop n (xs ++ xs₁) ≡ xs₁
  drop-++ zero [] xs₁ = refl
  drop-++ (suc n) (x ∷ xs) xs₁ = drop-++ n xs xs₁

  transpose-++ : {n m : ℕ} → {t : Set} → (xs : Vec (Vec t zero) n) → (ys : Vec (Vec t zero) m) →
                 transpose (xs ++ ys) ≡ []
  transpose-++ [] ys = empty (transpose ys)
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
    ≅⟨ hcong′ (Vec t) (*-distribʳ-+ o n m) (λ y → xs ++ y) (join-++ xs₁ xs₂) ⟩
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

  map-cast : {m n : ℕ} {s t : Set} → (f : s → t) → (xs : Vec s m) → .(eq : m ≡ n) → map f (cast eq xs) ≡ cast eq (map f xs)
  map-cast {zero} {zero} f [] eq = refl
  map-cast {suc m} {suc n} f (x ∷ xs) eq = cong (f x ∷_) (map-cast {m} {n} f xs (cong pred eq))

  map-take : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             map f (take n {m} xs) ≡ (take n {m} (map f xs))
  map-take zero f xs = refl
  map-take (suc n) {m} f (x ∷ xs) = cong (f x ∷_) (map-take n {m} f xs)

  map-drop : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             map f (drop n {m} xs) ≡ (drop n {m} (map f xs))
  map-drop zero f xs = refl
  map-drop (suc n) f (x ∷ xs) = map-drop n f xs

  map-split : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (m * n)) →
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
  map-head f ((x ∷ xs) ∷ xss) = cong (f x ∷_) (map-head f xss)

  map-tail : {n m : ℕ} → {s t : Set} → (f : s → t) → (xss : Vec (Vec s (suc m)) n) →
             map (map f) (map tail xss) ≡ map tail (map (map f) xss)
  map-tail f [] = refl
  map-tail f ((x ∷ xs) ∷ xss) = cong (map f xs ∷_) (map-tail f xss)

  head-take : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (suc (n + m))) →
              head xs ≡ head (take (suc n) {m} xs)
  head-take zero (x ∷ xs) = refl
  head-take (suc n) (x ∷ xs) = refl

  tail-take : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (suc (n + m))) →
              take n {m} (tail xs) ≡ tail (take (suc n) {m} xs)
  tail-take zero (x ∷ xs) = refl
  tail-take (suc n) (x ∷ xs) = refl

  map-head-take : (n : ℕ) → {m p : ℕ} → {t : Set} → (xs : Vec (Vec t (suc (n + m))) p) →
                  map head xs ≡ map head (map (take (suc n) {m}) xs)
  map-head-take n [] = refl
  map-head-take n {m} (xs₁ ∷ xs) =
    begin
      head xs₁ ∷ map head xs
    ≡⟨ cong₂ (λ x y → x ∷ y) (head-take n {m} xs₁) (map-head-take n {m} xs) ⟩
      refl

  map-tail-take : (n : ℕ) → {m p : ℕ} → {t : Set} → (xs : Vec (Vec t (suc (n + m))) p) →
                  map (take n {m}) (map tail xs) ≡  map tail (map (take (suc n) {m}) xs)
  map-tail-take n [] = refl
  map-tail-take n (xs₁ ∷ xs) =
    begin
      take n (tail xs₁) ∷ map (take n) (map tail xs)
    ≡⟨ cong₂ (λ x y → x ∷ y) (tail-take n xs₁) (map-tail-take n xs) ⟩
      refl

  take-fill : {m : ℕ} → {t : Set} → (n : ℕ) → (x : t) → take n {m} (fill (n + m) x) ≡ fill n x
  take-fill zero x = refl
  take-fill (suc n) x = cong (x ∷_) (take-fill n x)

  drop-fill : {m : ℕ} → {t : Set} → (n : ℕ) → (x : t) → drop n {m} (fill (n + m) x) ≡ fill m x
  drop-fill zero x = refl
  drop-fill (suc n) x = drop-fill n x

  take-transpose : (n : ℕ) → {m p : ℕ} → {t : Set} → (xs : Vec (Vec t (n + m)) p) →
                   take n {m} (transpose xs) ≡ transpose (map (take n {m}) xs)
  take-transpose n {m} {zero} [] = take-fill n []
  take-transpose zero {m} {suc p} xs = refl
  take-transpose (suc n) {m} {suc p} ((x ∷ xs₁) ∷ xs) =
    begin
      (x ∷ map head xs) ∷ take n (transpose (xs₁ ∷ map tail xs))
    ≡⟨ cong ((x ∷ map head xs) ∷_) (take-transpose n (xs₁ ∷ map tail xs)) ⟩
      (x ∷ map head xs) ∷ transpose (take n xs₁ ∷ map (take n) (map tail xs))
    ≡⟨ cong (λ y → (x ∷ y) ∷ transpose (take n xs₁ ∷ map (take n) (map tail xs))) (map-head-take n {m} xs) ⟩
      (x ∷ map head (map (take (suc n)) xs)) ∷ transpose (take n xs₁ ∷ map (take n) (map tail xs))
    ≡⟨ cong (λ y → (x ∷ map head (map (take (suc n)) xs)) ∷ transpose (take n xs₁ ∷ y)) (map-tail-take n xs) ⟩
      refl

  drop-tail : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (suc (n + m))) →
              drop n {m} (tail xs) ≡ drop (suc n) {m} xs
  drop-tail zero (x ∷ xs) = refl
  drop-tail (suc n) (x ∷ xs) = refl

  map-tail-drop : (n : ℕ) → {m p : ℕ} → {t : Set} → (xs : Vec (Vec t (suc (n + m))) p) →
                  map (drop n {m}) (map tail xs) ≡ map (drop (suc n) {m}) xs
  map-tail-drop n [] = refl
  map-tail-drop n (xs₁ ∷ xs) = cong₂ (λ x y → x ∷ y) (drop-tail n xs₁) (map-tail-drop n xs)

  drop-transpose : (n : ℕ) → {m p : ℕ} → {t : Set} → (xs : Vec (Vec t (n + m)) p) →
                   drop n {m} (transpose xs) ≡ transpose (map (drop n {m}) xs)
  drop-transpose n {m} {zero} [] = drop-fill n []
  drop-transpose zero {m} {suc p} xs = cong transpose (sym (map-id xs))
  drop-transpose (suc n) {m} {suc p} ((x ∷ xs₁) ∷ xs) =
    begin
      drop n (transpose (xs₁ ∷ map tail xs))
    ≡⟨ drop-transpose n (xs₁ ∷ map tail xs) ⟩
      transpose (drop n xs₁ ∷ map (drop n) (map tail xs))
    ≡⟨ cong (λ y → transpose (drop n xs₁ ∷ y)) (map-tail-drop n xs) ⟩
      refl

  fill-cast : {m n : ℕ} → {t : Set} → {xs : Vec t zero} → .(eq : m ≡ n) → cast eq (fill m xs) ≡ fill n []
  fill-cast {zero} {zero} eq = refl
  fill-cast {suc m} {suc n} {t} {[]} eq = cong ([] ∷_) (fill-cast {m} {n} (cong pred eq))

  map-head-cast : {m m₁ n : ℕ} → {t : Set} → .(eq : suc m ≡ suc m₁) → (xs : Vec (Vec t (suc m)) (suc n)) →
                  map head xs ≡ map head (map (cast eq) xs)
  map-head-cast {zero} {zero} {zero} eq ((x ∷ []) ∷ []) = refl
  map-head-cast {zero} {zero} {suc n} eq ((x ∷ []) ∷ xs₁) = cong (x ∷_) (map-head-cast eq xs₁)
  map-head-cast {suc m} {suc m₁} {zero} eq ((x ∷ xs) ∷ []) = refl
  map-head-cast {suc m} {suc m₁} {suc n} eq ((x ∷ xs) ∷ xs₁) = cong (x ∷_) (map-head-cast eq xs₁)

  map-tail-cast : {m m₁ n : ℕ} → {t : Set} → .(eq : suc m ≡ suc m₁) → (xs : Vec (Vec t (suc m)) (suc n)) →
                  map (cast (cong pred eq)) (map tail xs) ≡ map tail (map (cast eq) xs)
  map-tail-cast {zero} {zero} {zero} eq ((x ∷ []) ∷ []) = refl
  map-tail-cast {zero} {zero} {suc n} eq ((x ∷ []) ∷ xs₁) = cong ([] ∷_) (map-tail-cast eq xs₁)
  map-tail-cast {suc m} {suc m₁} {zero} eq ((x ∷ xs) ∷ []) = refl
  map-tail-cast {suc m} {suc m₁} {suc n} eq ((x ∷ xs) ∷ xs₁) = cong (cast (cong pred eq) xs ∷_) (map-tail-cast eq xs₁)

  transpose-cast : {m m₁ n : ℕ} → {t : Set} → .(eq : m ≡ m₁) → (xs : Vec (Vec t m) n) → cast eq (transpose xs) ≡ transpose (map (cast eq) xs)
  transpose-cast {zero} {zero} {zero} eq [] = refl
  transpose-cast {zero} {zero} {suc n} eq xs = refl
  transpose-cast {suc m} {suc m₁} {zero} eq [] = cong ([] ∷_) (fill-cast {m} {m₁} (cong pred eq))
  transpose-cast {suc m} {suc m₁} {suc n} eq xs =
    begin
      map head xs ∷ cast _ (transpose (map tail xs))
    ≡⟨ cong (map head xs ∷_) (transpose-cast {m} {m₁} (cong pred eq) (map tail xs) ) ⟩
      map head xs ∷ transpose (map (cast _) (map tail xs))
    ≡⟨ cong₂ (λ x y → x ∷ transpose y) (map-head-cast eq xs) (map-tail-cast eq xs) ⟩
      refl
