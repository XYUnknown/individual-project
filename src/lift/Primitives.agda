{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.Primitives where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; _≢_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _∸_)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribˡ-+; *-identityʳ; +-comm; +-assoc)
  open import Function using (_∘_)
  open import Agda.Builtin.Equality.Rewrite

  {- rewrites -}
  *zero : {m : ℕ} → m * zero ≡ zero
  *zero {zero} = refl
  *zero {suc m} = *zero {m}

  *suc : {m n : ℕ} → m * (suc n) ≡ m + m * n
  *suc {m} {n} =
    begin
      m * suc n
    ≡⟨ *-distribˡ-+ m 1 n ⟩
      m * 1 + m * n
    ≡⟨ cong (_+ m * n) (*-identityʳ m) ⟩
      refl

  +zero : {m : ℕ} → m + zero ≡ m
  +zero {zero}  = refl
  +zero {suc m} = cong suc +zero

  +suc : {m n : ℕ} → m + (suc n) ≡ suc (m + n)
  +suc {m} {n} =
    begin
      m + (1 + n)
    ≡⟨ sym (+-assoc m 1 n) ⟩
      m + 1 + n
    ≡⟨ cong (_+ n) (+-comm m 1) ⟩
      refl

  -- TODO : can we put this in REWRITE to aviod using subst and lemma in definition of slide?
  postulate +suc-com : (m n o : ℕ) → suc (m + (n + o)) ≡ suc (n + (m + o))

  {-# REWRITE *zero *suc +zero +suc #-}

  {- primitive map -}
  map : {n : ℕ} → {s : Set} → {t : Set} → (s → t) → Vec s n → Vec t n
  map f [] = []
  map f (x ∷ xs) = (f x) ∷ (map f xs)

  {- primitive id -}
  id : {T : Set} → T → T
  id t = t

  {- primitive take -}
  take : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t n
  take zero xs = []
  take (suc n) {m} (x ∷ xs) = x ∷ (take n {m} xs)

  {- primitive drop -}
  drop : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t m
  drop zero xs = xs
  drop (suc n) (x ∷ xs) = drop n xs

  {- primitive split -}
  {- split as slide with (step ≡ size) ? -}
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
  split n {zero} xs = []
  split n {suc m} xs = take n {n * m} xs ∷ split n (drop n xs)

  {- primitive join -}
  join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (n * m)
  join [] = []
  join (xs ∷ xs₁) = xs ++ join xs₁
  -- join {n} {suc m} {t} (xs ∷ xs₁) = subst (Vec t) (sym (distrib-suc m n)) (xs ++ join xs₁)

  {- primitive slide -}
  -- lemma
  suc-com : (m n o : ℕ) → suc (m + (n + o))  ≡ suc (n + (m + o))
  suc-com m n o =
    begin
      suc (m + (n + o))
    ≡⟨ cong suc (sym (+-assoc m n o )) ⟩
      suc (m + n + o)
    ≡⟨ cong suc (cong (_+ o) (+-comm m n)) ⟩
      suc (n + m + o)
    ≡⟨ cong suc (+-assoc n m o) ⟩
      refl

  -- (suc sp) and (suc n), to ensure step > 0
  slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec t (sz + n * (suc sp)) →
          Vec (Vec t sz) (suc n)
  slide {zero} sz sp xs = [ xs ]
  slide {suc n} sz sp {t} xs =
    take sz {(suc n) * (suc sp)} xs ∷ slide {n} sz sp (drop (suc sp) (subst (Vec t) (suc-com sz sp (n + n * sp)) xs))

  {- primitive reduce -}
  reduceSeq : {n : ℕ} → {s t : Set} → (s → t → t) → t → Vec s n → t
  reduceSeq f init [] = init
  reduceSeq f init (x ∷ xs) = reduceSeq f (f x init) xs

  reduce : {n : ℕ} → {t : Set} → (t → t → t) → t → Vec t n → t
  reduce f init xs = reduceSeq f init xs

  {- primitive partRed-}
  head : {n : ℕ} → {t : Set} → Vec t (suc n) → t
  head (x ∷ xs) = x

  reduce′ : {n : ℕ} → {t : Set} → (t → t → t) → Vec t (suc n) → t
  reduce′ f (x ∷ xs) = reduceSeq f x xs

  partRed : (n : ℕ) → {m : ℕ} → {t : Set} → (t → t → t) → Vec t (m * (suc n)) → Vec t m
  partRed n {zero} f [] = []
  partRed n {suc m} f xs =
    reduce′ f (take (suc n) {(m + m * n)} xs) ∷ partRed n {m} f (drop (suc n) xs)

  {- unused and alternative definitions -}
  {- alternative semantics for take and drop -}
  splitAt : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n + m)) →
            ∃₂ λ (xs₁ : Vec t n) (xs₂ : Vec t m) → xs ≡ xs₁ ++ xs₂
  splitAt zero xs =  ([] , xs , refl)
  splitAt (suc n) {m} (x ∷ xs)            with splitAt n {m} xs
  splitAt (suc n) {m} (x ∷ .(xs₁ ++ xs₂)) | (xs₁ , xs₂ , refl) = ((x ∷ xs₁) , xs₂ , refl)

  take′ : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t n
  take′ n {m} xs            with splitAt n {m} xs
  take′ n {m} .(xs₁ ++ xs₂) | (xs₁ , xs₂ , refl) = xs₁

  drop′ : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t m
  drop′ n {m} xs            with splitAt n {m} xs
  drop′ n {m} .(xs₁ ++ xs₂) | (xs₁ , xs₂ , refl) = xs₂

  {- operators -}
  -- To avoid the rewrites in primitive definitions causing difficulties in writing proofs for rewrite rules
  -- We define * in a nicer way
  _*′_ : ℕ → ℕ → ℕ
  n *′ zero = zero
  n *′ suc m = n + n *′ m

  -- A proof of the equality of customised operator *′ and *
  *≡*′ : (n : ℕ) → (m : ℕ) →
    n * m ≡ n *′ m
  *≡*′ n zero =
    begin
      n * zero
    ≡⟨ *-comm n zero ⟩
      refl
  *≡*′ n (suc m) =
    begin
      n * suc m
    ≡⟨ *-distribˡ-+ n 1 m ⟩
      n * 1 + n * m
    ≡⟨ cong (_+ n * m) (*-identityʳ n) ⟩
      n + n * m
    ≡⟨ cong (n +_) (*≡*′ n m) ⟩
      refl
