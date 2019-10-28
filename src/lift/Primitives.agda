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

  -- TODO potentially to deal with _+_
  +zero : {m : ℕ} → m + zero ≡ m
  +zero {m = zero}  = refl
  +zero {m = suc m} = cong suc +zero
  postulate +suc : {m n : ℕ} → m + (suc n) ≡ suc (m + n)
  -- +suc = {!!}

  {-# REWRITE *zero *suc #-}

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

  {- primitive map -}
  map : {n : ℕ} → {s : Set} → {t : Set} → (s → t) → Vec s n → Vec t n
  map f [] = []
  map f (x ∷ xs) = (f x) ∷ (map f xs)

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
  {- split as slide with (step ≡ size) ? -}
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
  split n {zero} xs = []
  split n {suc m} xs = take n xs ∷ split n (drop n xs)

  {- primitive join -}
  join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (n * m)
  join [] = []
  join (xs ∷ xs₁) = xs ++ join xs₁
  -- join {n} {suc m} {t} (xs ∷ xs₁) = subst (Vec t) (sym (distrib-suc m n)) (xs ++ join xs₁)

  {- primitive slide -}
  -- sp > 0
  -- n > 0
  slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec t (n * (suc sp) + sz) →
          Vec (Vec t sz) (suc n)
  slide {zero} sz sp xs = [ xs ]
  slide {suc n} sz sp xs = take sz {(suc n)* (suc sp)} {!!} ∷ slide {n} sz sp (drop sp {!!})

  {- primitive reduce -}
  reduceSeq : {n : ℕ} → {s t : Set} → (s → t → t) → t → Vec s n → t
  reduceSeq f init [] = init
  reduceSeq f init (x ∷ xs) = reduceSeq f (f x init) xs

  reduce : {n : ℕ} → {t : Set} → (t → t → t) → t → Vec t n → t
  reduce f init xs = reduceSeq f init xs

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
