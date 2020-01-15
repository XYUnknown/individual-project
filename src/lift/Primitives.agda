{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.Primitives where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; _≢_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _∸_)
  import Data.Product as Prod
  open Prod using (∃₂; _,_; _×_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribˡ-+; *-distribʳ-+; *-identityʳ; +-comm; +-assoc)
  open import Function using (_∘_)
  open import Agda.Builtin.Equality.Rewrite
  open import lift.Operators using (CommAssocMonoid)
  open CommAssocMonoid

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

  +comm₁ : {m n o : ℕ} → m + (n + o * suc n) ≡ n + (m + o * suc n)
  +comm₁ {m} {n} {o} =
    begin
      m + (n + o * suc n)
    ≡⟨ sym (+-assoc m n (o * suc n)) ⟩
      m + n + o * suc n
    ≡⟨ cong (_+ o * suc n) (+-comm m n ) ⟩
      n + m + o * suc n
    ≡⟨ +-assoc n m (o * suc n) ⟩
      refl

  {-# REWRITE *zero *suc +zero +suc +comm₁ #-}

  {- primitive map -}
  map : {n : ℕ} → {s : Set} → {t : Set} → (s → t) → Vec s n → Vec t n
  map f [] = []
  map f (x ∷ xs) = (f x) ∷ (map f xs)

  {- primitive mapⁿ -}
  -- the type of the function should be s → s
  -- the function doesn't change the type of the intake argument
  mapⁿ : {m : ℕ} → (n : ℕ) → {s : Set} → (s → s) → Vec s m → Vec s m
  mapⁿ zero f xs = xs
  mapⁿ (suc n) f xs = mapⁿ n f (map f xs)

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
  -- (suc sp) and (suc n), to ensure step > 0
  slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec t (sz + n * (suc sp)) →
          Vec (Vec t sz) (suc n)
  slide {zero} sz sp xs = [ xs ]
  slide {suc n} sz sp {t} xs =
    take sz {(suc n) * (suc sp)} xs ∷ slide {n} sz sp (drop (suc sp) xs)

  {- primitive reduce -}
  reduceSeq : {n : ℕ} → {s t : Set} → (s → t → t) → t → Vec s n → t
  reduceSeq f init [] = init
  reduceSeq f init (x ∷ xs) = reduceSeq f (f x init) xs

  reduce : {n : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t n → t
  reduce M xs = let _⊕_ = _⊕_ M; ε = ε M
                in reduceSeq _⊕_ ε xs

  {- primitive partRed -}
  -- m should > 0
  partRed : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t (n * suc m) → Vec t (suc m)
  partRed zero {zero} M [] = let ε = ε M
                             in [ ε ]
  partRed (suc n) {zero} M xs = [ reduce M xs ]
  partRed zero {suc m} M [] = let ε = ε M
                              in ε ∷ partRed zero {m} M []
  partRed (suc n) {suc m} M xs = [ reduce M (take (suc n) {suc (m + (n + n * m))} xs) ] ++ partRed (suc n) {m} M ((drop (suc n) xs))

  {- primitive zip -}
  zip : {n : ℕ} → {s : Set} → {t : Set} → Vec s n → Vec t n → Vec (s × t) n
  zip [] [] = []
  zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

  {- primitive unzip -}
  unzip : {n : ℕ} → {s : Set} → {t : Set} → Vec (s × t) n → Vec s n × Vec t n
  unzip [] = [] , []
  unzip ((x , y) ∷ xs) = Prod.zip _∷_ _∷_ (x , y) (unzip xs)

  {- primitive transpose -}
  -- lemma, fill a vector with x
  fill : {t : Set} → (n : ℕ) → t → Vec t n
  fill zero x = []
  fill (suc n) x = x ∷ fill n x

  -- lemma head and tail
  head : {t : Set} → {n : ℕ} → Vec t (suc n) → t
  head (x ∷ xs) = x

  tail : {t : Set} → {n : ℕ} → Vec t (suc n) → Vec t n
  tail (x ∷ xs) = xs

  transpose : {n m : ℕ} → {t : Set} → Vec (Vec t m) n → Vec (Vec t n) m
  transpose {zero} {zero} [] = []
  transpose {suc n} {zero} xss = []
  transpose {zero} {suc m} [] = fill _ []
  transpose {suc n} {suc m} xss = map head xss ∷ transpose (map tail xss)

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

  -- unused REWRITE
  *+distrib : {m n o : ℕ} →  m + o + (m + o) * n ≡ m * suc n + o * suc n
  *+distrib {m} {n} {o} =
    begin
      m + o + (m + o) * n
    ≡⟨ cong (m + o +_) (*-distribʳ-+ n m o)⟩
      m + o + (m * n + o * n)
    ≡⟨ (sym (+-assoc (m + o) (m * n) (o * n)))⟩
      m + o + m * n + o * n
    ≡⟨ cong (_+ o * n) (+-assoc m o (m * n)) ⟩
      m + (o + m * n) + o * n
    ≡⟨ cong (λ x → m + x + o * n) (+-comm o (m * n))⟩
      m + (m * n + o) + o * n
    ≡⟨ cong (_+ o * n) (sym (+-assoc m (m * n) o)) ⟩
      m + m * n + o + o * n
    ≡⟨ cong (λ x → x + o + o * n) (sym (*suc {m} {n})) ⟩
      m * suc n + o + o * n
    ≡⟨ +-assoc (m * suc n) o (o * n) ⟩
      m * suc n + (o + o * n)
    ≡⟨ cong (m * suc n +_) (sym (*suc {o} {n})) ⟩
      refl

  *+suc-distrib : {m n o : ℕ} → suc (n + (m + m * n) + (o + o * n)) ≡ suc (n + (m + o + (m + o) * n))
  *+suc-distrib {m} {n} {o} =
    begin
      suc (n + (m + m * n) + (o + o * n))
    ≡⟨ cong (λ x → suc (n + x + (o + o * n))) (sym (*suc {m} {n})) ⟩
      suc (n + m * suc n + (o + o * n))
    ≡⟨ cong (λ x → suc (n + m * suc n + x )) (sym (*suc {o} {n})) ⟩
      suc (n + m * suc n + o * suc n)
    ≡⟨ cong suc (+-assoc n (m * suc n) (o * suc n)) ⟩
      suc (n + (m * suc n + o * suc n))
    ≡⟨ cong (λ x → suc (n + x)) (sym (*+distrib {m} {n} {o})) ⟩
      refl

  *suc′ : {m n : ℕ} →  m + n * m ≡ m + m * n
  *suc′ {m} {n} =
    begin
      m + n * m
    ≡⟨ cong (m +_) (*-comm n m) ⟩
      refl

  +assoc : {m n o : ℕ} → m + (n + o) ≡ m + n + o
  +assoc {m} {n} {o} =
    begin
      m + (n + o)
    ≡⟨ sym (+-assoc m n o) ⟩
      refl
