{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop --confluence-check #-}
{-# OPTIONS --without-K #-}
module lift.Primitives where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; _≢_; refl; cong; sym; subst)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _∸_)
  import Data.Product as Prod
  open Prod using (∃₂; _,_; _×_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Data.Nat.Properties using (*-comm; *-distribˡ-+; *-distribʳ-+; *-identityʳ; +-comm; +-assoc)
  open import Function using (_∘_)
  open import Agda.Builtin.Equality.Rewrite
  open import lift.Operators using (CommAssocMonoid)
  open CommAssocMonoid
  -- open import Debug.Trace using (trace)

  {- rewrites -}
  *zero : {m : ℕ} → m * zero ≡ zero
  *zero {zero} = refl
  *zero {suc m} = *zero {m}

  *id : {m : ℕ} → m * 1 ≡ m
  *id {zero} = refl
  *id {suc m} = cong suc *id

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

  {-# REWRITE *zero +zero +suc *id #-}

  {- cast a vector, adapted from cast in Fin -}
  cast : {t : Set} → {m n : ℕ} → .(_ : m ≡ n) → Vec t m → Vec t n
  cast {t} {zero} {zero} eq [] = []
  cast {t} {suc m} {suc n} eq (x ∷ xs) = x ∷ cast {t} {m} {n} (cong pred eq) xs

  {- primitive map -}
  map : {n : ℕ} → {s : Set} → {t : Set} → (s → t) → Vec s n → Vec t n
  map f [] = []
  map f (x ∷ xs) = f x ∷ map f xs

  {- primitive map₂ -}
  -- the more complex case is map_n
  map₂ : {n m : ℕ} → {s t : Set} → (s → t) → Vec (Vec s n) m → Vec (Vec t n) m
  map₂ f xs = map (map f) xs

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
  split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (m * n) → Vec (Vec t n) m
  split n {zero} xs = []
  split n {suc m} xs = take n {m * n} xs ∷ split n (drop n xs)

  {- primitive join -}
  join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (m * n)
  join [] = []
  join (xs ∷ xs₁) = xs ++ join xs₁
  -- join {n} {suc m} {t} (xs ∷ xs₁) = subst (Vec t) (sym (distrib-suc m n)) (xs ++ join xs₁)

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
  transpose {suc n} {zero} xss = []
  transpose {zero} {m} [] = fill _ []
  transpose {suc n} {suc m} xss = map head xss ∷ transpose (map tail xss)

  {- primitive slide -}
  -- (suc sp) and (suc n), to ensure step > 0
  slide-lem : (n sz sp : ℕ) → suc (sz + (sp + n * suc sp)) ≡ suc (sp + (sz + n * suc sp))
  slide-lem n sz sp =
    begin
      suc (sz + (sp + n * suc sp))
    ≡⟨ cong (λ y → suc y) (sym (+-assoc sz sp (n * suc sp))) ⟩
      suc (sz + sp + n * suc sp)
    ≡⟨ cong (λ y → suc (y + n * suc sp)) (+-comm sz sp) ⟩
      cong (λ y → suc y) (+-assoc sp sz (n * suc sp))

  slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec t (sz + n * (suc sp)) →
          Vec (Vec t sz) (suc n)
  slide {zero} sz sp xs = [ xs ]
  slide {suc n} sz sp xs =
    take sz {(suc n) * (suc sp)} xs ∷ slide {n} sz sp (drop (suc sp) (cast (slide-lem n sz sp) xs))

  slide₂ : {n m : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec (Vec t (sz + n * (suc sp))) (sz + m * (suc sp)) →
           Vec (Vec (Vec (Vec t sz) sz) (suc n)) (suc m)
  slide₂ {n} {m} sz sp xs = map transpose (slide {m} sz sp (map (slide {n} sz sp) xs))

  {- split as a special case of slide -}
  split′ : {n : ℕ} → (sz : ℕ) → {t : Set} → Vec t (sz + n * (suc sz)) → Vec (Vec t sz) (suc n)
  split′ {n} sz xs = slide {n} sz sz xs

  {- primitive reduce -}
  reduceSeq : {n : ℕ} → {s t : Set} → (s → t → t) → t → Vec s n → t
  reduceSeq f init [] = init
  reduceSeq f init (x ∷ xs) = reduceSeq f (f x init) xs

  reduce : {n : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t n → t
  reduce M xs = let _⊕_ = _⊕_ M; ε = ε M
                in reduceSeq _⊕_ ε xs

  {- primitive partRed -}
  -- m should > 0
  partRed : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t (suc m * n) → Vec t (suc m)
  partRed zero {zero} M [] = let ε = ε M
                             in [ ε ]
  partRed (suc n) {zero} M xs = [ reduce M xs ]
  partRed zero {suc m} M [] = let ε = ε M
                              in ε ∷ partRed zero {m} M []
  partRed (suc n) {suc m} M xs = [ reduce M (take (suc n) {suc (n + (m * suc n))} xs) ] ++
                                 partRed (suc n) {m} M ((drop (suc n) xs))

  {- primitive zip -}
  zip : {n : ℕ} → {s : Set} → {t : Set} → Vec s n → Vec t n → Vec (s × t) n
  zip [] [] = []
  zip (x ∷ xs) (y ∷ ys) = (x , y) ∷ zip xs ys

  {- primitive unzip -}
  unzip : {n : ℕ} → {s : Set} → {t : Set} → Vec (s × t) n → Vec s n × Vec t n
  unzip [] = [] , []
  unzip ((x , y) ∷ xs) = Prod.zip _∷_ _∷_ (x , y) (unzip xs)

  {- primitive padCst -}
  padCstˡ : {n : ℕ} → (l : ℕ) → {t : Set} → t → Vec t n → Vec t (l + n)
  padCstˡ zero x xs = xs
  padCstˡ (suc l) x xs = padCstˡ l x ([ x ] ++ xs)

  padCstʳ : {n : ℕ} → (r : ℕ) → {t : Set} → t → Vec t n → Vec t (n + r)
  padCstʳ zero x xs = xs
  padCstʳ (suc r) x xs = padCstʳ r x (xs ++ [ x ])

  padCst : {n : ℕ} → (l r : ℕ) → {t : Set} → t → Vec t n → Vec t (l + n + r)
  padCst l r x xs = padCstʳ r x (padCstˡ l x xs)

  padCst₂ : {n m : ℕ} → (l r : ℕ) → {t : Set} → t → Vec (Vec t n) m → Vec (Vec t (l + n + r)) (l + m + r)
  padCst₂ {n} l r x xs = map (padCst l r x) (padCst l r (fill n x) xs)

  {- this breaks agda, issues fixed in agda v2.6.1 -}
  -- padCst : {n : ℕ} → (l r : ℕ) → {t : Set} → t → Vec t n → Vec t (l + n + r)
  -- padCst zero zero x xs = xs
  -- padCst zero (suc r) x xs = padCst zero r x (xs ++ [ x ])
  -- padCst (suc l) zero x xs = padCst l zero x ([ x ] ++ xs)
  -- padCst (suc l) (suc r) x xs = padCst l r x ([ x ] ++ xs ++ [ x ])
