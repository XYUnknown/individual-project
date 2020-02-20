{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.AlgorithmicRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Nat.Properties using (*-distribʳ-+)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)
  open import lift.Primitives using (map; id; take; drop; split;
    join; fill; head; tail; transpose; slide; reduceSeq; reduce; partRed)
  open import lift.Operators using (CommAssocMonoid)
  open CommAssocMonoid
  open import lift.Helpers

  {- lemmas -}
  -- used in proving reduction
  reduceSeq-reduce : {n : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (x : t) → (xs : Vec t n) →
                     let _⊕_ = _⊕_ M in
                     x ⊕ reduce M xs ≡ reduceSeq _⊕_ x xs
  reduceSeq-reduce M x [] = let ε = ε M; _⊕_ = _⊕_ M in
    begin
      x ⊕ ε
    ≡⟨ idʳ M x ⟩
      refl
  reduceSeq-reduce M x (x₁ ∷ xs) =  let ε = ε M; _⊕_ = _⊕_ M in
    begin
      x ⊕ reduceSeq _⊕_ (x₁ ⊕ ε) xs
    ≡⟨ cong (λ y → x ⊕ (reduceSeq _⊕_ y xs)) (idʳ M x₁) ⟩
      x ⊕ reduceSeq _⊕_ x₁ xs
    ≡⟨ cong (x ⊕_) (sym (reduceSeq-reduce M x₁ xs)) ⟩
      x ⊕ (x₁ ⊕ reduce M xs)
    ≡⟨ sym (assoc M x x₁ (reduce M xs)) ⟩
      (x ⊕ x₁) ⊕ reduce M xs
    ≡⟨ cong (_⊕ reduce M xs) (comm M x x₁) ⟩
      (x₁ ⊕ x) ⊕ reduce M xs
    ≡⟨ reduceSeq-reduce M (x₁ ⊕ x) xs ⟩
      refl

  reduce-++ : {n m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (xs₁ : Vec t n) → (xs₂ : Vec t m) →
              let _⊕_ = _⊕_ M in
              reduce M xs₁ ⊕ reduce M xs₂ ≡ reduce M (xs₁ ++ xs₂)
  reduce-++ M [] xs₂ = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      reduce M [] ⊕ reduce M xs₂
    ≡⟨⟩
      ε ⊕ reduce M xs₂
    ≡⟨ idˡ M (reduce M xs₂) ⟩
      refl
  reduce-++ M (x ∷ xs₁) xs₂ = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      reduce M (x ∷ xs₁) ⊕ reduce M xs₂
    ≡⟨⟩
      reduceSeq _⊕_ (x ⊕ ε) xs₁ ⊕ reduce M xs₂
    ≡⟨ cong (λ y → reduceSeq _⊕_ y xs₁ ⊕ reduce M xs₂) (idʳ M x) ⟩
      reduceSeq _⊕_ x xs₁ ⊕ reduce M xs₂
    ≡⟨ cong (_⊕ reduce M xs₂) (sym (reduceSeq-reduce M x xs₁)) ⟩
      (x ⊕ reduce M xs₁) ⊕ reduce M xs₂
    ≡⟨ assoc M x (reduce M xs₁) (reduce M xs₂) ⟩
      x ⊕ (reduce M xs₁ ⊕ reduce M xs₂)
    ≡⟨ cong (x ⊕_) (reduce-++ M xs₁ xs₂) ⟩
      x ⊕ reduce M (xs₁ ++ xs₂)
    ≡⟨ reduceSeq-reduce M x (xs₁ ++ xs₂) ⟩
      reduceSeq _⊕_ x (xs₁ ++ xs₂)
    ≡⟨ cong (λ y → reduceSeq _⊕_ y (xs₁ ++ xs₂)) (sym (idʳ M x)) ⟩
      refl

  reduce-take-drop : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (xs : Vec t (n + m)) →
                     let _⊕_ = _⊕_ M in
                     reduce M xs ≡ reduce M (take n {m} xs) ⊕ reduce M (drop n {m} xs)
  reduce-take-drop n {m} M xs =
    begin
      reduce M xs
    ≡⟨ cong (reduce M) (sym (take-drop n {m} xs)) ⟩
      reduce M (take n {m} xs ++ drop n xs)
    ≡⟨ sym (reduce-++ M (take n {m} xs) (drop n xs)) ⟩
      refl

  -- used in proving partialReduction₂
  partRed-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (xs₁ : Vec t n) → (xs₂ : Vec t (suc m * n)) →
               partRed n {suc m} M (xs₁ ++ xs₂) ≡ partRed n M xs₁ ++ partRed n {m} M xs₂
  partRed-++ zero {m} M [] [] = refl
  partRed-++ (suc n) {m} M xs₁ xs₂ =
    begin
      reduce M (take (suc n) {suc (n + m * suc n)} (xs₁ ++ xs₂)) ∷
      partRed (suc n) M (drop (suc n) (xs₁ ++ xs₂))
    ≡⟨ cong (λ ys → (reduce M ys ∷ partRed (suc n) M (drop (suc n) (xs₁ ++ xs₂)))) (take-++ (suc n) xs₁ xs₂) ⟩
      reduce M xs₁ ∷ partRed (suc n) M (drop (suc n) (xs₁ ++ xs₂))
    ≡⟨ cong (λ ys → (reduce M xs₁ ∷ partRed (suc n) M ys)) (drop-++ (suc n) xs₁ xs₂) ⟩
      refl

  map-join-partRed : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xss : Vec (Vec t n) (suc m)) →
                     join (map (partRed n {zero} M) xss) ≡ partRed n {m} M (join {n} {suc m} xss)
  map-join-partRed {zero} n M (xs ∷ []) =
    begin
      partRed n M xs ++ []
    ≡⟨ ++-[] (partRed n M xs) ⟩
      partRed n M xs
    ≡⟨ cong (λ ys → partRed n M ys) (sym (++-[] xs)) ⟩
      refl
  map-join-partRed {suc m} n M (xs ∷ xs₁) =
    begin
      partRed n {zero} M xs ++ join (map (partRed n {zero} M) xs₁)
    ≡⟨ cong (partRed n {zero} M xs ++_) (map-join-partRed n M xs₁) ⟩
      partRed n M xs ++ partRed n {m} M (join {n} {suc m} xs₁)
    ≡⟨ sym (partRed-++ n M xs (join {n} {suc m} xs₁)) ⟩
      refl

  {- Identity rules -}
  identity₁ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (f ∘ map id) xs ≡ f xs
  identity₁ f xs =
    begin
      (f ∘ map id) xs
    ≡⟨⟩
      f (map id xs)
    ≡⟨ cong f (map-id xs) ⟩
      f xs
    ∎

  identity₂ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (map id ∘ f) xs ≡ f xs
  identity₂ f xs =
    begin
      (map id ∘ f) xs
    ≡⟨⟩
      map id (f xs)
    ≡⟨ map-id (f xs) ⟩
      f xs
    ∎

  fill-empty : {t : Set} → {n : ℕ} → (xss : Vec (Vec t zero) n) →
               fill n [] ≡ xss
  fill-empty [] = refl
  fill-empty ([] ∷ xss) =
    begin
      [] ∷ fill _ []
    ≡⟨ cong ([] ∷_) (fill-empty xss) ⟩
      refl

  fill-empty₂ : {m : ℕ} → {t : Set} → (xs : Vec t m) →
                map tail (transpose (xs ∷ [])) ≡ fill m []
  fill-empty₂ [] = refl
  fill-empty₂ (x ∷ xs) =
    begin
      [] ∷ map tail (transpose (xs ∷ []))
    ≡⟨ cong ([] ∷_) (fill-empty₂ xs) ⟩
      refl

  map-tail-trans : {n m : ℕ} → {t : Set} → (xs : Vec t (suc m)) → (xss : Vec (Vec t (suc (suc m))) (suc n)) →
                   map tail (transpose (tail xs ∷ map tail (map tail xss))) ≡ transpose (map tail (map tail xss))
  map-tail-trans {n} {zero} (x ∷ []) xss = refl
  map-tail-trans {n} {suc m} (x ∷ xs) xss =
    begin
      map head (map tail (map tail xss)) ∷
      map tail (transpose (tail xs ∷ map tail (map tail (map tail xss))))
    ≡⟨ cong ( map head (map tail (map tail xss)) ∷_) (map-tail-trans xs (map tail xss)) ⟩
      refl

  transpose-head : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) n) →
                   map head (transpose (xs ∷ map tail xss)) ≡ xs
  transpose-head {n} {zero} [] xss = refl
  transpose-head {n} {suc m} (x ∷ xs) xss =
    begin
      x ∷ map head (transpose (xs ∷ map tail (map tail xss)))
    ≡⟨ cong (x ∷_) (transpose-head {n} {m} xs (map tail xss)) ⟩
      refl

  transpose-tail : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) n) →
                   map head xss ∷ map tail (transpose (xs ∷ map tail xss)) ≡ transpose xss
  transpose-tail {zero} {m} xs [] =
    begin
      [] ∷ map tail (transpose (xs ∷ []))
    ≡⟨ cong ([] ∷_) (fill-empty₂ xs) ⟩
      refl
  transpose-tail {suc n} {zero} [] xss = refl
  transpose-tail {suc n} {suc m} xs xss =
    begin
      map head xss ∷
      map head (map tail xss) ∷
      map tail (transpose (tail xs ∷ map tail (map tail xss)))
    ≡⟨ cong (map head xss ∷_) (cong (map head (map tail xss) ∷_) (map-tail-trans xs xss)) ⟩
      refl

  -- (Aᵀ)ᵀ ≡ A
  identity₃ : {n m : ℕ} → {t : Set} → (xss : Vec (Vec t m) n) →
              transpose (transpose xss) ≡ xss
  identity₃ {suc n} {zero} ([] ∷ xss) =
    begin
      [] ∷ fill n []
    ≡⟨ cong ([] ∷_) (fill-empty xss) ⟩
      refl
  identity₃ {zero} {m} [] =
    begin
      transpose (fill _ [])
    ≡⟨ empty (transpose (fill _ [])) ⟩
      refl
  identity₃ {suc n} {suc m} ((x ∷ xs) ∷ xss) =
    begin
      (x ∷ map head (transpose (xs ∷ map tail xss))) ∷
      transpose (map head xss ∷ map tail (transpose (xs ∷ map tail xss)))
    ≡⟨ cong (_∷ transpose (map head xss ∷ map tail (transpose (xs ∷ map tail xss))))
       (cong (x ∷_) (transpose-head xs xss)) ⟩
      (x ∷ xs) ∷ transpose (map head xss ∷ map tail (transpose (xs ∷ map tail xss)))
    ≡⟨ cong (λ yss → (x ∷ xs) ∷ transpose yss) (transpose-tail xs xss) ⟩
      (x ∷ xs) ∷ transpose (transpose xss)
    ≡⟨ cong ((x ∷ xs) ∷_) (identity₃ xss) ⟩
      refl

  {- Fusion rules -}
  fusion₁ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} → (f : t → r) → (g : s → t) → (xs : Vec s n) →
            (map f ∘ map g) xs ≡ map (f ∘ g) xs
  fusion₁ f g [] =
    begin
      (map f ∘ map g) []
    ≡⟨⟩
      map f (map g [])
    ≡⟨⟩
      map f []
    ≡⟨⟩
      []
    ≡⟨⟩
      map (f ∘ g) []
    ∎

  fusion₁ f g (x ∷ xs) =
    begin
      (map f ∘ map g) (x ∷ xs)
    ≡⟨⟩
      map f (map g (x ∷ xs))
    ≡⟨⟩
      map f (g x ∷ map g xs)
    ≡⟨⟩
      f (g x) ∷ map f (map g xs)
    ≡⟨⟩
      (f ∘ g) x ∷ map f (map g xs)
    ≡⟨ cong ((f ∘ g) x ∷_ ) (fusion₁ f g xs) ⟩
      (f ∘ g) x ∷ map (f ∘ g) xs
    ∎

  fusion₂ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} →
            (f : s → t) → (bf : t → r → r) → (init : r) → (xs : Vec s n) →
            reduceSeq (λ (a : s) (b : r) → (bf (f a) b)) init xs ≡ (reduceSeq bf init ∘ map f) xs
  fusion₂ f bf init [] = refl
  fusion₂ f bf init (x ∷ xs) =
    begin
      reduceSeq (λ a → bf (f a)) (bf (f x) init) xs
    ≡⟨ fusion₂ f bf (bf (f x) init) xs ⟩
      reduceSeq bf (bf (f x) init) (map f xs)
    ≡⟨⟩
      (reduceSeq bf init ∘ map f) (x ∷ xs)
    ∎

  {- Simplification rules -}
  simplification₁ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (m * n)) →
                    (join ∘ split n {m}) xs ≡ xs
  simplification₁ n {zero} [] = refl
  simplification₁ n {suc m} xs =
    begin
      take n xs ++ join (split n {m} (drop n xs))
    ≡⟨ cong (take n xs ++_) (simplification₁ n {m} (drop n xs)) ⟩
      take n xs ++ drop n xs
    ≡⟨ take-drop n xs ⟩
      refl

  simplification₂ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec (Vec t n) m) →
                    (split n ∘ join) xs ≡ xs
  simplification₂ n {zero} [] = refl
  simplification₂ n {suc m} (xs ∷ xs₁) =
    begin
      take n (xs ++ join xs₁) ∷ split n (drop n (xs ++ join xs₁))
    ≡⟨ cong (_∷ split n (drop n (xs ++ join xs₁))) (take-++ n xs (join xs₁)) ⟩
      xs ∷ split n (drop n (xs ++ join xs₁))
    ≡⟨ cong (xs ∷_) (cong (split n) (drop-++ n xs (join xs₁))) ⟩
      xs ∷ split n (join xs₁)
    ≡⟨ cong (xs ∷_) (simplification₂ n xs₁) ⟩
      refl

  {- Split-join rule -}
  splitJoin : {m : ℕ} → {s : Set} → {t : Set} →
              (n : ℕ) → (f : s → t) → (xs : Vec s (m * n)) →
              (join ∘ map (map f) ∘ split n {m}) xs ≡ map f xs
  splitJoin {m} n f xs =
    begin
      (join ∘ map (map f) ∘ split n {m}) xs
    ≡⟨⟩
      join (map (map f) (split n {m} xs))
    ≡⟨ cong join (map-split n {m} f xs) ⟩
      join (split n {m} (map f xs))
    ≡⟨ simplification₁ n {m} (map f xs) ⟩
      map f xs
    ∎

  {- Reduction -}
  reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
              (reduce M ∘ partRed n {m} M) xs ≡ reduce M xs
  reduction {zero} zero M [] = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      reduce M [ ε ]
    ≡⟨⟩
      ε ⊕ ε
    ≡⟨ idʳ M ε ⟩
      refl
  reduction {zero} (suc n) M xs = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      reduce M [ reduce M xs ]
    ≡⟨⟩
      (reduce M xs) ⊕ ε
    ≡⟨ idʳ M (reduce M xs) ⟩
      refl
  reduction {suc m} zero M [] = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      reduce M (ε ∷ partRed zero {m} M [])
    ≡⟨⟩
      reduceSeq _⊕_ (ε ⊕ ε) (partRed zero {m} M [])
    ≡⟨ cong (λ y → reduceSeq _⊕_ y (partRed zero {m} M [])) (idʳ M ε) ⟩
      reduce M (partRed zero {m} M [])
    ≡⟨ reduction {m} zero M [] ⟩
      refl
  reduction {suc m} (suc n) M xs = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      reduce M ([ reduce M (take (suc n) {suc (n + (m * suc n))} xs) ] ++ partRed (suc n) {m} M (drop (suc n) xs))
    ≡⟨ sym (reduce-++ M [ reduce M (take (suc n) {suc (n + (m * suc n))} xs) ] (partRed (suc n) {m} M (drop (suc n) xs))) ⟩
      reduce M [ reduce M (take (suc n) {suc (n + (m * suc n))} xs) ] ⊕ reduce M (partRed (suc n) {m} M (drop (suc n) xs))
    ≡⟨ cong (_⊕ reduce M (partRed (suc n) {m} M (drop (suc n) xs)))
       (idʳ M (reduce M (take (suc n) {suc (n + (m * suc n))} xs))) ⟩
      reduce M (take (suc n) {suc (n + (m * suc n))} xs) ⊕ reduce M (partRed (suc n) {m} M (drop (suc n) xs))
    ≡⟨ cong (reduce M (take (suc n) {suc (n + (m * suc n))} xs) ⊕_) (reduction {m} (suc n) M (drop (suc n) xs)) ⟩
      reduce M (take (suc n) {suc (n + (m * suc n))} xs) ⊕ reduce M (drop (suc n) {suc (n + (m * suc n))} xs)
    ≡⟨ sym (reduce-take-drop (suc n) {suc (n + (m * suc n))} M xs) ⟩
      refl

  {- Partial Reduction -}
  partialReduction₁ : {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t n)  →
                      partRed n M xs ≡ [ reduce M xs ]
  partialReduction₁ zero M [] = refl
  partialReduction₁ (suc n) M xs = refl

  partialReduction₂ : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
                      (join ∘ map (partRed n {zero} M) ∘ split n {suc m}) xs ≡ partRed n {m} M xs
  partialReduction₂ {zero} zero M [] = refl
  partialReduction₂ {zero} (suc n) M xs =
    begin
      [ reduce M (take (suc n) {zero} xs) ]
    ≡⟨ cong (λ ys → [ (reduce M) ys ]) (take-all (suc n) xs ) ⟩
      refl
  partialReduction₂ {suc m} zero M [] = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      join (map (partRed zero {zero} M) (split zero {suc (suc m)} []))
    ≡⟨⟩
      ε ∷ join (map (partRed zero {zero} M) (split zero {suc m} []))
    ≡⟨ cong (λ ys → (ε ∷ ys)) (map-join-partRed {m} zero M (split zero {suc m} [])) ⟩
      ε ∷ partRed zero {m} M (join {zero} {suc m} (split zero []))
    ≡⟨ cong (λ ys → (ε ∷ partRed zero {m} M ys)) (simplification₁ zero {m} []) ⟩
      refl
  partialReduction₂ {suc m} (suc n) M xs =
    begin
      join (map (partRed (suc n) {zero} M) (split (suc n) {suc (suc m)} xs))
    ≡⟨ map-join-partRed {suc m} (suc n) M (split (suc n) {suc (suc m)} xs) ⟩
      partRed (suc n) {suc m} M (join {suc n} (split (suc n) {suc (suc m)} xs))
    ≡⟨ cong (partRed (suc n) M) (simplification₁ (suc n) {suc (suc m)} xs) ⟩
      refl

