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
  import lift.Primitives as Pm
  open Pm
  open import lift.Operators using (CommAssocMonoid)
  open CommAssocMonoid
  open import lift.Helpers


  {- lemmas -}

  -- used in proving reduction
  reduceSeq-reduce : {n : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (x : t) → (xs : Vec t n) →
                     let _⊕_ = _⊕_ M in
                     x ⊕ Pm.reduce M xs ≡ Pm.reduceSeq _⊕_ x xs
  reduceSeq-reduce M x [] = let ε = ε M; _⊕_ = _⊕_ M in
    begin
      x ⊕ ε
    ≡⟨ idʳ M x ⟩
      refl
  reduceSeq-reduce M x (x₁ ∷ xs) =  let ε = ε M; _⊕_ = _⊕_ M in
    begin
      x ⊕ Pm.reduceSeq _⊕_ (x₁ ⊕ ε) xs
    ≡⟨ cong (λ y → x ⊕ (Pm.reduceSeq _⊕_ y xs)) (idʳ M x₁) ⟩
      x ⊕ Pm.reduceSeq _⊕_ x₁ xs
    ≡⟨ cong (x ⊕_) (sym (reduceSeq-reduce M x₁ xs)) ⟩
      x ⊕ (x₁ ⊕ Pm.reduce M xs)
    ≡⟨ sym (assoc M x x₁ (Pm.reduce M xs)) ⟩
      (x ⊕ x₁) ⊕ Pm.reduce M xs
    ≡⟨ cong (_⊕ Pm.reduce M xs) (comm M x x₁) ⟩
      (x₁ ⊕ x) ⊕ Pm.reduce M xs
    ≡⟨ reduceSeq-reduce M (x₁ ⊕ x) xs ⟩
      refl

  reduce-++ : {n m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (xs₁ : Vec t n) → (xs₂ : Vec t m) →
              let _⊕_ = _⊕_ M in
              Pm.reduce M xs₁ ⊕ Pm.reduce M xs₂ ≡ Pm.reduce M (xs₁ ++ xs₂)
  reduce-++ M [] xs₂ = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.reduce M [] ⊕ Pm.reduce M xs₂
    ≡⟨⟩
      ε ⊕ Pm.reduce M xs₂
    ≡⟨ idˡ M (Pm.reduce M xs₂) ⟩
      refl
  reduce-++ M (x ∷ xs₁) xs₂ = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.reduce M (x ∷ xs₁) ⊕ Pm.reduce M xs₂
    ≡⟨⟩
      Pm.reduceSeq _⊕_ (x ⊕ ε) xs₁ ⊕ Pm.reduce M xs₂
    ≡⟨ cong (λ y → Pm.reduceSeq _⊕_ y xs₁ ⊕ Pm.reduce M xs₂) (idʳ M x) ⟩
      Pm.reduceSeq _⊕_ x xs₁ ⊕ Pm.reduce M xs₂
    ≡⟨ cong (_⊕ Pm.reduce M xs₂) (sym (reduceSeq-reduce M x xs₁)) ⟩
      (x ⊕ Pm.reduce M xs₁) ⊕ Pm.reduce M xs₂
    ≡⟨ assoc M x (Pm.reduce M xs₁) (Pm.reduce M xs₂) ⟩
      x ⊕ (Pm.reduce M xs₁ ⊕ Pm.reduce M xs₂)
    ≡⟨ cong (x ⊕_) (reduce-++ M xs₁ xs₂) ⟩
      x ⊕ Pm.reduce M (xs₁ ++ xs₂)
    ≡⟨ reduceSeq-reduce M x (xs₁ ++ xs₂) ⟩
      Pm.reduceSeq _⊕_ x (xs₁ ++ xs₂)
    ≡⟨ cong (λ y → Pm.reduceSeq _⊕_ y (xs₁ ++ xs₂)) (sym (idʳ M x)) ⟩
      refl

  reduce-take-drop : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (xs : Vec t (n + m)) →
                     let _⊕_ = _⊕_ M in
                     Pm.reduce M xs ≡ Pm.reduce M (Pm.take n {m} xs) ⊕ Pm.reduce M (Pm.drop n {m} xs)
  reduce-take-drop n {m} M xs =
    begin
      Pm.reduce M xs
    ≡⟨ cong (Pm.reduce M) (sym (take-drop n {m} xs)) ⟩
      Pm.reduce M (Pm.take n {m} xs ++ Pm.drop n xs)
    ≡⟨ sym (reduce-++ M (Pm.take n {m} xs) (Pm.drop n xs)) ⟩
      refl

  -- used in proving partialReduction₂ ml
  partRed-++ : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → (xs₁ : Vec t n) → (xs₂ : Vec t (n * suc m)) →
               Pm.partRed n {suc m} M (xs₁ ++ xs₂) ≡ Pm.partRed n M xs₁ ++ partRed n {m} M xs₂
  partRed-++ zero {m} M [] [] = refl
  partRed-++ (suc n) {m} M xs₁ xs₂ =
    begin
      Pm.reduce M (Pm.take (suc n) {suc n * suc m} (xs₁ ++ xs₂)) ∷
      Pm.partRed (suc n) M (Pm.drop (suc n) (xs₁ ++ xs₂))
    ≡⟨ cong (λ ys → (Pm.reduce M ys ∷ Pm.partRed (suc n) M (Pm.drop (suc n) (xs₁ ++ xs₂)))) (take-++ (suc n) {suc n * suc m} xs₁ xs₂) ⟩
      Pm.reduce M xs₁ ∷ Pm.partRed (suc n) M (Pm.drop (suc n) (xs₁ ++ xs₂))
    ≡⟨ cong (λ ys → (Pm.reduce M xs₁ ∷ Pm.partRed (suc n) M ys)) (drop-++ (suc n) xs₁ xs₂) ⟩
      refl

  map-join-partRed : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xss : Vec (Vec t n) (suc m)) →
                     Pm.join (Pm.map (Pm.partRed n {zero} M) xss) ≡ Pm.partRed n {m} M (Pm.join {n} {suc m} xss)
  map-join-partRed {zero} n M (xs ∷ []) =
    begin
      Pm.partRed n M xs ++ []
    ≡⟨ ++-[] (Pm.partRed n M xs) ⟩
      Pm.partRed n M xs
    ≡⟨ cong (λ ys → Pm.partRed n M ys) (sym (++-[] xs)) ⟩
      refl
  map-join-partRed {suc m} n M (xs ∷ xs₁) =
    begin
      Pm.partRed n {zero} M xs ++ Pm.join (Pm.map (Pm.partRed n {zero} M) xs₁)
    ≡⟨ cong (Pm.partRed n {zero} M xs ++_) (map-join-partRed n M xs₁) ⟩
      Pm.partRed n M xs ++ Pm.partRed n {m} M (Pm.join {n} {suc m} xs₁)
    ≡⟨ sym (partRed-++ n M xs (Pm.join {n} {suc m} xs₁)) ⟩
      refl

  {- Identity rules -}
  identity₁ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (f ∘ Pm.map Pm.id) xs ≡ f xs
  identity₁ f xs =
    begin
      (f ∘ Pm.map Pm.id) xs
    ≡⟨⟩
      f (Pm.map Pm.id xs)
    ≡⟨ cong f (map-id xs) ⟩
      f xs
    ∎

  identity₂ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (Pm.map Pm.id ∘ f) xs ≡ f xs
  identity₂ f xs =
    begin
      (Pm.map Pm.id ∘ f) xs
    ≡⟨⟩
      Pm.map Pm.id (f xs)
    ≡⟨ map-id (f xs) ⟩
      f xs
    ∎

  fill-empty : {t : Set} → {n : ℕ} → (xss : Vec (Vec t zero) n) →
               Pm.fill n [] ≡ xss
  fill-empty [] = refl
  fill-empty ([] ∷ xss) =
    begin
      [] ∷ Pm.fill _ []
    ≡⟨ cong ([] ∷_) (fill-empty xss) ⟩
      refl

  fill-empty₂ : {m : ℕ} → {t : Set} → (xs : Vec t m) →
                Pm.map Pm.tail (Pm.transpose (xs ∷ [])) ≡ Pm.fill m []
  fill-empty₂ [] = refl
  fill-empty₂ (x ∷ xs) =
    begin
      [] ∷ Pm.map Pm.tail (Pm.transpose (xs ∷ []))
    ≡⟨ cong ([] ∷_) (fill-empty₂ xs) ⟩
      refl

  map-tail-trans : {n m : ℕ} → {t : Set} → (xs : Vec t (suc m)) → (xss : Vec (Vec t (suc (suc m))) (suc n)) →
                   Pm.map Pm.tail (Pm.transpose (Pm.tail xs ∷ Pm.map Pm.tail (Pm.map Pm.tail xss))) ≡ Pm.transpose (Pm.map Pm.tail (Pm.map Pm.tail xss))
  map-tail-trans {n} {zero} (x ∷ []) xss = refl
  map-tail-trans {n} {suc m} (x ∷ xs) xss =
    begin
      Pm.map Pm.head (Pm.map Pm.tail (Pm.map Pm.tail xss)) ∷
      Pm.map Pm.tail (Pm.transpose (Pm.tail xs ∷ Pm.map Pm.tail (Pm.map Pm.tail (Pm.map Pm.tail xss))))
    ≡⟨ cong ( Pm.map Pm.head (Pm.map Pm.tail (Pm.map Pm.tail xss)) ∷_) (map-tail-trans xs (Pm.map Pm.tail xss)) ⟩
      refl

  transpose-head : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) n) →
                   Pm.map Pm.head (Pm.transpose (xs ∷ Pm.map Pm.tail xss)) ≡ xs
  transpose-head {n} {zero} [] xss = refl
  transpose-head {n} {suc m} (x ∷ xs) xss =
    begin
      x ∷ Pm.map Pm.head (Pm.transpose (xs ∷ Pm.map Pm.tail (Pm.map Pm.tail xss)))
    ≡⟨ cong (x ∷_) (transpose-head {n} {m} xs (Pm.map Pm.tail xss)) ⟩
      refl

  transpose-tail : {n m : ℕ} → {t : Set} → (xs : Vec t m) → (xss : Vec (Vec t (suc m)) n) →
                   Pm.map Pm.head xss ∷ Pm.map Pm.tail (Pm.transpose (xs ∷ Pm.map Pm.tail xss)) ≡ Pm.transpose xss
  transpose-tail {zero} {m} xs [] =
    begin
      [] ∷ Pm.map Pm.tail (Pm.transpose (xs ∷ []))
    ≡⟨ cong ([] ∷_) (fill-empty₂ xs) ⟩
      refl
  transpose-tail {suc n} {zero} [] xss = refl
  transpose-tail {suc n} {suc m} xs xss =
    begin
      Pm.map Pm.head xss ∷
      Pm.map Pm.head (Pm.map Pm.tail xss) ∷
      Pm.map Pm.tail (Pm.transpose (Pm.tail xs ∷ Pm.map Pm.tail (Pm.map Pm.tail xss)))
    ≡⟨ cong (Pm.map Pm.head xss ∷_) (cong (Pm.map Pm.head (Pm.map Pm.tail xss) ∷_) (map-tail-trans xs xss)) ⟩
      refl

  -- (Aᵀ)ᵀ ≡ A
  identity₃ : {n m : ℕ} → {t : Set} → (xss : Vec (Vec t m) n) →
              Pm.transpose (Pm.transpose xss) ≡ xss
  identity₃ {suc n} {zero} ([] ∷ xss) =
    begin
      [] ∷ Pm.fill n []
    ≡⟨ cong ([] ∷_) (fill-empty xss) ⟩
      refl
  identity₃ {zero} {m} [] =
    begin
      Pm.transpose (fill _ [])
    ≡⟨ empty (Pm.transpose (Pm.fill _ [])) ⟩
      refl
  identity₃ {suc n} {suc m} ((x ∷ xs) ∷ xss) =
    begin
      (x ∷ Pm.map Pm.head (Pm.transpose (xs ∷ Pm.map Pm.tail xss))) ∷
      Pm.transpose (Pm.map Pm.head xss ∷ Pm.map Pm.tail (Pm.transpose (xs ∷ Pm.map Pm.tail xss)))
    ≡⟨ cong (_∷ Pm.transpose (Pm.map Pm.head xss ∷ Pm.map Pm.tail (Pm.transpose (xs ∷ Pm.map Pm.tail xss))))
       (cong (x ∷_) (transpose-head xs xss)) ⟩
      (x ∷ xs) ∷ Pm.transpose (Pm.map Pm.head xss ∷ Pm.map Pm.tail (Pm.transpose (xs ∷ Pm.map Pm.tail xss)))
    ≡⟨ cong (λ yss → (x ∷ xs) ∷ Pm.transpose yss) (transpose-tail xs xss) ⟩
      (x ∷ xs) ∷ Pm.transpose (Pm.transpose xss)
    ≡⟨ cong ((x ∷ xs) ∷_) (identity₃ xss) ⟩
      refl

  {- Fusion rules -}
  fusion₁ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} → (f : t → r) → (g : s → t) → (xs : Vec s n) →
            (Pm.map f ∘ Pm.map g) xs ≡ Pm.map (f ∘ g) xs
  fusion₁ f g [] =
    begin
      (Pm.map f ∘ Pm.map g) []
    ≡⟨⟩
      Pm.map f (Pm.map g [])
    ≡⟨⟩
      Pm.map f []
    ≡⟨⟩
      []
    ≡⟨⟩
      Pm.map (f ∘ g) []
    ∎

  fusion₁ f g (x ∷ xs) =
    begin
      (Pm.map f ∘ Pm.map g) (x ∷ xs)
    ≡⟨⟩
      Pm.map f (Pm.map g (x ∷ xs))
    ≡⟨⟩
      Pm.map f (g x ∷ Pm.map g xs)
    ≡⟨⟩
      f (g x) ∷ Pm.map f (Pm.map g xs)
    ≡⟨⟩
      (f ∘ g) x ∷ Pm.map f (Pm.map g xs)
    ≡⟨ cong ((f ∘ g) x ∷_ ) (fusion₁ f g xs) ⟩
      (f ∘ g) x ∷ Pm.map (f ∘ g) xs
    ∎

  fusion₂ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} →
            (f : s → t) → (bf : t → r → r) → (init : r) → (xs : Vec s n) →
            Pm.reduceSeq (λ (a : s) (b : r) → (bf (f a) b)) init xs ≡ (Pm.reduceSeq bf init ∘ Pm.map f) xs
  fusion₂ f bf init [] = refl
  fusion₂ f bf init (x ∷ xs) =
    begin
      Pm.reduceSeq (λ a → bf (f a)) (bf (f x) init) xs
    ≡⟨ fusion₂ f bf (bf (f x) init) xs ⟩
      Pm.reduceSeq bf (bf (f x) init) (Pm.map f xs)
    ≡⟨⟩
      (Pm.reduceSeq bf init ∘ Pm.map f) (x ∷ xs)
    ∎

  {- Simplification rules -}
  simplification₁ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n * m)) →
                    (Pm.join ∘ Pm.split n {m}) xs ≡ xs
  simplification₁ n {zero} [] = refl
  simplification₁ n {suc m} xs =
    begin
      Pm.take n xs ++ Pm.join (Pm.split n {m} (Pm.drop n xs))
    ≡⟨ cong (Pm.take n xs ++_) (simplification₁ n {m} (Pm.drop n xs)) ⟩
      Pm.take n xs ++ Pm.drop n xs
    ≡⟨ take-drop n xs ⟩
      refl

  simplification₂ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec (Vec t n) m) →
                    (Pm.split n ∘ Pm.join) xs ≡ xs
  simplification₂ n {zero} [] = refl
  simplification₂ n {suc m} (xs ∷ xs₁) =
    begin
      Pm.take n (xs ++ Pm.join xs₁) ∷ Pm.split n (Pm.drop n (xs ++ Pm.join xs₁))
    ≡⟨ cong (_∷ Pm.split n (Pm.drop n (xs ++ Pm.join xs₁))) (take-++ n xs (Pm.join xs₁)) ⟩
      xs ∷ Pm.split n (Pm.drop n (xs ++ Pm.join xs₁))
    ≡⟨ cong (xs ∷_) (cong (Pm.split n) (drop-++ n xs (Pm.join xs₁))) ⟩
      xs ∷ Pm.split n (Pm.join xs₁)
    ≡⟨ cong (xs ∷_) (simplification₂ n xs₁) ⟩
      refl

  {- Split-join rule -}
  splitJoin : {m : ℕ} → {s : Set} → {t : Set} →
              (n : ℕ) → (f : s → t) → (xs : Vec s (n * m)) →
              (Pm.join ∘ Pm.map (Pm.map f) ∘ Pm.split n {m}) xs ≡ Pm.map f xs
  splitJoin {m} n f xs =
    begin
      (Pm.join ∘ Pm.map (Pm.map f) ∘ Pm.split n {m}) xs
    ≡⟨⟩
      Pm.join (Pm.map (Pm.map f) (Pm.split n {m} xs))
    ≡⟨ cong Pm.join (map-split n {m} f xs) ⟩
      Pm.join (Pm.split n {m} (Pm.map f xs))
    ≡⟨ simplification₁ n {m} (Pm.map f xs) ⟩
      Pm.map f xs
    ∎

  {- Reduction -}
  reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (n * suc m)) →
              (Pm.reduce M ∘ Pm.partRed n {m} M) xs ≡ Pm.reduce M xs
  reduction {zero} zero M [] = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.reduce M [ ε ]
    ≡⟨⟩
      ε ⊕ ε
    ≡⟨ idʳ M ε ⟩
      refl
  reduction {zero} (suc n) M xs = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.reduce M [ Pm.reduce M xs ]
    ≡⟨⟩
      (Pm.reduce M xs) ⊕ ε
    ≡⟨ idʳ M (Pm.reduce M xs) ⟩
      refl
  reduction {suc m} zero M [] = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.reduce M (ε ∷ Pm.partRed zero {m} M [])
    ≡⟨⟩
      Pm.reduceSeq _⊕_ (ε ⊕ ε) (Pm.partRed zero {m} M [])
    ≡⟨ cong (λ y → Pm.reduceSeq _⊕_ y (Pm.partRed zero {m} M [])) (idʳ M ε) ⟩
      Pm.reduce M (Pm.partRed zero {m} M [])
    ≡⟨ reduction {m} zero M [] ⟩
      refl
  reduction {suc m} (suc n) M xs = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.reduce M ([ Pm.reduce M (take (suc n) {suc (m + (n + n * m))} xs) ] ++ Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))
    ≡⟨ sym (reduce-++ M [ Pm.reduce M (take (suc n) {suc (m + (n + n * m) )} xs) ] (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))) ⟩
      Pm.reduce M [ Pm.reduce M (take (suc n) {suc (m + (n + n * m))} xs) ] ⊕ Pm.reduce M (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))
    ≡⟨ cong (_⊕ Pm.reduce M (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))) (idʳ M (Pm.reduce M (Pm.take (suc n) {suc (m + (n + n * m))} xs))) ⟩
      Pm.reduce M (Pm.take (suc n) {suc (m + (n + n * m))} xs) ⊕ Pm.reduce M (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))
    ≡⟨ cong (Pm.reduce M (Pm.take (suc n) {suc (m + (n + n * m))} xs) ⊕_) (reduction {m} (suc n) M (Pm.drop (suc n) xs)) ⟩
      Pm.reduce M (Pm.take (suc n) {suc (m + (n + n * m))} xs) ⊕ Pm.reduce M (Pm.drop (suc n) {suc (m + (n + n * m))} xs)
    ≡⟨ sym (reduce-take-drop (suc n) {suc (m + (n + n * m))} M xs) ⟩
      refl

  {- Partial Reduction -}
  partialReduction₁ : {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t n)  →
                      Pm.partRed n M xs ≡ [ Pm.reduce M xs ]
  partialReduction₁ zero M [] = refl
  partialReduction₁ (suc n) M xs = refl

  partialReduction₂ : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (n * suc m)) →
                      (Pm.join ∘ Pm.map (Pm.partRed n {zero} M) ∘ Pm.split n {suc m}) xs ≡ Pm.partRed n {m} M xs
  partialReduction₂ {zero} zero M [] = refl
  partialReduction₂ {zero} (suc n) M xs =
    begin
      [ Pm.reduce M (Pm.take (suc n) {zero} xs) ]
    ≡⟨ cong (λ ys → [ (Pm.reduce M) ys ]) (take-all (suc n) xs ) ⟩
      refl
  partialReduction₂ {suc m} zero M [] = let _⊕_ = _⊕_ M; ε = ε M in
    begin
      Pm.join (Pm.map (Pm.partRed zero {zero} M) (Pm.split zero {suc (suc m)} []))
    ≡⟨⟩
      ε ∷ Pm.join (Pm.map (Pm.partRed zero {zero} M) (Pm.split zero {suc m} []))
    ≡⟨ cong (λ ys → (ε ∷ ys)) (map-join-partRed {m} zero M (Pm.split zero {suc m} [])) ⟩
      ε ∷ Pm.partRed zero {m} M (Pm.join {zero} {suc m} (Pm.split zero []))
    ≡⟨ cong (λ ys → (ε ∷ Pm.partRed zero {m} M ys)) (simplification₁ zero {m} []) ⟩
      refl
  partialReduction₂ {suc m} (suc n) M xs =
    begin
      Pm.join (Pm.map (Pm.partRed (suc n) {zero} M) (Pm.split (suc n) {suc (suc m)} xs))
    ≡⟨ map-join-partRed {suc m} (suc n) M (Pm.split (suc n) {suc (suc m)} xs) ⟩
      Pm.partRed (suc n) {suc m} M (Pm.join {suc n} (Pm.split (suc n) {suc (suc m)} xs))
    ≡⟨ cong (Pm.partRed (suc n) M) (simplification₁ (suc n) {suc (suc m)} xs) ⟩
      refl

  {- Tiling -}
  -- u = 2 * sz
  slide-join : {n : ℕ} → {t : Set} → (sz : ℕ) → (sp : ℕ) → (xs : Vec t (sz + n * suc sp)) →
               Pm.slide {n} sz sp xs ≡
               Pm.join (Pm.map (λ (tile : Vec t (2 * sz)) → Pm.slide {{!!}} sz sp tile) (Pm.slide (2 * sz) (sz + sp) xs) )
  slide-join = {!!}
