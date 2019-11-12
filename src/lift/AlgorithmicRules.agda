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


  {- lemmas -}
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

  map-take : (n : ℕ) → {m : ℕ} → {s t : Set} → (f : s → t) → (xs : Vec s (n + m)) →
             Pm.map f (Pm.take n {m} xs) ≡  (Pm.take n {m} (Pm.map f xs))
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

  -- The reduction rule
  reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
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
      Pm.reduce M ([ Pm.reduce M (take (suc n) {suc (n + m + m * n)} xs) ] ++ Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))
    ≡⟨ sym (reduce-++ M [ Pm.reduce M (take (suc n) {suc (n + m + m * n)} xs) ] (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))) ⟩
      Pm.reduce M [ Pm.reduce M (take (suc n) {suc (n + m + m * n)} xs) ] ⊕ Pm.reduce M (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))
    ≡⟨ cong (_⊕ Pm.reduce M (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))) (idʳ M (Pm.reduce M (Pm.take (suc n) {suc (n + m + m * n)} xs))) ⟩
      Pm.reduce M (Pm.take (suc n) {suc (n + m + m * n)} xs) ⊕ Pm.reduce M (Pm.partRed (suc n) {m} M (Pm.drop (suc n) xs))
    ≡⟨ cong (Pm.reduce M (Pm.take (suc n) {suc (n + m + m * n)} xs) ⊕_) (reduction {m} (suc n) M (Pm.drop (suc n) xs)) ⟩
      Pm.reduce M (Pm.take (suc n) {suc (n + m + m * n)} xs) ⊕ Pm.reduce M (Pm.drop (suc n) {suc (n + m + m * n)} xs)
    ≡⟨ sym (reduce-take-drop (suc n) {suc (n + m + m * n)} M xs) ⟩
      refl

  {- Partial Reduction -}
  partialReduction₁ : {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t n)  →
                      Pm.partRed n M xs ≡ [ Pm.reduce M xs ]
  partialReduction₁ zero M [] = refl
  partialReduction₁ (suc n) M xs = refl

  {-
  take-++′ : (n : ℕ) → {m o : ℕ} → {t : Set} → (xs : Vec t (n + m)) → (xs₁ : Vec t o) →
             Pm.take n {m} xs ≡ Pm.take n {m + o} (xs ++ xs₁)
  take-++′ zero {m} {o} xs xs₁ = refl
  take-++′ (suc n) {m} {o} (x ∷ xs) xs₁ =
    begin
      x ∷ Pm.take n {m} xs
    ≡⟨ cong (x ∷_) (take-++′ n {m} {o} xs xs₁) ⟩
      refl

  drop-++′ : (n : ℕ) → {m o : ℕ} → {t : Set} → (xs : Vec t (n + m)) → (xs₁ : Vec t o) →
             Pm.drop n {m} xs ++ xs₁ ≡ Pm.drop n {m + o} (xs ++ xs₁)
  drop-++′ zero {m} {o} xs xs₁ = refl
  drop-++′ (suc n) {m} {o} (x ∷ xs) xs₁ =
    begin
      Pm.drop n {m} xs ++ xs₁
    ≡⟨ drop-++′ n {m} {o} xs xs₁ ⟩
      refl

  partRed-++ : {m o : ℕ} → {t : Set} → (n : ℕ) → (f : t → t → t) → (xs₁ : Vec t (m * suc n)) → (xs₂ : Vec t (o * suc n)) →
               Pm.partRed n {m} f xs₁ ++ Pm.partRed n {o} f xs₂ ≡ Pm.partRed n {(m + o)} f (xs₁ ++ xs₂)
  partRed-++ {zero} {o} n f [] xs₂ = refl
  partRed-++ {suc m} {o} {t} n f xs₁ xs₂ =
    begin
      Pm.reduce′ f (Pm.take (suc n) {(m + m * n)} xs₁) ∷ Pm.partRed n {m} f (drop (suc n) xs₁) ++ Pm.partRed n {o} f xs₂
    ≡⟨ cong (Pm.reduce′ f (Pm.take (suc n) {(m + m * n)} xs₁) ∷_) (partRed-++ {m} {o} n f (drop (suc n) xs₁) xs₂) ⟩
      Pm.reduce′ f (Pm.take (suc n) {(m + m * n)} xs₁) ∷ Pm.partRed n f (Pm.drop (suc n) {(m + m * n)} xs₁ ++ xs₂)
    ≡⟨ cong (λ y → Pm.reduce′ f y ∷ Pm.partRed n f (Pm.drop (suc n) {(m + m * n)} xs₁ ++ xs₂)) (take-++′ (suc n) {(m + m * n)} {(o * suc n)} xs₁ xs₂) ⟩
      Pm.reduce′ f (Pm.take (suc n) {(m + m * n) + (o * suc n)} (xs₁ ++ xs₂)) ∷ Pm.partRed n f (Pm.drop (suc n) xs₁ ++ xs₂)
    ≡⟨ cong (λ ys → Pm.reduce′ f (Pm.take (suc n) {(m + m * n) + (o * suc n)} (xs₁ ++ xs₂)) ∷ Pm.partRed n f ys) (drop-++′ (suc n) xs₁ xs₂ )⟩
      refl

  partRed-take-drop : {m : ℕ} → {t : Set} → (n : ℕ) → (f : t → t → t) → (xs : Vec t ((suc m) * (suc n))) →
                      Pm.partRed n {1} f (Pm.take (suc n) {(m + m * n)} xs) ++ Pm.partRed n {m} f (Pm.drop (suc n) xs)
                      ≡ Pm.partRed n {suc m} f xs
  partRed-take-drop {m} n f xs =
    begin
      Pm.partRed n {1} f (take (suc n) {(m + m * n)} xs) ++ Pm.partRed n {m} f (Pm.drop (suc n) xs)
    ≡⟨ partRed-++ {1} {m} n f (take (suc n) {(m + m * n)} xs) (Pm.drop (suc n) xs) ⟩
      Pm.partRed n {(suc m)} f (Pm.take (suc n) {(m + m * n)} xs ++ Pm.drop (suc n) {(m + m * n)} xs)
    ≡⟨ cong (Pm.partRed n {(suc m)} f) (take-drop (suc n) {(m + m * n)} xs) ⟩
      refl
  -}
  {- the second option of partial reduction -}
  take-all : (n : ℕ) → {t : Set} → (xs : Vec t n) →
              Pm.take n {zero} xs ≡ xs
  take-all zero [] = refl
  take-all (suc n) (x ∷ xs) =
    begin
      x ∷ Pm.take n xs
    ≡⟨ cong (x ∷_) (take-all n xs) ⟩
      refl

  map-join-partRed : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
                     Pm.join (Pm.map (Pm.partRed n {zero} M) (Pm.split n {suc m} xs)) ≡ Pm.partRed n {m} M (Pm.join {n} {suc m} (Pm.split n xs))
  map-join-partRed = {!!}

  partialReduction₂ : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
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
    ≡⟨ cong (λ ys → (ε ∷ ys)) (map-join-partRed {m} zero M []) ⟩
      ε ∷ Pm.partRed zero {m} M (Pm.join {zero} {suc m} (Pm.split zero []))
    ≡⟨ cong (λ ys → (ε ∷ Pm.partRed zero {m} M ys)) (simplification₁ zero {m} []) ⟩
      refl
  -- TODO
  partialReduction₂ {suc m} {t} (suc n) M xs = {!!}

  {-
  partialReduction₂ {zero} n f [] = refl
  partialReduction₂ {suc m} n f xs =
    begin
      Pm.partRed n {1} f (Pm.take (suc n) {(m + m * n)} xs) ++
      Pm.join (Pm.map (Pm.partRed n {1} f) (Pm.split (suc n) {m} (Pm.drop (suc n) xs)))
    ≡⟨ cong (Pm.partRed n {1} f (Pm.take (suc n) {(m + m * n)} xs) ++_) (partialReduction₂ {m} n f (Pm.drop (suc n) xs) ) ⟩
      Pm.partRed n {1} f (Pm.take (suc n) {(m + m * n)} xs) ++ Pm.partRed n {m} f (Pm.drop (suc n) xs)
    ≡⟨ partRed-take-drop {m} n f xs ⟩
      refl
  -}
  {- Tiling -}
  map-join : {s : Set} → {t : Set} → {m n : ℕ} →
             (f : s → t) → (xs : Vec (Vec s n) m) →
             Pm.map f (Pm.join xs) ≡ Pm.join (Pm.map (Pm.map f) xs)
  map-join f [] = refl
  map-join f (xs ∷ xs₁) =
    begin
      Pm.map f (xs ++ Pm.join (xs₁))
    ≡⟨ map-++ f xs (Pm.join xs₁) ⟩
      Pm.map f xs ++ Pm.map f (Pm.join xs₁)
    ≡⟨ cong (Pm.map f xs ++_) (map-join f xs₁) ⟩
      refl
