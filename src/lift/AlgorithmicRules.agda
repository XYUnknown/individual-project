{-# OPTIONS --allow-unsolved-metas #-}
{- TODO: remove the pragma when all the holes are filled -}
{-# OPTIONS --rewriting --prop #-}
module lift.AlgorithmicRules where
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; sym; subst; cong₂)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
  open import Data.Product using (∃₂; _,_)
  open import Data.Vec using (Vec; _∷_; []; [_]; _++_)
  open import Function using (_∘_)
  import lift.Primitives as Pm
  open Pm

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
  -- TODO: better way to declare this abstract binary operator with cerntain properties?
  {-
  record AssocCommBinOp {t : Set} : Set where
    field
      _⊕_ : t → t → t
      comm : ∀ x y → x ⊕ y ≡ y ⊕ x
      assoc : ∀ x y z → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)
    infixl 6 _⊕_
  open AssocCommBinOp
  -}

  -- an arbitrary operator which is associative and commutative
  postulate _⊕_ : {t : Set} → t → t → t
  postulate ⊕-comm : {t : Set} → ∀ (x y : t) → x ⊕ y ≡ y ⊕ x
  postulate ⊕-assoc : {t : Set} → ∀ (x y z : t) → (x ⊕ y) ⊕ z ≡ x ⊕ (y ⊕ z)

  reduce′-assoc : {n : ℕ} → {t : Set} → (init : t) → (x : t) → (xs : Vec t (suc n)) →
    (Pm.reduce′ _⊕_ (x ∷ xs)) ⊕ init ≡ (Pm.reduce′ _⊕_ xs) ⊕ (x ⊕ init)
  reduce′-assoc init x (x₁ ∷ []) =
    begin
      Pm.reduce′ _⊕_ (x ∷ x₁ ∷ []) ⊕ init
    ≡⟨⟩
      Pm.reduceSeq _⊕_ (x₁ ⊕ x) [] ⊕ init
    ≡⟨⟩
      (x₁ ⊕ x) ⊕ init
    ≡⟨ ⊕-assoc x₁ x init ⟩
      x₁ ⊕ (x ⊕ init)
    ≡⟨⟩
      refl
  reduce′-assoc init x (x₁ ∷ x₂ ∷ xs) =
    begin
      Pm.reduceSeq _⊕_ (x₁ ⊕ x) (x₂ ∷ xs) ⊕ init
    ≡⟨ reduce′-assoc init (x₁ ⊕ x) (x₂ ∷ xs) ⟩
      Pm.reduce′ _⊕_ (x₂ ∷ xs) ⊕ ((x₁ ⊕ x) ⊕ init)
    ≡⟨ cong (Pm.reduce′ _⊕_ (x₂ ∷ xs) ⊕_) (⊕-assoc x₁ x init) ⟩
      Pm.reduce′ _⊕_ (x₂ ∷ xs) ⊕ (x₁ ⊕ (x ⊕ init))
    ≡⟨ sym (reduce′-assoc (x ⊕ init) x₁ (x₂ ∷ xs)) ⟩
      refl

  reduce≡reduce′ : {n : ℕ} → {t : Set} → (init : t) → (xs : Vec t (suc n)) →
                 Pm.reduce _⊕_ init xs ≡ _⊕_ (Pm.reduce′ _⊕_ xs) init
  reduce≡reduce′ init (x ∷ []) = refl
  reduce≡reduce′ init (x ∷ x₁ ∷ xs) =
    begin
      Pm.reduce _⊕_ (x ⊕ init) (x₁ ∷ xs)
    ≡⟨ reduce≡reduce′ (x ⊕ init) (x₁ ∷ xs) ⟩
      (Pm.reduce′ _⊕_ (x₁ ∷ xs)) ⊕ (x ⊕ init)
    ≡⟨ sym (reduce′-assoc init x (x₁ ∷ xs)) ⟩
      refl

  reduce-++ : {n m : ℕ} → {t : Set} → (f : t → t → t) → (init : t) → (xs₁ : Vec t n) → (xs₂ : Vec t m) →
              Pm.reduce f init (xs₁ ++ xs₂) ≡ Pm.reduce f (Pm.reduce f init xs₁) xs₂
  reduce-++ f init [] xs₂ = refl
  reduce-++ f init (x ∷ xs₁) xs₂ =
    begin
      Pm.reduce f (f x init) (xs₁ ++ xs₂)
    ≡⟨ reduce-++ f (f x init) xs₁ xs₂ ⟩
      refl

  reduce-take-drop : (n : ℕ) → {m : ℕ} → {t : Set} → (init : t) → (xs : Vec t (suc n + m)) →
    Pm.reduce _⊕_ init xs ≡ Pm.reduce  _⊕_ (_⊕_ (Pm.reduce′ _⊕_ (Pm.take (suc n) {m} xs)) init) (Pm.drop (suc n) {m} xs)
  reduce-take-drop n {m} init xs =
    begin
      Pm.reduce _⊕_ init xs
    ≡⟨ cong (Pm.reduce _⊕_ init) (sym (take-drop (suc n) {m} xs)) ⟩
      Pm.reduce _⊕_ init (Pm.take (suc n) {m} xs ++ Pm.drop (suc n) xs)
    ≡⟨ reduce-++ _⊕_ init (Pm.take (suc n) {m} xs) (Pm.drop (suc n) xs) ⟩
      Pm.reduce _⊕_ (Pm.reduce _⊕_ init (Pm.take (suc n) {m} xs)) (Pm.drop (suc n) {m} xs)
    ≡⟨ cong (λ ys → Pm.reduce _⊕_ ys (Pm.drop (suc n) {m} xs)) (reduce≡reduce′ init (Pm.take (suc n) {m} xs)) ⟩
      Pm.reduce _⊕_ (_⊕_ (Pm.reduce′ _⊕_ (Pm.take (suc n) {m} xs)) init) (Pm.drop (suc n) {m} xs)
    ∎

  -- The reduction rule
  reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (init : t) → (xs : Vec t (m * (suc n))) →
               (Pm.reduce _⊕_ init ∘ Pm.partRed n {m} _⊕_) xs ≡ Pm.reduce _⊕_ init xs
  reduction {zero} n init [] = refl
  reduction {suc m} n init xs =
    begin
      Pm.reduce _⊕_ init ((Pm.reduce′ _⊕_ (Pm.take (suc n) {(m + m * n)} xs)) ∷ Pm.partRed n {m} _⊕_ (Pm.drop (suc n) xs))
    ≡⟨ reduction {m} n (_⊕_ (Pm.reduce′ _⊕_ (Pm.take (suc n) {(m + m * n)} xs)) init) ((Pm.drop (suc n) xs)) ⟩
      Pm.reduce _⊕_ (_⊕_ (Pm.reduce′ _⊕_ (Pm.take (suc n) {(m + m * n)} xs)) init) (Pm.drop (suc n) {(m + m * n)} xs)
    ≡⟨ sym (reduce-take-drop n {m + m * n} init xs) ⟩
      refl

  -- a test that the redution rule is working
  _ : (Pm.reduce _+_ 1 ∘ Pm.partRed 1 {2} _+_) (1 ∷ 1 ∷ 2 ∷ 2 ∷ []) ≡ Pm.reduce _+_ 1 (1 ∷ 1 ∷ 2 ∷ 2 ∷ [])
  _ = refl

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
