# Defined Primitives and Proven Rewrite Rules

## Primitives
### Module
Source: `/individual-project/src/lift/Primitives.adga`
```agda
module lift.Primitives where
  ...
```
### definied primitives
* id
```agda
id : {T : Set} → T → T
```
* map
```agda
map : {n : ℕ} → {s : Set} → {t : Set} → (s → t) → Vec s n → Vec t n
```
* take
```agda
take : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t n
```
* drop
```agda
drop : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n + m) → Vec t m
```
* split
```agda
split : (n : ℕ) → {m : ℕ} → {t : Set} → Vec t (n * m) → Vec (Vec t n) m
```
* join
```agda
join : {n m : ℕ} → {t : Set} → Vec (Vec t n) m → Vec t (n * m)
```
* slide
```agda
slide : {n : ℕ} → (sz : ℕ) → (sp : ℕ)→ {t : Set} → Vec t (sz + n * (suc sp)) → Vec (Vec t sz) (suc n)
```
* reduceSeq
```agda
reduceSeq : {n : ℕ} → {s t : Set} → (s → t → t) → t → Vec s n → t
```
* reduce
```agda
reduce : {n : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t n → t
```
* partRed
```agda
partRed : (n : ℕ) → {m : ℕ} → {t : Set} → (M : CommAssocMonoid t) → Vec t (suc m * n) → Vec t (suc m)
```
* zip
```agda
zip : {n : ℕ} → {s : Set} → {t : Set} → Vec s n → Vec t n → Vec (s × t) n
```
* unzip
```agda
unzip : ((x , y) ∷ xs) = Prod.zip _∷_ _∷_ (x , y) (unzip xs)
```
## Rewrite Rules
### Module
Source: `/individual-project/src/lift/AlgorithmicRules.adga`
```agda
module lift.AlgorithmicRules where
  ...
```
### Proven Rewrite Rules
* Identity Rules
  - Option 1
  ```adga
  identity₁ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (f ∘ Pm.map Pm.id) xs ≡ f xs
  ```
  - Option 2
  ```agda
  identity₂ : {n : ℕ} → {s : Set} → {t : Set} → (f : Vec s n → Vec t n) → (xs : Vec s n) →
              (Pm.map Pm.id ∘ f) xs ≡ f xs
  ```

* Fusion Rules
  - Option 1
  ```adga
  fusion₁ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} → (f : t → r) → (g : s → t) → (xs : Vec s n) →
            (Pm.map f ∘ Pm.map g) xs ≡ Pm.map (f ∘ g) xs
  ```
  - Option 2
  ```agda
  fusion₂ : {n : ℕ} → {s : Set} → {t : Set} → {r : Set} →
            (f : s → t) → (bf : t → r → r) → (init : r) → (xs : Vec s n) →
            Pm.reduceSeq (λ (a : s) (b : r) → (bf (f a) b)) init xs ≡ (Pm.reduceSeq bf init ∘ Pm.map f) xs
  ```

* Simplification Rules
  - Option 1
  ```adga
  simplification₁ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec t (n * m)) →
                    (Pm.join ∘ Pm.split n {m}) xs ≡ xs
  ```
  - Option 2
  ```agda
  simplification₂ : (n : ℕ) → {m : ℕ} → {t : Set} → (xs : Vec (Vec t n) m) →
                    (Pm.split n ∘ Pm.join) xs ≡ xs
  ```

* Split-join Rule
```agda
splitJoin : {m : ℕ} → {s : Set} → {t : Set} →
              (n : ℕ) → (f : s → t) → (xs : Vec s (n * m)) →
              (Pm.join ∘ Pm.map (Pm.map f) ∘ Pm.split n {m}) xs ≡ Pm.map f xs
```

* Reduction Rule
```agda
reduction : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (suc m * n)) →
              (Pm.reduce M ∘ Pm.partRed n {m} M) xs ≡ Pm.reduce M xs
```

* Partial Reduction Rules
  - Option 1
  ```adga
  partialReduction₁ : {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t n)  →
                      Pm.partRed n M xs ≡ [ Pm.reduce M xs ]
  ```
  - Option 2
  ```agda
  partialReduction₂ : {m : ℕ} → {t : Set} → (n : ℕ) → (M : CommAssocMonoid t) → (xs : Vec t (n * suc m)) →
                      (Pm.join ∘ Pm.map (Pm.partRed n {zero} M) ∘ Pm.split n {suc m}) xs ≡ Pm.partRed n {m} M xs
  ```
