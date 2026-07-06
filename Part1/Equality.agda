module Part1.Equality where

data _≡_ {A : Set} (x : A) : A → Set where 
    refl : x ≡ x

infix 4 _≡_

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x 
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z 
trans refl refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong-app : {A B : Set} {f g : A → B} → f ≡ g → ∀(x : A) → f x ≡ g x 
cong-app refl x = refl 

subst : {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl Px = Px

-- Reasoning module 
module ≡-Reasoning {A : Set} where 

    infix 1 proof_ 
    infixr 2 step-≡-| step-≡-⟩ 
    infix 3 _∎ 

    proof_ : {x y : A} → x ≡ y → x ≡ y 
    proof x=y = x=y 

    step-≡-| : ∀ (x : A) {y : A} → x ≡ y → x ≡ y 
    step-≡-| x x=y = x=y 

    step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z 
    step-≡-⟩ x y=z x=y = trans x=y y=z

    _∎ : ∀ (x : A) → x ≡ x 
    x ∎ = refl 

    syntax step-≡-| x x=y = x ≡⟨⟩ x=y
    syntax step-≡-⟩ x y=z x=y = x ≡⟨ x=y ⟩ y=z

open ≡-Reasoning

trans' : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z 
trans' {A} {x} {y} {z} x=y y=z = 
    proof 
        x 
    ≡⟨ x=y ⟩ 
        y 
    ≡⟨ y=z ⟩ 
        z 
    ∎ 

data ℕ : Set where
    zero : ℕ 
    suc : ℕ → ℕ 

_+_ : ℕ → ℕ → ℕ 
zero + y = y
suc x + y = suc (x + y)

postulate 
    +-id : ∀ (n : ℕ) → n + zero ≡ n 
    +-suc : ∀ (n m : ℕ) → n + (suc m) ≡ suc (n + m)

+-comm : ∀ (n m : ℕ) → n + m ≡ m + n 
+-comm n zero = +-id n
+-comm n (suc m) = proof 
                        n + suc m 
                    ≡⟨ +-suc n m ⟩ 
                        suc (n + m)
                    ≡⟨ cong suc (+-comm n m) ⟩ 
                        suc (m + n) 
                    ≡⟨⟩ 
                        suc m + n 
                    ∎

module ≤-Reasoning where 

    data _≤_ : ℕ → ℕ → Set where 
        z≤n : {n : ℕ} →  zero ≤ n  
        s≤s : {n m : ℕ} → n ≤ m → (suc n) ≤ (suc m)
    infix 4 _≤_

    ≤-trans : {n m k : ℕ} → n ≤ m → m ≤ k → n ≤ k 
    ≤-trans z≤n m≤k = z≤n
    ≤-trans (s≤s n≤m) (s≤s m≤k) = s≤s (≤-trans n≤m m≤k) 

    -- ≤-cong : ∀ (f : ℕ → ℕ) {n m : ℕ} → n ≤ m → f n ≤ f m 
    -- ≤-cong f z≤n = {!   !}
    -- ≤-cong f (s≤s n≤m) = {!   !}

    n≤n : {n : ℕ} → n ≤ n 
    n≤n {zero} = z≤n
    n≤n {suc n} = s≤s n≤n
    
    infix 1 begin-≤_ 
    infixr 2 step-≤-| step-≤-⟩ 
    infix 3 _end-≤ 

    begin-≤_ : {x y : ℕ} → x ≤ y → x ≤ y 
    begin-≤ x≤y = x≤y

    step-≤-| : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y 
    step-≤-| x x≤y = x≤y 

    step-≤-⟩ : ∀ (x : ℕ) {y z : ℕ} → y ≤ z → x ≤ y → x ≤ z 
    step-≤-⟩ x y≤z x≤y = ≤-trans x≤y y≤z

    _end-≤ : ∀ (n : ℕ) → n ≤ n 
    n end-≤ = n≤n

    syntax step-≤-⟩ x y≤z x≤y = x ≤⟨ x≤y ⟩ y≤z  

open ≤-Reasoning 

=-≤ : {n m : ℕ} → n ≡ m → n ≤ m 
=-≤ refl = n≤n

+-≤-monoᴸ : {n m k : ℕ} → n ≤ m → n + k ≤ m + k 
+-≤-monoᴸ {n} {m} {zero} n≤m = 
    begin-≤ 
        n + zero
    ≤⟨ =-≤ (+-id n) ⟩ 
        n 
    ≤⟨ n≤m ⟩ 
        m 
    ≤⟨ =-≤ (sym (+-id m)) ⟩ 
        m + zero
    end-≤ 
+-≤-monoᴸ {n} {m} {k = suc k} n≤m = 
    begin-≤ 
        n + (suc k) 
    ≤⟨ =-≤ (+-suc n k) ⟩ 
        suc (n + k)
    ≤⟨ s≤s (+-≤-monoᴸ n≤m) ⟩ 
        suc (m + k) 
    ≤⟨ =-≤ (sym (+-suc m k)) ⟩ 
        m + (suc k)
    end-≤ 

-- other cases also interesting but it serves the purpose 


-- Rewriting 
data even : ℕ → Set 
data odd  : ℕ → Set 

data even where 
    zero : even zero 
    suc  : {n : ℕ} → odd n → even (suc n) 

data odd where 
    suc : {n : ℕ} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (n m : ℕ) → even (n + m) → even (m + n)
even-comm n m ev rewrite +-comm n m = ev

_≐_ : {A : Set} (x y : A) → Set₁ 
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

≐-refl : {A : Set} {x : A} → x ≐ x 
≐-refl P Px = Px

≐-trans : {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z 
≐-trans x=y y=z P Px =  y=z P (x=y P Px)

≐-sym : {A : Set} {x y : A} → x ≐ y → y ≐ x 
≐-sym {A} {x} {y} x=y P = x=y Q (≐-refl P) 
    where 
    Q : A → Set 
    Q z = P z → P x 

≡-→-≐ : {A : Set} → {x y : A} → x ≡ y → x ≐ y 
≡-→-≐ x=y P = subst P x=y

≐-→-≡ : {A : Set} → {x y : A} → x ≐ y → x ≡ y 
≐-→-≡ {A} {x} {y} x=y = x=y Q refl
    where 
        Q : A → Set 
        Q z = x ≡ z 

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡'_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where 
    refl' : x ≡' x 

sym' : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡' y → y ≡' x 
sym' refl' = refl'

_≐'_ : {ℓ : Level} {A : Set ℓ} {x y : A} → Set (lsuc ℓ)
_≐'_ {ℓ} {A} {x} {y} = ∀ (P : A → Set ℓ) → P x → P y 

_∘_ : {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃} → (B → C) → (A → B) → (A → C)
f ∘ g = λ x  → f (g x) 



