module Part1.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

-- {-# }

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = 
    begin
      (3 + 4) + 5
      ≡⟨ refl ⟩ 
      7 + 5
      ≡⟨ refl ⟩ 
      12
      ≡⟨ refl ⟩
      3 + 9 
      ≡⟨ refl ⟩ 
      3 + (4 + 5)
    ∎

+-assoc : {m n k : ℕ} → (m + n) + k ≡ m + (n + k)
+-assoc {zero} {n} {k} = 
    begin
      (zero + n) + k
  ≡⟨⟩
    n + k
  ≡⟨⟩
    zero + (n + k)
    ∎

+-assoc {(suc m)} {n} {k} = 
    begin 
        (suc m + n ) + k
        ≡⟨⟩ 
        suc (m + n) + k
        ≡⟨⟩
        suc ((m + n) + k)
        ≡⟨ cong suc (+-assoc {m} {n} {k}) ⟩
        suc (m + (n + k)) 
        ≡⟨⟩ 
        suc m + (n + k)
        ∎

leftId-0 : ∀ (n : ℕ) → zero + n ≡ n
leftId-0 zero = refl
leftId-0 (suc n) = cong suc refl

rightId-0 : ∀ (n : ℕ) → n + zero ≡ n
rightId-0 zero = refl 
rightId-0 (suc n) = cong suc (rightId-0 n)

+-suc : ∀  (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc zero m = 
  begin
    zero + suc m 
  ≡⟨ refl ⟩ 
    suc m
  ≡⟨ refl ⟩ 
    suc (zero + m) 
  ∎
+-suc (suc n) m =
  begin
    suc n + suc m
  ≡⟨ cong suc (+-suc n m) ⟩
    suc (suc (n + m))
  ≡⟨ refl ⟩ 
    suc ( (suc n) + m )
  ∎

+-comm : ∀ (n m : ℕ) → n + m ≡ m + n 
+-comm m zero = rightId-0 m
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩ 
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    (suc n) + m
  ∎

+-comm' : ∀ (n m : ℕ) → n + m ≡ m + n 
+-comm' zero m = sym (rightId-0 m)
+-comm' (suc n) m = 
  begin 
    suc n + m
  ≡⟨ refl ⟩ 
    suc (n + m) 
  ≡⟨ cong suc (+-comm' n m) ⟩ 
    suc (m + n)
  ≡⟨ sym (+-suc m n) ⟩ 
    m + suc n
  ∎  

+-rearrange : ∀ (x y z w : ℕ) → (x + y) + (z + w) ≡ x + (y + z) + w
+-rearrange x y z w = 
  begin 
    (x + y) + (z + w) 
  ≡⟨ sym (+-assoc {x + y} {z} {w})  ⟩
    ((x + y) + z) + w 
  ≡⟨ cong (_+ w) (+-assoc {x} {y} {z}) ⟩ 
    x + (y + z) + w 
  ∎

+-assoc' : ∀  (n m k : ℕ) → (n + m) + k ≡ n + (m + k)
+-assoc' zero m k = refl 
+-assoc' (suc n) m k rewrite +-assoc' n m k = refl

+-swap : ∀ (n m k : ℕ) → n + (m + k) ≡ m + (n + k) 
+-swap n m k = 
  begin 
    n + (m + k) 
  ≡⟨ sym (+-assoc' n m k) ⟩ 
    (n + m) + k
  ≡⟨ cong (_+ k) (+-comm n m) ⟩ 
    (m + n) + k
  ≡⟨ +-assoc' m n k ⟩ 
    m + (n + k)
  ∎

x*0=0 : ∀ (n : ℕ) → n * zero ≡ zero 
x*0=0 0 = refl 
x*0=0 (suc n) rewrite x*0=0 n = refl

0*x=0 : ∀ (n : ℕ) → zero * n ≡ zero 
0*x=0 0 = refl 
0*x=0 (suc n) rewrite 0*x=0 n = refl

*-distrib-+ : ∀ (n m k : ℕ) → (m + n) * k ≡ (m * k) + (n * k)
-- *-distrib-+ n m zero = 
--   begin 
--     (m + n) * zero 
--   ≡⟨ x*0=0 (m + n) ⟩ 
--     zero  
--   ≡⟨ sym (x*0=0 m) ⟩ 
--     m * zero
--   ≡⟨ {!   !} ⟩ 
--     m * zero + zero 
--   ≡⟨ {!   !} ⟩ 
--     m * zero +  n * zero 
--   ∎
-- *-distrib-+ n m (suc k) = {!   !}
*-distrib-+ zero m k =
  begin 
    (m + zero) * k 
  ≡⟨ cong (_* k) (rightId-0 m) ⟩ 
    m * k 
  ≡⟨ sym (rightId-0 (m * k)) ⟩ 
    (m * k) + zero 
  ∎
*-distrib-+ (suc n) m k = 
  begin 
    (m + (suc n)) * k 
  ≡⟨ cong (_* k) (+-suc m n) ⟩ 
    (suc (m + n)) * k
  ≡⟨ refl ⟩ 
    k + ((m + n) * k)
  ≡⟨ cong (k +_) (*-distrib-+ n m k) ⟩ 
    k + ( m * k + n * k)
  ≡⟨ +-swap k (m * k) (n * k) ⟩ 
    m * k + (suc n) * k 
  ∎

*-assoc : ∀ (n m k : ℕ) → (n * m) * k ≡ n * (m * k)
*-assoc zero m k = refl
*-assoc (suc n) m k = 
  begin 
    (suc n * m) * k 
  ≡⟨ refl ⟩ 
    (m + n * m) * k
  ≡⟨ *-distrib-+ (n * m) m k ⟩ 
    m * k + n * m * k 
  ≡⟨ cong (m * k +_) (*-assoc n m k) ⟩ 
    suc n * (m * k)
  ∎ 

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n 
*-suc zero n = refl
*-suc (suc m) n =
  begin
    suc (n + m * suc n)
  ≡⟨ cong (λ (k : ℕ) → suc(n  + k )) (*-suc m n) ⟩
    suc (n + (m + m * n))
  ≡⟨ cong suc (+-swap n m (m * n)) ⟩ 
    suc m + suc m * n
  ∎ 

*-comm : ∀ (n m : ℕ) → n * m ≡ m * n 
*-comm zero m = sym (x*0=0 m)
*-comm (suc n) m = 
  begin 
    m + n * m 
  ≡⟨ cong (m +_) (*-comm n m) ⟩ 
    m + m * n 
  ≡⟨ sym (*-suc m n) ⟩
    m * suc n 
  ∎

0monusN=0 : ∀ (n : ℕ) → zero ∸ n ≡ zero 
0monusN=0 zero = refl
0monusN=0 (suc n) = refl

*-leftId1 : ∀ (n : ℕ) → 1 * n ≡ n 
*-leftId1 zero = refl
*-leftId1 (suc n) = cong suc (rightId-0 n)

^-distrLeft-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p) 
^-distrLeft-+-* m zero p = 
  begin
    m ^ (0 + p) 
  ≡⟨ refl ⟩ 
    m ^ p 
  ≡⟨ sym (*-leftId1 (m ^ p)) ⟩ 
    1 * m ^ p 
  ≡⟨ refl ⟩ 
    (m ^ zero) * (m ^ p) 
  ∎
^-distrLeft-+-* m (suc n) p = 
  begin 
    m ^ (suc n + p)
  ≡⟨ refl ⟩ 
    m * m ^ (n + p) 
  ≡⟨ cong (m *_) (^-distrLeft-+-* m n p) ⟩ 
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩  
    m * m ^ n * m ^ p 
  ∎

  -- hasAssoc : (ℕ → ℕ → ℕ) → ∀ (m n k) → 
-- pattern hasAssoc = 

swap : ∀ (_∘_ : ℕ → ℕ → ℕ) 
          → (∀ (m n k : ℕ) → m ∘ (n ∘ k) ≡ (m ∘ n) ∘ k)
          → (∀ (m n : ℕ) → m ∘ n ≡ n ∘ m)  
          → (∀ (m n k : ℕ) → m ∘ (n ∘ k) ≡ n ∘ (m ∘ k))
swap _∘_ ∘-assoc ∘-comm m n k = 
  begin
    m ∘ (n ∘ k) 
  ≡⟨ ∘-assoc m n k ⟩ 
    (m ∘ n) ∘ k
  ≡⟨ cong (_∘ k) (∘-comm m n) ⟩
    (n ∘ m) ∘ k 
  ≡⟨ sym (∘-assoc n m k) ⟩  
    n ∘ (m ∘ k)
  ∎

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap = swap _*_ (λ m n k → sym (*-assoc m n k)) (*-comm)

^-distrRight-* : ∀ (m n k : ℕ) → (m * n) ^ k ≡ m ^ k * n ^ k
^-distrRight-* m n zero = refl
^-distrRight-* m n (suc k) = 
  begin 
    (m * n) ^ (suc k) 
  ≡⟨ refl ⟩ 
    m * n * (m * n) ^ k
  ≡⟨ cong (m * n *_ ) (^-distrRight-* m n k) ⟩ 
    m * n * (m ^ k * n ^ k)
  ≡⟨ *-assoc m n (m ^ k * n ^ k) ⟩ 
    m * (n * (m ^ k * n ^ k))
  ≡⟨ cong (m *_) (*-swap n (m ^ k) (n ^ k)) ⟩ 
    m * (m ^ k * (n * n ^ k)) 
  ≡⟨ sym (*-assoc m (m ^ k) (n * n ^ k)) ⟩   
    (m ^ suc k) * (n ^ suc k)
  ∎

^-*-assoc : ∀ (m n k : ℕ) →  (m ^ n) ^ k ≡ m ^ (n * k)
^-*-assoc m n zero = 
  begin 
    (m ^ n) ^ zero 
  ≡⟨ refl ⟩ 
    1 
  ≡⟨ refl ⟩ 
    m ^ zero 
  -- cong gives error but everything type checks
  ≡⟨  cong (m ^_) refl ⟩ 
    m ^ (n * zero) 
  ∎
^-*-assoc m n (suc k) = 
  begin 
    m ^ n * (m ^ n) ^ k 
  ≡⟨ cong (m ^ n *_) (^-*-assoc m n k) ⟩
    m ^ n * (m ^ (n * k))
  ≡⟨ sym (^-distrLeft-+-* m n (n * k)) ⟩ 
    m ^ (n + n * k)
  ≡⟨ cong (m ^_) (sym (*-suc n k)) ⟩  
    m ^ (n * suc k) 
  ∎

-- GIVES ERROR DUE TO DUPLICATE BUILTIN NATURAL NUMBES PRAGMA
-- import Part1.Naturals using (Bin)

-- Just copied then ... 
data Bin : Set where 
    # : Bin
    _O : Bin → Bin
    _I : Bin → Bin 

Binsuc : Bin → Bin 
Binsuc # = # I
Binsuc (bits O) = bits I
Binsuc (bits I) = (Binsuc bits) O

-- Conversions

-- Natural number to Binary repr.
Num2Bin : ℕ → Bin 
Num2Bin 0 = # O
Num2Bin (suc n) = Binsuc (Num2Bin n)

-- Binary number to natural (n = Sum_i (x_i * 2^i))
Bin2NumHelper : Bin → ℕ → ℕ
Bin2NumHelper # n = 0
Bin2NumHelper (bits O) n = Bin2NumHelper bits (n + 1)
Bin2NumHelper (bits I) n = (2 ^ n) + (Bin2NumHelper bits (n + 1))

-- Omitting helper function
Bin2Num : Bin → ℕ
Bin2Num = λ (b : Bin) → Bin2NumHelper b 0

-- Maybe a more recursive approach

-- Proofs 

FromSuc : ∀ (b : Bin) → Bin2Num ( Binsuc b) ≡ suc (Bin2Num b)
FromSuc # = refl
FromSuc (b O) = refl
FromSuc (b I) = 
  begin 
    Bin2Num (Binsuc (b I))
  ≡⟨ {!  !} ⟩ 
    suc (Bin2Num (b I)) 
  ∎

ToFromNum : ∀ (n : ℕ) →  Bin2Num (Num2Bin n) ≡ n
ToFromNum zero = refl
ToFromNum (suc n) = 
    begin 
      Bin2Num (Num2Bin (suc n)) 
    ≡⟨ refl ⟩ 
      Bin2Num (Binsuc (Num2Bin n))
    ≡⟨ {!   !} ⟩ 
      suc (Bin2Num (Num2Bin n))
    ≡⟨ cong suc (ToFromNum n) ⟩ 
      suc n
    ∎



