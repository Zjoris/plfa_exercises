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
  ≡⟨ {!   !} ⟩ 
    m * k + (suc n) * k 
  ∎

