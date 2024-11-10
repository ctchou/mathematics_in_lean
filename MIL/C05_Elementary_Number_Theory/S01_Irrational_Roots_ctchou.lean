import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num

#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul
#check Nat.dvd_gcd

theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h

example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have div2_m : 2 ∣ m := by
--    sorry
    apply even_of_even_sqr
    simp [sqr_eq]
  have ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp div2_m
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 := by
--    sorry
    have pos_2 : 0 < 2 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left pos_2 this
  have div2_n : 2 ∣ n := by
--    sorry
    apply even_of_even_sqr
    simp [← this]
  have div2_gcd : 2 ∣ m.gcd n := by
--    sorry
    apply Nat.dvd_gcd div2_m div2_n
  have : 2 ∣ 1 := by
--    sorry
    unfold Nat.Coprime at coprime_mn
    rw [coprime_mn] at div2_gcd
    exact div2_gcd
  norm_num at this

theorem divp_of_divp_sqr {m p : ℕ} (prime_p : p.Prime) (h : p ∣ m ^ 2) : p ∣ m := by
  rw [pow_two, Nat.Prime.dvd_mul prime_p] at h
  cases h <;> assumption

example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
--  sorry
  intro sqr_eq
  have p_ge_2 : 2 ≤ p := Nat.Prime.two_le prime_p
  have divp_m : p ∣ m := by
    apply divp_of_divp_sqr prime_p
    simp [sqr_eq]
  have ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp divp_m
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    have pos_p : 0 < p := by linarith
    apply Nat.eq_of_mul_eq_mul_left pos_p this
  have divp_n : p ∣ n := by
    apply divp_of_divp_sqr prime_p
    simp [← this]
  have divp_gcd : p ∣ m.gcd n := by
    apply Nat.dvd_gcd divp_m divp_n
  have : p ∣ 1 := by
    unfold Nat.Coprime at coprime_mn
    rw [coprime_mn] at divp_gcd
    exact divp_gcd
  have : p ≤ 1 := by
    apply Nat.le_of_dvd
    . linarith
    . exact this
  linarith

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have p_nez : p ≠ 0 := by
    linarith [(Nat.prime_def_lt.mp prime_p).1]
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
--    sorry
    rw [factorization_pow' m 2 p]
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
--    sorry
    rw [factorization_mul' p_nez nsqr_nez, factorization_pow' n 2 p, Nat.Prime.factorization' prime_p]
    abel
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
--    sorry
    rw [factorization_pow' m k p]
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
--    sorry
    rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow' n k p]
    abel
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
--  sorry
  simp [← Nat.mul_sub]

#check multiplicity
