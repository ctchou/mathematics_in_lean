import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction

example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
--    sorry
    linarith [Nat.factorial_pos (n + 1)]
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
--    sorry
    apply Nat.dvd_factorial (Nat.Prime.pos pp)
    linarith
  have : p = 1 := by
--    sorry
    have p_dvd_diff := Nat.dvd_sub' pdvd this
    simp at p_dvd_diff
    simp [p_dvd_diff]
  show False
--  sorry
  linarith [Nat.Prime.one_lt pp]

open Finset

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end

section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
--  sorry
  ext x
  simp ; tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
--  sorry
  ext x
  simp ; tauto

end

example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h

theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
--  sorry
  rcases Nat.Prime.eq_one_or_self_of_dvd prime_q p h with p1 | pq
  . linarith [Nat.Prime.one_lt prime_p]
  . assumption

theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
--  sorry
  rcases h₁ with pa | ps
  . have p_eq_a := _root_.Nat.Prime.eq_of_dvd_of_prime prime_p h₀.1 pa
    left ; assumption
  . have p_in_s := ih h₀.2 ps
    right ; assumption

example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter

theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
--    sorry
    have all_pos : ∀ n ∈ s', 0 < n := by
      intro n ns
      apply Nat.Prime.pos (mem_s'.mp ns)
    linarith [Finset.prod_pos all_pos]
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
--    sorry
    apply Finset.dvd_prod_of_mem
    simp [s'_def, pp]
    apply h p pp
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
--  sorry
  rw [Nat.dvd_one] at this
  linarith [Nat.Prime.one_lt pp]

theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k

example : 27 % 4 = 3 := by norm_num

example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
--  sorry
  constructor
  . apply Nat.div_dvd_of_dvd h₀
  . have h₃ : 0 < n := by apply Nat.zero_lt_of_lt h₂
    have h₄ : 1 < m := by apply Nat.lt_of_lt_of_le (by norm_num : 1 < 2) h₁
    apply Nat.div_lt_self h₃ h₄

theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
--  . sorry
  . by_cases prime_m : Nat.Prime m
    . use m
    . rcases ih m mltn h1 prime_m with ⟨p, prime_p, p_dvd_m, p_mod4_3⟩
      use p
      simp [prime_p, p_mod4_3]
      apply dvd_trans p_dvd_m mdvdn
--  . sorry
  . rcases aux mdvdn mge2 mltn with ⟨nm_dvd_n, nm_lt_n⟩
    by_cases prime_nm : Nat.Prime (n/m)
    . use (n/m)
    . rcases ih (n/m) (nm_lt_n) h1 prime_nm with ⟨p, prime_p, p_dvd_nm, p_mod4_3⟩
      use p
      simp [prime_p, p_mod4_3]
      apply dvd_trans p_dvd_nm nm_dvd_n

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption

lemma aux1 {p : ℕ} {s : Finset ℕ} : p ∈ s → (p ∣ ∏ i ∈ s, i) := by
--  sorry
  induction' s using Finset.induction_on with a s ans ih
  . simp
  simp [Finset.prod_insert ans]
  rintro (pa | ps)
  . simp [pa]
  . have := ih ps
    apply Dvd.dvd.mul_left this a

lemma aux2 {p : ℕ} {s : Finset ℕ} (hp : Nat.Prime p) (hs : ∀ i ∈ s, Nat.Prime i) (hd : p ∣ ∏ i in s, i) : p ∈ s := by
  induction' s using Finset.induction_on with a s ans ih
  . simp at hd
    linarith [Nat.Prime.one_lt hp]
  simp
  simp at hs
  simp [Finset.prod_insert ans, Nat.Prime.dvd_mul hp] at hd
  rcases hd with pa | ps
  . left
    have := Nat.Prime.one_lt hp
    simp [Nat.dvd_prime hs.1] at pa
    rcases pa <;> linarith
  . right
    apply ih hs.2 ps

theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
--    sorry
    rw [add_comm, Nat.add_mul_mod_self_left]
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
--    sorry
    apply (hs p).mp
    simp [pp, p4eq]
  have pne3 : p ≠ 3 := by
--    sorry
    intro peq3
    simp [peq3] at pp
    simp [peq3, Nat.Prime.dvd_mul pp, (by norm_num : ¬ 3 ∣ 4)] at pdvd
    have : ∀ i ∈ erase s 3, Nat.Prime i := by
      simp
      intro i _ is
      apply ((hs i).mpr is).1
    have erase_3 := aux2 Nat.prime_three this pdvd
    simp at erase_3
  have : p ∣ 4 * ∏ i in erase s 3, i := by
--    sorry
    have : p ∈ erase s 3 := by simp [ps, pne3]
    have := aux1 this
    apply Dvd.dvd.mul_left this 4
  have p_dvd_3 : p ∣ 3 := by
--    sorry
    have dvd_diff := Nat.dvd_sub' pdvd this
    simp at dvd_diff ; assumption
  have : p = 3 := by
--    sorry
    have pne1 : ¬ p = 1 := by linarith [Nat.Prime.one_lt pp]
    have p1p3 := (Nat.dvd_prime Nat.prime_three).mp p_dvd_3
    simp [pne1] at p1p3
    assumption
  contradiction
