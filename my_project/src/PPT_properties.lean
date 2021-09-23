import data.zmod.parity
import number_theory.pythagorean_triples

import number_theory.quadratic_reciprocity


/-
Authors: Lisa Cenek, Brittany Gelb
-/

/-
Several useful elementary properties of primitive pythagorean triples follow nicely from the 
classification theorem. 

We formalize some of those properties, starting with divisibility by 3 and 4.
-/

open pythagorean_triple

/-
If x,y,z is a primitive pythagorean triple, then exactly one of x,y is 0 mod 4.
-/
theorem pythagorean_triple_exactly_one_div_four {x y z : ℤ} (h : pythagorean_triple x y z)
  (h_coprime : int.gcd x y = 1):
  ((x % 4 = 0) ∧ (y % 4 ≠ 0)) ∨ ((x % 4 ≠ 0) ∧ (y % 4 = 0))  :=
begin
  have k : pythagorean_triple x y z ∧ int.gcd x y = 1,
  split,
  exact h,
  exact h_coprime,
  rw coprime_classification at k,
  cases k with m km,
  cases km with n kmn,

  cases kmn with k1 k2,
  cases k2 with k2 k3,
  cases k3 with k3 k4,
  cases k4 with k4 k5,
  {
    cases k1 with y_even x_even,
    {
      right,
      cases y_even with x_odd y_even,
      cases k4 with k4m k4n,
      have eq1 := int.mod_add_div m 2,
      rw k4m at eq1,
      rw zero_add at eq1,
      rw ← eq1 at y_even,
      rw ← mul_assoc 2 2 (m / 2) at y_even,
      have two_mul_two : (2 : ℤ ) * 2 = 4 := by norm_num,
      rw two_mul_two at y_even,
      norm_num,
      rw mul_assoc at y_even,
      have four_div_y := dvd.intro (m / 2 * n) (eq.symm y_even),
      refine ⟨_, four_div_y⟩,
      rw ← imp_false,
      intro j,
      have four_div_one := int.dvd_gcd j four_div_y,
      rw h_coprime at four_div_one,
      norm_num at four_div_one,
    },
    {
      left,
      cases x_even with x_even y_odd,
      cases k4 with k4m k4n,
      have eq1 := int.mod_add_div m 2,
      rw k4m at eq1,
      rw zero_add at eq1,
      rw ← eq1 at x_even,
      rw ← mul_assoc 2 2 (m / 2) at x_even,
      have two_mul_two : (2 : ℤ ) * 2 = 4 := by norm_num,
      rw two_mul_two at x_even,
      norm_num,
      rw mul_assoc at x_even,
      have four_div_x := dvd.intro (m / 2 * n) (eq.symm x_even),
      refine ⟨four_div_x, _⟩,
      rw ← imp_false,
      intro j,
      have four_div_one := int.dvd_gcd four_div_x j,
      rw h_coprime at four_div_one,
      norm_num at four_div_one,
    }

  },

{
    cases k1 with y_even x_even,
    {
      right,
      cases y_even with x_odd y_even,
      cases k5 with k5m k5n,

      have eq1 := int.mod_add_div n 2,
      rw k5n at eq1,
      rw zero_add at eq1,
      rw mul_assoc at y_even,
      rw mul_comm m n at y_even,
      rw ← mul_assoc at y_even,

      rw ← eq1 at y_even,

      rw ← mul_assoc 2 2 (n / 2) at y_even,

      have two_mul_two : (2 : ℤ ) * 2 = 4 := by norm_num,

      rw two_mul_two at y_even,

      norm_num,
      rw mul_assoc at y_even,
      have four_div_y := dvd.intro (n / 2 * m) (eq.symm y_even),

      refine ⟨_, four_div_y⟩,
      rw ← imp_false,
      intro j,

      have four_div_one := int.dvd_gcd j four_div_y,
      rw h_coprime at four_div_one,
      norm_num at four_div_one,

    },
    {
      left,
      cases x_even with x_even y_odd,
      cases k5 with k5m k5n,

      have eq1 := int.mod_add_div n 2,
      rw k5n at eq1,
      rw zero_add at eq1,
      rw mul_assoc at x_even,
      rw mul_comm m n at x_even,
      rw ← mul_assoc at x_even,
      rw ← eq1 at x_even,
      rw ← mul_assoc 2 2 (n / 2) at x_even,
      have two_mul_two : (2 : ℤ ) * 2 = 4 := by norm_num,
      rw two_mul_two at x_even,

      norm_num,
      rw mul_assoc at x_even,
      have four_div_x := dvd.intro (n / 2 * m) (eq.symm x_even),

      refine ⟨four_div_x, _⟩,
      rw ← imp_false,
      intro j,

      have four_div_one := int.dvd_gcd four_div_x j,
      rw h_coprime at four_div_one,
      norm_num at four_div_one,
    }

  }


end


/-
Lemma to obtain possible values modulo 3.
(Modeled from data.nat.parity)
-/
lemma mod_three_eq_zero_or_one_or_two (n : ℤ) : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 :=
have h : n % 3 < 3 := abs_of_nonneg (show 0 ≤ (3 : ℤ), from dec_trivial) ▸ int.mod_lt _ dec_trivial,
have h₁ : 0 ≤ n % 3 := int.mod_nonneg _ dec_trivial,
match (n % 3), h, h₁ with
| (0 : ℕ) := λ _ _ , or.inl rfl
| (1 : ℕ) := λ _ _ , or.inr (or.inl rfl)
| (2 : ℕ) := λ _ _ , or.inr (or.inr rfl)
| (k + 3 : ℕ) := λ h _, absurd h dec_trivial
| -[1+ a] := λ _ h₁, absurd h₁ dec_trivial
end




/-
If x,y,z is a primitive pythagorean triple, then exactly one of x,y is 0 mod 3.
-/
theorem pythagorean_triple_exactly_one_div_three {x y z : ℤ} (h : pythagorean_triple x y z)
  (h_coprime : int.gcd x y = 1):
  ((x % 3 = 0) ∧ (y % 3 ≠ 0)) ∨ ((x % 3 ≠ 0) ∧ (y % 3 = 0))  :=
begin
  by_contradiction H,
  rw push_neg.not_or_eq at H,
  cases H with h1 h2,
  rw push_neg.not_and_eq at h1,
  rw push_neg.not_and_eq at h2,
  rw push_neg.not_not_eq at h1,

  by_cases j : (x % 3 = 0),
  {
    have j' := h1 j,
    simp at h1 j j',
    have three_div_one := int.dvd_gcd j j',
    rw h_coprime at three_div_one,
    norm_num at three_div_one,
  },
  {
  have j' := h2 j,

  have xlem := mod_three_eq_zero_or_one_or_two x,
  have ylem := mod_three_eq_zero_or_one_or_two y,

  have xlem' := or.resolve_left xlem j,
  have ylem' := or.resolve_left ylem j',

  have pyth_mod : (x * x + y * y) % 3 = (x * x + y * y) % 3 := by refl,
  have xyz : x * x + y * y = z * z := h,

  have pyth_mod' : (x*x + y*y) % 3 = (z*z) % 3 := by {
    calc (x*x + y*y) % 3 = (x*x + y*y) % 3 : by refl
                  ...= (z*z) % 3 : by rw xyz,
        },

  cases xlem' with x1 x2,
  {
    cases ylem' with y1 y2,
    {
      have x_sq := int.mul_mod x x 3,
      rw x1 at x_sq,
      have y_sq := int.mul_mod y y 3,
      rw y1 at y_sq,
      norm_num at x_sq,
      norm_num at y_sq,

      rw int.add_mod (x*x) (y*y) 3 at pyth_mod',
      rw x_sq at pyth_mod',
      rw y_sq at pyth_mod',
      norm_num at pyth_mod',

      haveI : fact (nat.prime 3) := by sorry,
      have two_not_zero : (2 : zmod 3) ≠ 0 := dec_trivial,
      
      have lem := zmod.euler_criterion 3 two_not_zero,
      {
        have two_not_euler_right : ¬ ((2 : zmod 3)^(3/2) = 1):= by dec_trivial,
        rw ← not_iff_not at lem,
        rw ← lem at two_not_euler_right,
        sorry,
      },
    }, sorry,
  },
  sorry,
  },
end