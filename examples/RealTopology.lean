import Mathlib.Basic.Real.Basic
--import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
--import Mathlib.Tactic.Ring
--import Mathlib.Tactic.Linarith
--import Mathlib.Tactic.NormNum
--import Mathlib.Tactic.Positivity
--import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
--import Mathlib.Tactic.Tauto
--import Mathlib.Tactic.Common
import Mathlib.Topology.MetricSpace.Basic

-- Definition. A *neighborhood* of a point x₀ in a
-- metric space S is a set
--   Nᵣ(x₀) = { x ∈ S | dist(x, x₀) < r }
-- for some radius r. Ross requires r > 0, but the
-- usual approach in Lean is to omit this from the
-- definition and instead impose r > 0 in theorems.
def Neighborhood {S} [MetricSpace S] (x₀ : S) (r : ℝ) : Set S :=
  { x : S | dist x x₀ < r }

-- Definition. A point x₀ is *interior to* a set E if
-- there exists a neighborhood of positive radius
-- around x₀ that is entirely contained within E.
def IsInteriorTo {S} [MetricSpace S] (x₀ : S) (E : Set S) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (Neighborhood x₀ r) ⊆ E

-- Definition. The *interior* of a set E is the set of
-- all its interior points.
def Interior {S} [MetricSpace S] (E : Set S) : Set S :=
  { x : S | IsInteriorTo x E }

theorem center_of_neighborhood_is_member
    {S} [MetricSpace S] (x : S) (r : ℝ) (hr : 0 < r)
    : x ∈ Neighborhood x r := by
  unfold Neighborhood
  norm_num
  exact hr

theorem interior_implies_member
    {S} [MetricSpace S] (x : S) (E : Set S) (h : IsInteriorTo x E) : x ∈ E := by
  unfold IsInteriorTo at h
  obtain ⟨r, hr⟩ := h
  have : x ∈ Neighborhood x r := center_of_neighborhood_is_member x r (hr.1)
  tauto

open Set

-- Theorem. The left endpoint of any closed interval
-- [a, b] is not interior to the interval.
theorem left_endpoint_of_closed_interval_is_not_interior
    (a : ℝ) (b : ℝ) : ¬(IsInteriorTo a (Icc a b)) := by
  -- We need to show that no neighborhood of a (of
  -- positive radius) is contained within [a, b].
  unfold IsInteriorTo
  -- Let r be any positive number, and consider Nᵣ(a).
  push Not
  intro r hr
  -- We need to find an x ∈ Nᵣ(a) that's not in [a, b].
  suffices ∃ x : ℝ, x ∈ Neighborhood a r ∧ x ∉ Icc a b   by intro h; rcases this with ⟨x, hx, hxnot⟩; exact hxnot (h hx)
  -- Use x = a - r / 2.
  let x := a - r / 2
  -- x ∈ Nᵣ(a).
  have : x ∈ Neighborhood a r                            := by change dist x a < r; rw [Real.dist_eq]; dsimp [x]; (rw [show a - r / 2 - a = -(r / 2) by ring, abs_neg]); (rw [abs_of_pos (by linarith)]); linarith
  -- Because x < a, we know x ∉ [a, b].
  have : x < a                                           := by dsimp [x]; exact sub_lt_self _ (half_pos hr)
  have : x ∉ Icc a b                                     := by intro hx; exact (not_le_of_gt this) hx.1
  -- We've found the x we were looking for.
  use x

-- Theorem. Any element x of the open interval (a, b)
-- is interior to (a, b).
theorem any_member_of_open_interval_is_interior {a : ℝ} {b : ℝ} {x : ℝ} (_ : x ∈ Ioo a b) : IsInteriorTo x (Ioo a b) := by
  -- Need to show ∃ Nᵣ(x) ⊆ (a, b) with r ≥ 0.
  unfold IsInteriorTo
  -- Proof is by cases.
  rcases le_total (x - a) (b - x) with hleft | hright
  · -- Case 1: x is in the left half of (a, b).
    -- Let r = x - a.
    let r := x - a
    -- Claim: r > 0.
    have : r > 0                                         := by change x - a > 0; exact sub_pos.mpr (Set.mem_Ioo.mp ‹x ∈ Ioo a b›).1
    -- Claim: Nᵣ(x) ⊆ (a, b).
    have : Neighborhood x r ⊆ Ioo a b := by
      -- Nᵣ(x) = (x - r, x + r) = (a, x + r).
      suffices Ioo a (x + r) ⊆ Ioo a b                   by intro y hy; change dist y x < r at hy; (have hd : |y - x| < r := by simpa [Real.dist_eq] using hy); rcases abs_lt.mp hd with ⟨hl, hu⟩; apply this; change a < y ∧ y < x + r; constructor <;> linarith [show r = x - a by rfl]
      -- x + r ≤ b.
      have : x + r ≤ b                                   := by simpa [r, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using add_le_add_right hleft x
      .                                                  intro y hy; exact ⟨hy.1, lt_of_lt_of_le hy.2 this⟩
    use r
  · -- Case 2: x is in the right half of (a, b).
    -- Let r = b - x.
    let r := b - x
    -- Claim: r > 0.
    have : r > 0                                         := by dsimp [r]; linarith [Set.mem_Ioo.mp ‹x ∈ Ioo a b›]
    -- Claim: Nᵣ(x) ⊆ (a, b).
    have : Neighborhood x r ⊆ Ioo a b := by
      -- Nᵣ(x) = (x - r, x + r) = (x - r, b).
      suffices Ioo (x - r) b ⊆ Ioo a b                   by intro y hy; change dist y x < r at hy; (have hd : |y - x| < r := by simpa [Real.dist_eq] using hy); rcases abs_lt.mp hd with ⟨hl, hu⟩; (have hlow : a ≤ x - r := by dsimp [r]; linarith [hright]); (have hup : x + r = b := by dsimp [r]; ring); apply this; change x - r < y ∧ y < b; constructor <;> linarith
      -- x - r ≥ a.
      have : x - r ≥ a                                   := by dsimp [r]; linarith [hright]
      .                                                  intro y hy; exact ⟨lt_of_le_of_lt this hy.1, hy.2⟩
    use r

-- Theorem. Any element x of (a, b) is interior to
-- [a, b].
theorem any_member_of_open_interval_is_interior_to_closed_interval
    {a : ℝ} {b : ℝ} {x : ℝ} (_ : x ∈ Ioo a b)
    : IsInteriorTo x (Icc a b) := by
  -- Need to show ∃ Nᵣ(x) ⊆ [a, b] with r ≥ 0.
  unfold IsInteriorTo
  -- Proof is by cases.
  rcases le_total (x - a) (b - x) with hleft | hright
  · -- Case 1: x is in the left half of [a, b].
    -- Let r = x - a.
    let r := x - a
    -- Claim: r > 0.
    have : r > 0                                         := by change x - a > 0; exact sub_pos.mpr (Set.mem_Ioo.mp ‹x ∈ Ioo a b›).1
    -- Claim: Nᵣ(x) ⊆ [a, b].
    have : Neighborhood x r ⊆ Icc a b := by
      -- Nᵣ(x) = (x - r, x + r) = (a, x + r).
      suffices Ioo a (x + r) ⊆ Icc a b                   by intro y hy; change dist y x < r at hy; (have hd : |y - x| < r := by simpa [Real.dist_eq] using hy); rcases abs_lt.mp hd with ⟨hl, hu⟩; apply this; change a < y ∧ y < x + r; constructor <;> linarith [show r = x - a by rfl]
      -- x + r ≤ b.
      have : x + r ≤ b                                   := by simpa [r, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using add_le_add_right hleft x
      .                                                  intro y hy; exact ⟨le_of_lt hy.1, le_of_lt (lt_of_lt_of_le hy.2 this)⟩
    use r
  · -- Case 2: x is in the right half of [a, b].
    -- This time we use r = b - x, but the rest of
    -- the proof is similar.
    let r := b - x
    have : r > 0                                         := by dsimp [r]; linarith [Set.mem_Ioo.mp ‹x ∈ Ioo a b›]
    have : Neighborhood x r ⊆ Icc a b := by
      suffices Ioo (x - r) b ⊆ Icc a b                   by intro y hy; change dist y x < r at hy; (have hd : |y - x| < r := by simpa [Real.dist_eq] using hy); rcases abs_lt.mp hd with ⟨hl, hu⟩; (have hlow : a ≤ x - r := by dsimp [r]; linarith [hright]); (have hup : x + r = b := by dsimp [r]; ring); apply this; change x - r < y ∧ y < b; constructor <;> linarith
      have : x - r ≥ a                                   := by dsimp [r]; linarith [hright]
      .                                                  intro y hy; exact ⟨le_trans this (le_of_lt hy.1), le_of_lt hy.2⟩
    use r

-- Definition. A set E is *open* if every point in E is
-- interior.
def IsOpen421 {S} [MetricSpace S] (E : Set S) :=
  ∀ x ∈ E, IsInteriorTo x E

-- Definition. A set E is *closed* if its complement is
-- open.
def IsClosed421 {S} [MetricSpace S] (E : Set S) :=
  IsOpen421 Eᶜ

-- Theorem. The interval (a, b) is open in ℝ.
theorem open_interval_is_open (a : ℝ) (b : ℝ)
    : IsOpen421 (Ioo a b) := by
  -- We need to show that every element is interior.
  unfold IsOpen421
  -- Let x ∈ (a, b).
  intro x hx
  -- Then x is interior by an earlier theorem.
  .                                                      exact any_member_of_open_interval_is_interior hx

-- Theorem. The interval [a, b] is closed in ℝ.
theorem closed_interval_is_closed (a : ℝ) (b : ℝ)
    : IsClosed421 (Icc a b) := by
  -- We need to prove that [a, b]ᶜ is open.
  unfold IsClosed421
  -- Let x ∈ [a, b]ᶜ. We'll prove that x is interior.
  unfold IsOpen421
  intro x hx
  -- Either x < a or x > b. The rest of the proof is by
  -- cases.
  have hlr: x < a ∨ x > b := by change ¬ (a ≤ x ∧ x ≤ b) at hx; (rcases lt_or_ge x a with h | h); (· exact Or.inl h); · right; exact not_le.mp (by intro hxb; exact hx ⟨h, hxb⟩)
  rcases hlr with hl | hr
  · -- Case 1: x < a.
    -- We need to find a neighborhood Nᵣ(x) ⊆ [a, b]ᶜ
    -- with positive radius.
    unfold IsInteriorTo
    -- Let r = a - x.
    let r := a - x
    -- r > 0.
    have : r > 0 := by change a - x > 0; exact sub_pos.mpr hl
    -- Nᵣ(x) ⊆ [a, b]ᶜ.
    have : Neighborhood x r ⊆ (Icc a b)ᶜ := by intro y hy; change dist y x < r at hy; (have hd : |y - x| < r := by simpa [Real.dist_eq] using hy); have hupper := (abs_lt.mp hd).2; intro hycc; dsimp [r] at hupper; linarith [hycc.1]
    -- We've found the desired neighborhood.
    use r
  · -- Case 2: b < x. The proof is similar:
    unfold IsInteriorTo
    let r := x - b
    have : r > 0 := by change x - b > 0; exact sub_pos.mpr hr
    have : Neighborhood x r ⊆ (Icc a b)ᶜ := by intro y hy; change dist y x < r at hy; (have hd : |y - x| < r := by simpa [Real.dist_eq] using hy); have hlow := (abs_lt.mp hd).1; intro hycc; dsimp [r] at hlow; linarith [hycc.2]
    use r

theorem interval_from_a_to_infinity_excluding_a_is_open
    (a : ℝ) : IsOpen421 (Ioi a) := by
  unfold IsOpen421
  intro x hx
  unfold IsInteriorTo
  let r := x - a
  have : r > 0 := by change x - a > 0; exact sub_pos.mpr hx
  have : Neighborhood x r ⊆ Ioi a := by intro y hy; change dist y x < r at hy; rw [Real.dist_eq] at hy; rcases abs_lt.mp hy with ⟨hlo, _⟩; change a < y; nlinarith [show r = x - a by rfl]
  use r

theorem interval_from_minus_infinity_to_b_excluding_b_is_open
    (b : ℝ) : IsOpen421 (Iio b) := by
  unfold IsOpen421
  intro x hx
  unfold IsInteriorTo
  let r := b - x
  have : r > 0 := by simpa [r] using (sub_pos.mpr (Set.mem_Iio.mp hx))
  have : Neighborhood x r ⊆ Iio b := by intro y hy; change dist y x < r at hy; rw [Real.dist_eq] at hy; have hle : y - x ≤ |y - x| := le_abs_self (y - x); change y < b; dsimp [r] at hy; nlinarith
  use r

theorem interval_from_a_to_infinity_including_a_is_closed
    (a : ℝ) : IsClosed421 (Ici a) := by
  unfold IsClosed421
  suffices IsOpen421 (Iio a) by simpa using this
  exact interval_from_minus_infinity_to_b_excluding_b_is_open a

theorem whole_real_line_is_open : IsOpen421 (univ : Set ℝ) := by
  unfold IsOpen421
  intro x hx
  unfold IsInteriorTo
  use 1
  constructor; (· norm_num); · intro y hy; exact Set.mem_univ y

theorem empty_set_is_open : IsOpen421 (S := ℝ) ∅ := by
  unfold IsOpen421
  .                                                      intro x hx; exact False.elim hx

theorem whole_real_line_is_closed : IsClosed421 (univ : Set ℝ) := by
  unfold IsClosed421
  suffices IsOpen421 ∅ by simpa using this
  exact empty_set_is_open

theorem empty_set_is_closed : IsClosed421 (S := ℝ) ∅ := by
  unfold IsClosed421
  suffices IsOpen421 univ by simpa using this
  exact whole_real_line_is_open

def Rational (x : ℝ) : Prop := ¬(Irrational x)

def Rationals : Set ℝ := { x : ℝ | Rational x }

def Irrationals : Set ℝ := { x : ℝ | Irrational x }

-- Ross Exercise 13.10(a)
example (x : ℝ) : ¬(IsInteriorTo x { 1 / (n : ℝ) | n : PNat }) := by
  let E := { 1 / (n : ℝ) | n : PNat }
  unfold IsInteriorTo
  push Not
  intro r hr
  have: ∀ e ∈ E, Rational e := by intro e he; rcases he with ⟨n, hn⟩; intro hi; unfold Irrational at hi; apply hi; refine ⟨(n : ℚ)⁻¹, ?_⟩; simpa [div_eq_mul_inv] using hn
  have hirrational: ∃ x₁ ∈ Neighborhood x r, Irrational x₁ := by (obtain ⟨y, hyirr, hy₁, hy₂⟩ := exists_irrational_btwn (show x - r < x + r by linarith)); refine ⟨y, ?_, hyirr⟩; change dist y x < r; rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨x₁, hx₁⟩ := hirrational
  have : x₁ ∉ E := by intro hE; exact this x₁ hE hx₁.2
  exact Set.not_subset.mpr ⟨x₁, hx₁.1, this⟩

-- Ross Exercise 13.10(b)
example (x : ℝ) : ¬(IsInteriorTo x Rationals) := by
  unfold IsInteriorTo
  push Not
  intro r hr
  have hirrational: ∃ x₁ ∈ Neighborhood x r, Irrational x₁ := by (obtain ⟨y, hyirr, hy₁, hy₂⟩ := exists_irrational_btwn (show x - r < x + r by linarith)); refine ⟨y, ?_, hyirr⟩; change dist y x < r; rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨x₁, hx₁⟩ := hirrational
  exact Set.not_subset.mpr ⟨x₁, hx₁.1, by simpa [Rationals, Rational] using hx₁.2⟩

theorem union_of_collection_of_open_is_open {S} [MetricSpace S] (C : Set (Set S)) (_ : ∀ E ∈ C, IsOpen421 E) : IsOpen421 (⋃₀ C) := by
  unfold IsOpen421
  intro x hx
  have hexistsE₁: ∃ E₁ ∈ C, x ∈ E₁ := by rcases mem_sUnion.mp hx with ⟨E, hE, hxE⟩; exact ⟨E, hE, hxE⟩
  obtain ⟨E₁, hE₁⟩ := hexistsE₁
  have : IsOpen421 E₁ := by exact (‹∀ E ∈ C, IsOpen421 E› E₁ hE₁.1)
  have hexistsr: ∃ r > 0, Neighborhood x r ⊆ E₁ := by exact this x hE₁.2
  obtain ⟨r, hr⟩ := hexistsr
  have : Neighborhood x r ⊆ ⋃₀ C := by intro y hy; simp only [Set.mem_sUnion]; exact ⟨E₁, hE₁.1, hr.2 hy⟩
  exact ⟨r, hr.1, this⟩

theorem intersection_of_two_opens_is_open {S} [MetricSpace S] {E₁ : Set S} {E₂ : Set S} (_ : IsOpen421 E₁) (_ : IsOpen421 E₂) : IsOpen421 (E₁ ∩ E₂) := by
  unfold IsOpen421
  intro x hx
  have : x ∈ E₁ := by exact hx.1
  have : x ∈ E₂ := by exact hx.2
  have : IsInteriorTo x E₁ := by exact ‹IsOpen421 E₁› x hx.1
  have : IsInteriorTo x E₂ := by exact ‹IsOpen421 E₂› x hx.2
  have hexists1: ∃ r₁ > 0, Neighborhood x r₁ ⊆ E₁ := by rcases ‹IsInteriorTo x E₁› with ⟨r₁, hr₁, hsub⟩; exact ⟨r₁, hr₁, hsub⟩
  obtain ⟨r₁, hr₁⟩ := hexists1
  have hexists2: ∃ r₂ > 0, Neighborhood x r₂ ⊆ E₂ := by simpa [IsInteriorTo] using this
  obtain ⟨r₂, hr₂⟩ := hexists2
  let r := min r₁ r₂
  let N := Neighborhood x r
  have : N ⊆ E₁ := by intro y hy; change dist y x < min r₁ r₂ at hy; (rcases le_total r₁ r₂ with h | h); (· rw [min_eq_left h] at hy; exact hr₁.2 (by change dist y x < r₁; exact hy)); · rw [min_eq_right h] at hy; exact hr₁.2 (by change dist y x < r₁; exact lt_of_lt_of_le hy h)
  have : N ⊆ E₂ := by intro y hy; change dist y x < min r₁ r₂ at hy; (rcases le_total r₁ r₂ with h | h); (· rw [min_eq_left h] at hy; exact hr₂.2 (by change dist y x < r₂; exact lt_of_lt_of_le hy h)); · rw [min_eq_right h] at hy; exact hr₂.2 (by change dist y x < r₂; exact hy)
  have : N ⊆ E₁ ∩ E₂ := by intro y hy; exact ⟨(‹N ⊆ E₁›) hy, (‹N ⊆ E₂›) hy⟩
  . exact ⟨r, lt_min hr₁.1 hr₂.1, this⟩

theorem intersection_of_collection_of_closed_is_closed {S} [MetricSpace S] (C : Set (Set S)) (_ : ∀ E ∈ C, IsClosed421 E) : IsClosed421 (⋂₀ C) := by
  unfold IsClosed421
  suffices IsOpen421 (⋃₀ { Eᶜ | E ∈ C }) by (have hEq : (⋂₀ C)ᶜ = ⋃₀ {Eᶜ | E ∈ C} := by ext y; simp); rw [hEq]; exact this
  have : ∀ E ∈ C, IsOpen421 Eᶜ := by intro E hE; simpa [IsClosed421] using (‹∀ E ∈ C, IsClosed421 E› E hE)
  apply union_of_collection_of_open_is_open; intro F hF; rcases hF with ⟨E, hE, hEq⟩; rw [← hEq]; exact this E hE

theorem union_of_two_closeds_is_closed {S} [MetricSpace S] {E₁ : Set S} {E₂ : Set S} (_ : IsClosed421 E₁) (_ : IsClosed421 E₂) : IsClosed421 (E₁ ∪ E₂) := by
  unfold IsClosed421
  suffices IsOpen421 (E₁ᶜ ∩ E₂ᶜ) by simpa using this
  have hE1open : IsOpen421 E₁ᶜ := by simpa [IsClosed421] using ‹IsClosed421 E₁›
  have hE2open : IsOpen421 E₂ᶜ := by simpa [IsClosed421] using ‹IsClosed421 E₂›
  --unfold IsOpen421; intro x hx; have h₁ : IsInteriorTo x E₁ᶜ := ‹IsOpen421 E₁ᶜ› x hx.1; have h₂ : IsInteriorTo x E₂ᶜ := ‹IsOpen421 E₂ᶜ› x hx.2; rcases h₁ with ⟨r₁, hr₁, hs₁⟩; rcases h₂ with ⟨r₂, hr₂, hs₂⟩; refine ⟨min r₁ r₂, lt_min hr₁ hr₂, ?_⟩; intro y hy; change dist y x < min r₁ r₂ at hy; constructor; (· apply hs₁; change dist y x < r₁; exact lt_of_lt_of_le hy (min_le_left _ _)); · apply hs₂; change dist y x < r₂; exact lt_of_lt_of_le hy (min_le_right _ _)
  apply (intersection_of_two_opens_is_open hE1open hE2open)

def IsBoundary {S} [MetricSpace S] (x₀ : S) (E : Set S) :=
  ∀ r : ℝ, 0 < r →
    (let N := Neighborhood x₀ r
    N ∩ E ≠ ∅ ∧ N ∩ Eᶜ ≠ ∅)

def Boundary {S} [MetricSpace S] (E : Set S) :=
  { x : S | IsBoundary x E }

example (a : ℝ) (b : ℝ) (hle : a ≤ b) : IsBoundary a (Icc a b) := by
  unfold IsBoundary
  intro r hr N
  constructor
  · have : a ∈ N := by unfold N; unfold Neighborhood; change dist a a < r; simp; exact hr
    have : a ∈ Icc a b := by unfold Icc; change a ≤ a ∧ a ≤ b; simp; exact hle
    intro h; have hm : a ∈ N ∩ Icc a b := ⟨‹a ∈ N›, ‹a ∈ Icc a b›⟩; rw [h] at hm; exact hm
  · let x := a - r / 2
    have : x ∈ N := by change dist x a < r; rw [Real.dist_eq]; dsimp [x]; (rw [show a - r / 2 - a = -(r / 2) by ring, abs_neg, abs_of_pos (half_pos hr)]); linarith
    have : x ∉ Icc a b := by intro hx; (have hlt : a - r / 2 < a := by rw [sub_lt_iff_lt_add]; exact lt_add_of_pos_right _ (half_pos hr)); exact (not_le_of_gt hlt) hx.1
    have : x ∈ (Icc a b)ᶜ := by intro hx; exact this hx
    intro h; (have hm : x ∈ N ∩ (Icc a b)ᶜ := ⟨by assumption, by assumption⟩); rw [h] at hm; exact hm

example {S} [MetricSpace S] (x : S) (E : Set S) : ¬(IsInteriorTo x E ∧ IsBoundary x E) := by
  push Not
  intro hinterior
  unfold IsBoundary
  push Not
  unfold IsInteriorTo at hinterior
  obtain ⟨r, hr⟩ := hinterior
  obtain ⟨hrpos, hN⟩ := hr
  use r
  constructor
  · exact hrpos
  · set N := Neighborhood x r
    suffices (N ∩ Eᶜ) = ∅ by intro h; obtain ⟨y, hy⟩ := h.2; have hmem : y ∈ (∅ : Set S) := this ▸ hy; exact hmem
    apply Set.Subset.antisymm; (· intro y hy; exact (hy.2 (hN hy.1)).elim); · exact Set.empty_subset _

lemma boundary_subset_of_boundary_of_complement {S} [MetricSpace S] (x : S) (E : Set S) (hx : IsBoundary x E) : IsBoundary x Eᶜ := by
  unfold IsBoundary at hx
  unfold IsBoundary
  rw [compl_compl]
  intro r hr; exact ⟨(hx r hr).2, (hx r hr).1⟩

theorem boundary_of_set_equals_boundary_of_complement {S} [MetricSpace S] (E : Set S) : Boundary E = Boundary Eᶜ := by
  suffices Boundary E ⊆ Boundary Eᶜ ∧ Boundary Eᶜ ⊆ Boundary E by exact Set.Subset.antisymm this.1 this.2
  constructor
  · intro x hx
    unfold Boundary at hx
    change IsBoundary x E at hx
    unfold Boundary
    change IsBoundary x Eᶜ
    apply boundary_subset_of_boundary_of_complement x E hx
  · intro x hx
    unfold Boundary at hx
    change IsBoundary x Eᶜ at hx
    unfold Boundary
    change IsBoundary x E
    have : IsBoundary x Eᶜᶜ := by apply boundary_subset_of_boundary_of_complement x Eᶜ hx
    simp_all only [compl_compl]

theorem open_iff_disjoint_from_boundary {S} [MetricSpace S] (E : Set S) : IsOpen421 E ↔ E ∩ Boundary E = ∅ := by
  constructor
  · intro hopen
    suffices ∀ x : S, x ∈ E → ¬(IsBoundary x E) by ext x; constructor; (· intro hx; exact (this x hx.1) hx.2); · intro hx; simp at hx
    intro x hx
    have : IsInteriorTo x E := by exact hopen x hx
    intro hb; unfold IsBoundary at hb; unfold IsInteriorTo at this; obtain ⟨r, hrpos, hN⟩ := this; have hcomp := (hb r hrpos).2; (have hEq : Neighborhood x r ∩ Eᶜ = ∅ := by apply Set.Subset.antisymm; (· intro y hy; exact (hy.2 (hN hy.1)).elim); · exact Set.empty_subset _); exact hcomp hEq
  · intro hdisjoint
    unfold IsOpen421
    intro x hx
    have hnotboundary: ¬(IsBoundary x E) := by intro hb; have h : x ∈ E ∩ Boundary E := ⟨hx, hb⟩; rw [hdisjoint] at h; exact h
    unfold IsBoundary at hnotboundary
    push Not at hnotboundary
    obtain ⟨r, hr⟩ := hnotboundary
    obtain ⟨hrpos, h⟩ := hr
    unfold IsInteriorTo
    use r
    constructor
    · exact hrpos
    · let N := Neighborhood x r
      have : (N ∩ E) = ∅ ∨ (N ∩ Eᶜ) = ∅ := by by_cases hne : N ∩ Eᶜ = ∅; (· exact Or.inr hne); · left; by_contra hnot; apply h; constructor; (· exact Set.nonempty_iff_ne_empty.mpr hnot); · exact Set.nonempty_iff_ne_empty.mpr hne
      have : N ∩ E ≠ ∅ := by apply Set.nonempty_iff_ne_empty.mp; exact ⟨x, ⟨by simpa [N, Neighborhood] using hrpos, hx⟩⟩
      have : N ∩ Eᶜ = ∅ := by by_contra hne; apply h; constructor; (· exact Set.nonempty_iff_ne_empty.mpr this); · exact Set.nonempty_iff_ne_empty.mpr hne
      intro y hy; by_contra hye; have hm : y ∈ N ∩ Eᶜ := ⟨hy, hye⟩; rw [this] at hm; exact hm

example {S} [MetricSpace S] (E : Set S) : IsClosed421 E ↔ Boundary E ⊆ E := by
  constructor
  · intro hclosed
    have : IsOpen421 Eᶜ := by simpa [IsClosed421] using hclosed
    have : Eᶜ ∩ Boundary Eᶜ = ∅ := by exact (open_iff_disjoint_from_boundary Eᶜ).mp this
    have : Eᶜ ∩ Boundary E = ∅ := by ext y; constructor; (· intro hy; (have hy' : y ∈ Eᶜ ∩ Boundary Eᶜ := by rw [← boundary_of_set_equals_boundary_of_complement E]; exact hy); rw [this] at hy'; simpa using hy'); · simp
    intro x hx; by_contra hnot; have hmem : x ∈ Eᶜ ∩ Boundary E := ⟨hnot, hx⟩; rw [this] at hmem; exact hmem
  · intro hcontainsboundary
    have : Boundary E ∩ Eᶜ = ∅ := by apply Set.Subset.antisymm; (· intro x hx; exact (hx.2 (hcontainsboundary hx.1)).elim); · exact Set.empty_subset _
    have : Boundary Eᶜ ∩ Eᶜ = ∅ := by rw [← boundary_of_set_equals_boundary_of_complement E]; exact this
    have : IsOpen421 Eᶜ := by apply (open_iff_disjoint_from_boundary Eᶜ).2; simpa [Set.inter_comm] using this
    unfold IsClosed421; exact this

def IsUpperBound (M : ℝ) (E : Set ℝ) : Prop :=
  ∀ x ∈ E, x ≤ M

def IsBoundedBelow (E : Set ℝ) : Prop :=
  ∃ L : ℝ, ∀ x ∈ E, L ≤ x

def IsBoundedAbove (E : Set ℝ) : Prop :=
  ∃ M : ℝ, IsUpperBound M E

def IsBounded (E : Set ℝ) : Prop :=
  IsBoundedBelow E ∧ IsBoundedAbove E

def IsCompact421 (E : Set ℝ) : Prop :=
  IsBounded E ∧ IsClosed421 E

#print isLUB_csSup

def IsSupremum (M : ℝ) (E : Set ℝ) : Prop :=
  IsUpperBound M E ∧ (∀ t : ℝ, t < M → ¬(IsUpperBound t E))

/-theorem sup_exists
    (E : Set ℝ) (hnonempty : E.Nonempty) (hbdd : IsBoundedAbove E)
    : ∃ M : ℝ, (∀ x ∈ E, x ≤ M) ∧ (∀ t : ℝ, t < M → ∃ x ∈ E, t < x) := by
  let M := sSup E; have hlub : IsLUB E M := isLUB_csSup hnonempty hbdd; refine ⟨M, hlub.1, ?_⟩; intro t ht; by_contra hnone; (have htub : ∀ x ∈ E, x ≤ t := by intro x hx; exact le_of_not_gt (fun htx : t < x => hnone ⟨x, hx, htx⟩)); exact (not_lt_of_ge (hlub.2 htub)) ht-/

theorem sup_exists
    (E : Set ℝ) (hnonempty : E.Nonempty) (hbdd : IsBoundedAbove E)
    : ∃ M : ℝ, IsSupremum M E := by
  let M := sSup E; have hlub : IsLUB E M := isLUB_csSup hnonempty hbdd; refine ⟨M, hlub.1, ?_⟩; intro t ht htub; exact (not_lt_of_ge (hlub.2 htub)) ht

theorem nonempty_compact_has_max (E : Set ℝ)
    : E.Nonempty ∧ IsCompact421 E → ∃ x ∈ E, IsUpperBound x E := by
  contrapose
  intro hnomax
  push Not at hnomax
  push Not
  intro hnonempty
  unfold IsCompact421
  push Not
  intro hbdd
  unfold IsBounded at hbdd
  obtain ⟨_, hbdd⟩ := hbdd
  have hsup : ∃ M : ℝ, IsSupremum M E := sup_exists E hnonempty hbdd
  obtain ⟨M, hM⟩ := hsup
  have : M ∉ E := by by_contra hME; exact hnomax M hME hM.1
  have : IsBoundary M E := by unfold IsBoundary; intro r hr; constructor; (· by_contra hnone; (have htub : IsUpperBound (M - r / 2) E := by intro y hy; by_contra hgt; have hyM : y ≤ M := hM.1 y hy; (have hN : y ∈ Neighborhood M r := by change dist y M < r; rw [Real.dist_eq, abs_sub_comm]; rw [abs_of_nonneg (sub_nonneg.mpr hyM)]; linarith [lt_of_not_ge hgt]); have hm : y ∈ Neighborhood M r ∩ E := ⟨hN, hy⟩; rw [hnone] at hm; exact hm); exact (hM.2 (M - r / 2) (by linarith)) htub); · by_contra hnone; (have hMmem : M ∈ Neighborhood M r := by change dist M M < r; simp; exact hr); have hm : M ∈ Neighborhood M r ∩ Eᶜ := ⟨hMmem, this⟩; rw [hnone] at hm; exact hm
  have : ¬(Boundary E ⊆ E) := by intro hsub; (have hmemb : M ∈ Boundary E := by (change M ∈ { x | IsBoundary x E }); exact ‹IsBoundary M E›); exact ‹M ∉ E› (hsub hmemb)
  intro hclosed; (have hopen : IsOpen421 Eᶜ := by simpa [IsClosed421] using hclosed); have hdis : Eᶜ ∩ Boundary Eᶜ = ∅ := (open_iff_disjoint_from_boundary Eᶜ).mp hopen; have hbeq : Boundary Eᶜ = Boundary E := (boundary_of_set_equals_boundary_of_complement E).symm; rw [hbeq] at hdis; apply this; intro x hx; by_contra hnot; have hm : x ∈ Eᶜ ∩ Boundary E := ⟨hnot, hx⟩; rw [hdis] at hm; exact hm
  /-have hsupexists: ∃ M : ℝ, IsSupremum M E := by exact sup_exists E hnonempty hcompact.1.2
  obtain ⟨M, hM⟩ := hsupexists
  use M
  constructor
  · -/
