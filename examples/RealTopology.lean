import Mathlib.Basic.Real.Basic
--import Mathlib.Algebra.Order.Archimedean.Real.Basic
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

/-theorem center_of_neighborhood_is_member
    {S} [MetricSpace S] (x : S) (r : ℝ) (hr : 0 < r)
    : x ∈ Neighborhood x r := by
  unfold Neighborhood
  norm_num
  exact hr-/

/-theorem interior_implies_member
    {S} [MetricSpace S] (x : S) (E : Set S) (h : IsInteriorTo x E) : x ∈ E := by
  unfold IsInteriorTo at h
  obtain ⟨r, hr⟩ := h
  have : x ∈ Neighborhood x r := center_of_neighborhood_is_member x r (hr.1)
  tauto-/

open Set

-- Theorem. The left endpoint of any closed interval
-- [a, b] is not interior to the interval.
theorem left_endpoint_of_closed_interval_is_not_interior
    {a : ℝ} {b : ℝ} : ¬(IsInteriorTo a (Icc a b)) := by
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
