module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
public import ReciprocityTheory.ReducedBases.LatticeReduction

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SpanFlag
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.IndepOfFlag
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.RB

open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def V {d : ℕ} (u : Fin d → E) (n : ℕ) : Submodule ℝ E := span ℝ (u '' {l | l.val < n})

lemma V_mono {d : ℕ} (u : Fin d → E) {m n : ℕ} (h : m ≤ n) : V u m ≤ V u n := by
  exact Submodule.span_mono (Set.image_mono fun l hl => show l.val < n from lt_of_lt_of_le (show l.val < m from hl) h)

lemma V_eq {d : ℕ} (u : Fin d → E) (k : Fin d) : span ℝ (u '' Set.Iio k) = V u k.val := by
  first
  | rfl
  | (simp only [V]; congr 1; congr 1; ext l; exact Iff.rfl)

lemma mem_V_of_lt {d : ℕ} (u : Fin d → E) {l : Fin d} {n : ℕ} (h : l.val < n) : u l ∈ V u n := Submodule.subset_span ⟨l, h, rfl⟩

lemma finite_ball [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] (R : ℝ) :
    (Metric.closedBall (0 : E) R ∩ (X : Set E)).Finite := by
  haveI : DiscreteTopology X.toAddSubgroup := ‹DiscreteTopology X›
  have hc : IsClosed (X : Set E) := (X.toAddSubgroup).isClosed_of_discreteTopology
  have hdisc : IsDiscrete (X : Set E) := by
    first
    | exact ⟨‹DiscreteTopology X›⟩
    | exact isDiscrete_iff_discreteTopology.2 ‹DiscreteTopology X›
    | exact ‹DiscreteTopology X›
  exact Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hc

lemma indep_of_flag [FiniteDimensional ℝ E] {d : ℕ} (hd : d = finrank ℝ E) (f : Fin d → E)
    (h : ∀ k, f k ∉ V f k.val) : LinearIndependent ℝ f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  let s := Finset.univ.filter (fun l => g l ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [s, hi]⟩
  let k := s.max' hs
  have hk : g k ≠ 0 := by
    have := s.max'_mem hs
    simpa [s] using this
  have hgt : ∀ l, k < l → g l = 0 := by
    intro l hl
    by_contra h0
    exact absurd (s.le_max' l (by simp [s, h0])) (not_le.2 hl)
  have hsplit : ∀ l, g l • f l =
      (if l = k then g k • f k else 0) + (if l < k then g l • f l else 0) := by
    intro l
    rcases lt_trichotomy l k with h1 | h1 | h1
    · simp [h1, h1.ne]
    · rw [h1]; simp
    · simp [hgt l h1, h1.ne', not_lt.2 h1.le]
  have h2 : g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l = 0 := by
    have e : ∑ l, g l • f l = g k • f k + ∑ l ∈ Finset.univ.filter (· < k), g l • f l := by
      rw [Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => hsplit l), Finset.sum_add_distrib,
        Finset.sum_filter]
      simp
    rw [← e]
    exact hg
  have hmem : g k • f k ∈ V f k.val := by
    rw [eq_neg_of_add_eq_zero_left h2]
    refine Submodule.neg_mem _ (_root_.sum_mem fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩))
    have hl' : l < k := by simpa using hl
    exact Fin.lt_iff_val_lt_val.1 hl'
  have h3 := Submodule.smul_mem (V f k.val) (g k)⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ hk, one_smul] at h3
  exact h k h3

def phi {d : ℕ} (u : Fin d → E) (k : Fin d) (x : E) : ℝ := ⟪gs u k, x⟫_ℝ / ‖gs u k‖ ^ 2

section phi
variable {d : ℕ} (u : Fin d → E) (k : Fin d)

lemma phi_add (x y : E) : phi u k (x + y) = phi u k x + phi u k y := by
  simp only [phi, inner_add_right, add_div]

lemma phi_sub (x y : E) : phi u k (x - y) = phi u k x - phi u k y := by
  simp only [phi, inner_sub_right, sub_div]

lemma phi_smul (a : ℝ) (x : E) : phi u k (a • x) = a * phi u k x := by
  simp only [phi, real_inner_smul_right, mul_div_assoc]

private lemma inner_gs_eq_zero_of_mem_V {x : E} (hx : x ∈ V u k.val) : ⟪gs u k, x⟫_ℝ = 0 := by
  have hx' : x ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k) := by
    rw [span_gramSchmidt_Iio, V_eq]
    exact hx
  have hle : span ℝ (gramSchmidt ℝ u '' Set.Iio k) ≤ (ℝ ∙ gramSchmidt ℝ u k)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact gramSchmidt_orthogonal ℝ u (ne_of_gt hj)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hx')

lemma phi_V {x : E} (hx : x ∈ V u k.val) : phi u k x = 0 := by
  simp [phi, inner_gs_eq_zero_of_mem_V u k hx]

private lemma sub_gs_mem_V : u k - gs u k ∈ V u k.val := by
  rw [← V_eq, ← span_gramSchmidt_Iio ℝ u k]
  show u k - gramSchmidt ℝ u k ∈ span ℝ (gramSchmidt ℝ u '' Set.Iio k)
  rw [gramSchmidt_def ℝ u k, sub_sub_cancel]
  refine _root_.sum_mem fun i hi => ?_
  have hsub : (ℝ ∙ gramSchmidt ℝ u i) ≤ span ℝ (gramSchmidt ℝ u '' Set.Iio k) :=
    Submodule.span_mono (Set.singleton_subset_iff.2 ⟨i, Finset.mem_Iio.1 hi, rfl⟩)
  apply hsub
  first
  | exact Submodule.starProjection_apply_mem _ _
  | (rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _)
  | simp

lemma phi_self (hu : LinearIndependent ℝ u) : phi u k (u k) = 1 := by
  have hne : gs u k ≠ 0 := by
    first
    | exact gramSchmidt_ne_zero ℝ k hu
    | exact gramSchmidt_ne_zero k hu
    | exact gramSchmidt_ne_zero (𝕜 := ℝ) (n := k) hu
  have h1 : phi u k (u k) = phi u k (gs u k) + phi u k (u k - gs u k) := by
    rw [← phi_add]; congr 1; abel
  rw [h1, phi_V u k (sub_gs_mem_V u k), add_zero, phi, real_inner_self_eq_norm_sq,
    div_self (pow_ne_zero 2 (norm_ne_zero_iff.2 hne))]

lemma phi_comb (hu : LinearIndependent ℝ u) (a : Fin d → ℝ) (ha : ∀ l, k < l → a l = 0) :
    phi u k (∑ l, a l • u l) = a k := by
  have h : phi u k (∑ l, a l • u l) = ∑ l, a l * phi u k (u l) := by
    simp only [phi, inner_sum, real_inner_smul_right, Finset.sum_div, mul_div_assoc]
  rw [h, Finset.sum_eq_single k]
  · rw [phi_self u k hu, mul_one]
  · intro l _ hlk
    rcases lt_or_gt_of_ne hlk with h1 | h1
    · rw [phi_V u k (mem_V_of_lt u (Fin.lt_iff_val_lt_val.1 h1)), mul_zero]
    · rw [ha l h1, zero_mul]
  · simp

private lemma exists_coeffs_of_mem_V {d : ℕ} (u : Fin d → E) {n : ℕ} {x : E} (hx : x ∈ V u n) :
    ∃ c : Fin d → ℝ, (∀ l : Fin d, n ≤ l.val → c l = 0) ∧ x = ∑ l, c l • u l := by
  rw [V, Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨c, fun l hl => ?_, ?_⟩
  · by_contra h
    have := (Finsupp.mem_supported ℝ c).1 hc (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hl)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    exact zero_smul _ _

lemma decomp (hu : LinearIndependent ℝ u) {x : E} (hx : x ∈ V u (k.val + 1)) :
    x - phi u k x • u k ∈ V u k.val := by
  obtain ⟨c, hc, rfl⟩ := exists_coeffs_of_mem_V u hx
  rw [phi_comb u k hu c (fun l hl => hc l (Fin.lt_iff_val_lt_val.1 hl))]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), add_sub_cancel_left]
  refine _root_.sum_mem fun l hl => ?_
  have hlk : l ≠ k := Finset.ne_of_mem_erase hl
  rcases lt_or_gt_of_ne hlk with h1 | h1
  · exact Submodule.smul_mem _ _ (mem_V_of_lt u (Fin.lt_iff_val_lt_val.1 h1))
  · rw [hc l (Fin.lt_iff_val_lt_val.1 h1), zero_smul]
    exact Submodule.zero_mem _

end phi

lemma exists_coeffs {d : ℕ} (u : Fin d → E) {n : ℕ} {x : E} (hx : x ∈ V u n) :
    ∃ c : Fin d → ℝ, (∀ l : Fin d, n ≤ l.val → c l = 0) ∧ x = ∑ l, c l • u l := exists_coeffs_of_mem_V u hx

private lemma norm_add_smul_sq_of_real_inner_eq_zero (a g : E) (t : ℝ) (h : ⟪g, a⟫_ℝ = 0) :
    ‖a + t • g‖ ^ 2 = ‖a‖ ^ 2 + t ^ 2 * ‖g‖ ^ 2 := by
  have h' : ⟪a, g⟫_ℝ = 0 := by rw [real_inner_comm]; exact h
  rw [norm_add_sq_real, real_inner_smul_right, h', mul_zero, mul_zero, add_zero, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]

private lemma norm_gs_sq_le_norm_sq {d : ℕ} (u : Fin d → E) (k : Fin d) : ‖gs u k‖ ^ 2 ≤ ‖u k‖ ^ 2 := by
  have h := norm_add_smul_sq_of_real_inner_eq_zero (u k - gs u k) (gs u k) 1 (inner_gs_eq_zero_of_mem_V u k (sub_gs_mem_V u k))
  rw [one_smul, sub_add_cancel, one_pow, one_mul] at h
  rw [h]
  nlinarith [sq_nonneg ‖u k - gs u k‖]

private lemma exists_lattice_mem_V_norm_sub_sq_le {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (hX : ∀ l, u l ∈ X) (M : ℝ) (N : ℕ) (hN : N ≤ d) (hM : ∀ j : Fin d, j.val < N → ‖u j‖ ^ 2 ≤ M) :
    ∀ n : ℕ, n ≤ N → ∀ w ∈ V u n, ∃ z ∈ X, z ∈ V u n ∧ ‖w - z‖ ^ 2 ≤ n * M := by
  intro n
  induction n with
  | zero =>
    intro _ w hw
    refine ⟨0, X.zero_mem, Submodule.zero_mem _, ?_⟩
    have h0 : V u 0 = ⊥ := by simp [V]
    rw [h0, Submodule.mem_bot] at hw
    simp [hw]
  | succ n ih =>
    intro hn w hw
    have hjn : n < d := by omega
    let j : Fin d := ⟨n, hjn⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, |phi u j w - m| ≤ 1 :=
      ⟨round (phi u j w), by have := abs_sub_round (phi u j w); linarith⟩
    have hw1 : w - (m : ℝ) • u j ∈ V u (j.val + 1) :=
      Submodule.sub_mem _ hw (Submodule.smul_mem _ _ (mem_V_of_lt u (Nat.lt_succ_self n)))
    have ht : phi u j (w - (m : ℝ) • u j) = phi u j w - m := by
      rw [phi_sub, phi_smul, phi_self u j hu, mul_one]
    have hw2 : w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j ∈ V u n := by
      have h1 := decomp u j hu hw1
      have h2 : phi u j (w - (m : ℝ) • u j) • (u j - gs u j) ∈ V u n :=
        Submodule.smul_mem _ _ (sub_gs_mem_V u j)
      have h3 := Submodule.add_mem _ h1 h2
      have h4 : w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j =
          (w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • u j) +
            phi u j (w - (m : ℝ) • u j) • (u j - gs u j) := by
        rw [smul_sub]; abel
      rw [h4]; exact h3
    obtain ⟨z, hzX, hzV, hz⟩ := ih (by omega) _ hw2
    refine ⟨(m : ℝ) • u j + z, ?_, ?_, ?_⟩
    · rw [Int.cast_smul_eq_zsmul]
      exact X.add_mem (X.smul_mem m (hX j)) hzX
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (mem_V_of_lt u (Nat.lt_succ_self n)))
        (V_mono u (Nat.le_succ n) hzV)
    · have hsplit : w - ((m : ℝ) • u j + z) =
          (w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j - z) +
            phi u j (w - (m : ℝ) • u j) • gs u j := by abel
      have horth : ⟪gs u j, w - (m : ℝ) • u j - phi u j (w - (m : ℝ) • u j) • gs u j - z⟫_ℝ = 0 :=
        inner_gs_eq_zero_of_mem_V u j (Submodule.sub_mem _ hw2 hzV)
      rw [hsplit, norm_add_smul_sq_of_real_inner_eq_zero _ _ _ horth]
      have ht2 : phi u j (w - (m : ℝ) • u j) ^ 2 ≤ 1 := by
        rw [ht]
        have := abs_le.1 hm
        nlinarith
      have hMj : ‖u j‖ ^ 2 ≤ M := hM j (show n < N by omega)
      have hprod : phi u j (w - (m : ℝ) • u j) ^ 2 * ‖gs u j‖ ^ 2 ≤ 1 * M :=
        mul_le_mul ht2 ((norm_gs_sq_le_norm_sq u j).trans hMj) (by positivity) zero_le_one
      push_cast
      nlinarith

lemma reduce {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (hX : ∀ l, u l ∈ X) (k : Fin d) (hmono : ∀ j : Fin d, j < k → ‖u j‖ ≤ ‖u k‖) {x : E}
    (hxX : x ∈ X) (hxV : x ∈ V u (k.val + 1)) (hphi : |phi u k x| ≤ 1) :
    ∃ y ∈ X, y ∈ V u (k.val + 1) ∧ phi u k y = phi u k x ∧ ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2 := by
  have hkd : k.val < d := k.isLt
  have hM : ∀ j : Fin d, j.val < k.val → ‖u j‖ ^ 2 ≤ ‖u k‖ ^ 2 := fun j hj =>
    pow_le_pow_left₀ (norm_nonneg _) (hmono j (Fin.lt_iff_val_lt_val.2 hj)) 2
  have hw2 : x - phi u k x • gs u k ∈ V u k.val := by
    have h1 := decomp u k hu hxV
    have h2 : phi u k x • (u k - gs u k) ∈ V u k.val :=
      Submodule.smul_mem _ _ (sub_gs_mem_V u k)
    have h3 : x - phi u k x • gs u k = (x - phi u k x • u k) + phi u k x • (u k - gs u k) := by
      rw [smul_sub]; abel
    rw [h3]; exact Submodule.add_mem _ h1 h2
  obtain ⟨z, hzX, hzV, hz⟩ :=
    exists_lattice_mem_V_norm_sub_sq_le u hu X hX (‖u k‖ ^ 2) k.val hkd.le hM k.val le_rfl _ hw2
  refine ⟨x - z, X.sub_mem hxX hzX, Submodule.sub_mem _ hxV (V_mono u (Nat.le_succ _) hzV), ?_, ?_⟩
  · rw [phi_sub, phi_V u k hzV, sub_zero]
  · have hsplit : x - z = (x - phi u k x • gs u k - z) + phi u k x • gs u k := by abel
    rw [hsplit, norm_add_smul_sq_of_real_inner_eq_zero _ _ _ (inner_gs_eq_zero_of_mem_V u k (Submodule.sub_mem _ hw2 hzV))]
    have hp2 : phi u k x ^ 2 ≤ 1 := by
      have := abs_le.1 hphi
      nlinarith
    have hprod : phi u k x ^ 2 * ‖gs u k‖ ^ 2 ≤ 1 * ‖u k‖ ^ 2 :=
      mul_le_mul hp2 (norm_gs_sq_le_norm_sq u k) (by positivity) zero_le_one
    have hd : (k.val : ℝ) + 1 ≤ d := by exact_mod_cast hkd
    have hu0 : 0 ≤ ‖u k‖ ^ 2 := by positivity
    nlinarith

end ReciprocityTheory.ChartRestriction.G.H1.RB
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1.RB

open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma greedy [FiniteDimensional ℝ E] (X : Submodule ℤ E) [DiscreteTopology X] {d : ℕ}
    (v : Fin d → E) (hv : LinearIndependent ℝ v) (hvX : ∀ i, v i ∈ X) :
    ∃ u : Fin d → E, ∀ k : Fin d, u k ∈ X ∧ u k ∉ V u k.val ∧ (∃ i, ‖u k‖ ≤ ‖v i‖) ∧
      ∀ z ∈ X, z ∉ V u k.val → ‖u k‖ ≤ ‖z‖ := by
  classical
  have hstep : ∀ (u : Fin d → E) (n : ℕ), n < d → ∃ w ∈ X, w ∉ V u n ∧ (∃ i, ‖w‖ ≤ ‖v i‖) ∧
      ∀ z ∈ X, z ∉ V u n → ‖w‖ ≤ ‖z‖ := by
    intro u n hn
    have hex : ∃ i, v i ∉ V u n := by
      by_contra h
      push_neg at h
      have hle : span ℝ (Set.range v) ≤ V u n :=
        span_le.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
      have h1 : finrank ℝ (span ℝ (Set.range v)) = d := by
        rw [finrank_span_eq_card hv, Fintype.card_fin]
      have h2 : finrank ℝ (V u n) ≤ n := by
        have hV : V u n = span ℝ (Set.range (fun i : Fin n => u (Fin.castLE hn.le i))) := by
          unfold V
          congr 1
          ext x
          simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
          constructor
          · rintro ⟨l, hl, rfl⟩
            exact ⟨⟨l.val, hl⟩, rfl⟩
          · rintro ⟨i, rfl⟩
            exact ⟨Fin.castLE hn.le i, i.isLt, rfl⟩
        rw [hV]
        exact (finrank_range_le_card _).trans (by simp)
      have h3 := Submodule.finrank_mono hle
      omega
    obtain ⟨i0, hi0⟩ := hex
    have hAfin : {z : E | z ∈ X ∧ z ∉ V u n ∧ ‖z‖ ≤ ‖v i0‖}.Finite :=
      (finite_ball X ‖v i0‖).subset (by
        rintro z ⟨hzX, -, hz⟩
        exact ⟨mem_closedBall_zero_iff.mpr hz, hzX⟩)
    obtain ⟨w, ⟨hwX, hwV, hwle⟩, hwmin⟩ :=
      Set.exists_min_image _ (fun z => ‖z‖) hAfin ⟨v i0, hvX i0, hi0, le_rfl⟩
    refine ⟨w, hwX, hwV, ⟨i0, hwle⟩, fun z hzX hzV => ?_⟩
    by_cases hz : ‖z‖ ≤ ‖v i0‖
    · exact hwmin z ⟨hzX, hzV, hz⟩
    · exact hwle.trans (le_of_not_ge hz)
  have hVupd : ∀ (u : Fin d → E) (i : Fin d) (w : E) (n : ℕ), n ≤ i.val →
      V (Function.update u i w) n = V u n := by
    intro u i w n hn
    unfold V
    congr 1
    apply Set.image_congr
    intro l hl
    have hli : l ≠ i := by
      intro h
      subst h
      simp only [Set.mem_setOf_eq] at hl
      omega
    simp [Function.update_of_ne hli]
  have key : ∀ n ≤ d, ∃ u : Fin d → E, ∀ k : Fin d, k.val < n → (u k ∈ X ∧ u k ∉ V u k.val ∧
      (∃ i, ‖u k‖ ≤ ‖v i‖) ∧ ∀ z ∈ X, z ∉ V u k.val → ‖u k‖ ≤ ‖z‖) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨fun _ => 0, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨u, hu⟩ := ih (by omega)
      obtain ⟨w, hw⟩ := hstep u n (by omega)
      refine ⟨Function.update u ⟨n, by omega⟩ w, fun k hk => ?_⟩
      rw [hVupd u ⟨n, by omega⟩ w k.val (by show k.val ≤ n; omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · have hki : k ≠ ⟨n, by omega⟩ := by
          intro h
          rw [h] at hk
          exact lt_irrefl _ hk
        rw [Function.update_of_ne hki]
        exact hu k hk
      · have hki : k = ⟨n, by omega⟩ := Fin.ext hk
        rw [hki, Function.update_self]
        exact hw
  obtain ⟨u, hu⟩ := key d le_rfl
  exact ⟨u, fun k => hu k k.isLt⟩

lemma exists_b [FiniteDimensional ℝ E] {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u)
    (X : Submodule ℤ E) [DiscreteTopology X] (hX : ∀ l, u l ∈ X) (k : Fin d)
    (hmono : ∀ j : Fin d, j < k → ‖u j‖ ≤ ‖u k‖) :
    ∃ b : E, b ∈ X ∧ b ∈ V u (k.val + 1) ∧ 0 < phi u k b ∧ phi u k b ≤ 1 ∧
      (∀ x ∈ X, x ∈ V u (k.val + 1) → 0 < phi u k x → phi u k x ≤ 1 → phi u k b ≤ phi u k x) ∧
      (∀ x ∈ X, x ∈ V u (k.val + 1) → phi u k x = phi u k b → ‖b‖ ≤ ‖x‖) ∧
      ‖b‖ ^ 2 ≤ d * ‖u k‖ ^ 2 := by
  classical
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_of_lt k.pos
  have hR : 0 ≤ Real.sqrt d * ‖u k‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hBfin : {y : E | y ∈ X ∧ y ∈ V u (k.val + 1) ∧ 0 < phi u k y ∧ phi u k y ≤ 1 ∧
      ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2}.Finite :=
    (finite_ball X (Real.sqrt d * ‖u k‖)).subset (by
      rintro y ⟨hyX, -, -, -, hy⟩
      refine ⟨mem_closedBall_zero_iff.mpr ?_, hyX⟩
      have h2 : ‖y‖ ^ 2 ≤ (Real.sqrt d * ‖u k‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
        exact hy
      by_contra hc
      push_neg at hc
      nlinarith [norm_nonneg y])
  have hBne : ({y : E | y ∈ X ∧ y ∈ V u (k.val + 1) ∧ 0 < phi u k y ∧ phi u k y ≤ 1 ∧
      ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2}).Nonempty :=
    ⟨u k, hX k, mem_V_of_lt u (Nat.lt_succ_self _), by rw [phi_self u k hu]; exact one_pos,
      (phi_self u k hu).le, le_mul_of_one_le_left (sq_nonneg _) hd⟩
  obtain ⟨b0, hb0B, hb0min⟩ := Set.exists_min_image _ (phi u k) hBfin hBne
  have hCfin : {y : E | (y ∈ X ∧ y ∈ V u (k.val + 1) ∧ 0 < phi u k y ∧ phi u k y ≤ 1 ∧
      ‖y‖ ^ 2 ≤ d * ‖u k‖ ^ 2) ∧ phi u k y = phi u k b0}.Finite :=
    hBfin.subset (fun y hy => hy.1)
  obtain ⟨b, ⟨⟨hbX, hbV, hb0, hb1, hbd⟩, hbphi⟩, hbmin⟩ :=
    Set.exists_min_image _ (fun y => ‖y‖) hCfin ⟨b0, hb0B, rfl⟩
  refine ⟨b, hbX, hbV, hb0, hb1, ?_, ?_, hbd⟩
  · intro x hxX hxV h0 h1
    obtain ⟨y, hyX, hyV, hyphi, hyd⟩ :=
      reduce u hu X hX k hmono hxX hxV (abs_le.mpr ⟨by linarith, h1⟩)
    have hy0 : 0 < phi u k y := by rw [hyphi]; exact h0
    have hy1 : phi u k y ≤ 1 := by rw [hyphi]; exact h1
    rw [hbphi, ← hyphi]
    exact hb0min y ⟨hyX, hyV, hy0, hy1, hyd⟩
  · intro x hxX hxV hx
    by_cases hxd : ‖x‖ ^ 2 ≤ d * ‖u k‖ ^ 2
    · have hx0 : 0 < phi u k x := by rw [hx]; exact hb0
      have hx1 : phi u k x ≤ 1 := by rw [hx]; exact hb1
      exact hbmin x ⟨⟨hxX, hxV, hx0, hx1, hxd⟩, hx.trans hbphi⟩
    · push_neg at hxd
      have hlt : ‖b‖ ^ 2 < ‖x‖ ^ 2 := lt_of_le_of_lt hbd hxd
      by_contra hc
      push_neg at hc
      nlinarith [norm_nonneg b, norm_nonneg x]

lemma span_flag {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (b : Fin d → E) (hbX : ∀ k, b k ∈ X) (hbV : ∀ k : Fin d, b k ∈ V u (k.val + 1))
    (hb0 : ∀ k, 0 < phi u k (b k)) (hb1 : ∀ k, phi u k (b k) ≤ 1)
    (hbmin : ∀ k : Fin d, ∀ x ∈ X, x ∈ V u (k.val + 1) → 0 < phi u k x → phi u k x ≤ 1 →
      phi u k (b k) ≤ phi u k x) :
    ∀ n ≤ d, ∀ x ∈ X, x ∈ V u n → x ∈ span ℤ (Set.range b) := by
  intro n
  induction n with
  | zero =>
    intro _ x _ hx
    obtain ⟨c, hc, rfl⟩ := exists_coeffs u hx
    have hc0 : ∀ l, c l = 0 := fun l => hc l (Nat.zero_le _)
    simp [hc0]
  | succ n ih =>
    intro hn x hxX hxV
    have hkV : x ∈ V u ((⟨n, by omega⟩ : Fin d).val + 1) := hxV
    have htpos : 0 < phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩) := hb0 _
    obtain ⟨q, hq⟩ : ∃ q : ℤ, q = ⌊phi u ⟨n, by omega⟩ x / phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩)⌋ :=
      ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y : E, y = x - (q : ℝ) • b ⟨n, by omega⟩ := ⟨_, rfl⟩
    have hyX : y ∈ X := by
      rw [hy, Int.cast_smul_eq_zsmul]
      exact X.sub_mem hxX (X.smul_mem q (hbX _))
    have hyV : y ∈ V u ((⟨n, by omega⟩ : Fin d).val + 1) := by
      rw [hy]
      exact Submodule.sub_mem _ hkV (Submodule.smul_mem _ _ (hbV _))
    have hyphi : phi u ⟨n, by omega⟩ y =
        phi u ⟨n, by omega⟩ x - q * phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩) := by
      rw [hy, phi_sub, phi_smul]
    have hlo : 0 ≤ phi u ⟨n, by omega⟩ y := by
      rw [hyphi]
      have h1 := Int.floor_le (phi u ⟨n, by omega⟩ x / phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩))
      rw [← hq] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 htpos.le
      rw [div_mul_cancel₀ _ htpos.ne'] at h2
      linarith
    have hhi : phi u ⟨n, by omega⟩ y < phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩) := by
      rw [hyphi]
      have h1 := Int.lt_floor_add_one
        (phi u ⟨n, by omega⟩ x / phi u ⟨n, by omega⟩ (b ⟨n, by omega⟩))
      rw [← hq] at h1
      have h2 := mul_lt_mul_of_pos_right h1 htpos
      rw [div_mul_cancel₀ _ htpos.ne'] at h2
      linarith
    have hy0 : phi u ⟨n, by omega⟩ y = 0 := by
      by_contra hne
      have hpos : 0 < phi u ⟨n, by omega⟩ y := lt_of_le_of_ne hlo (Ne.symm hne)
      have h3 := hbmin _ y hyX hyV hpos (hhi.le.trans (hb1 _))
      linarith
    have hyVn : y ∈ V u n := by
      have h4 := decomp u ⟨n, by omega⟩ hu hyV
      rwa [hy0, zero_smul, sub_zero] at h4
    have hyspan := ih (by omega) y hyX hyVn
    have hxy : x = y + q • b ⟨n, by omega⟩ := by
      rw [hy, Int.cast_smul_eq_zsmul]
      abel
    rw [hxy]
    exact (span ℤ (Set.range b)).add_mem hyspan
      ((span ℤ (Set.range b)).smul_mem q (subset_span ⟨_, rfl⟩))

end ReciprocityTheory.ChartRestriction.G.H1.RB
end
end

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module

theorem reducedBasis_holds : ReducedBasisStatement := by
  intro E _ _ _ X _ _ M v hv hvX hvM
  classical
  obtain ⟨u, hu⟩ := RB.greedy X v hv hvX
  have huX : ∀ k, u k ∈ X := fun k => (hu k).1
  have huV : ∀ k : Fin (finrank ℝ E), u k ∉ RB.V u k.val := fun k => (hu k).2.1
  have hli : LinearIndependent ℝ u := RB.indep_of_flag rfl u huV
  have hmono : ∀ k j : Fin (finrank ℝ E), j < k → ‖u j‖ ≤ ‖u k‖ := by
    intro k j hjk
    apply (hu j).2.2.2 (u k) (huX k)
    intro hmem
    exact huV k (RB.V_mono u (Fin.lt_iff_val_lt_val.1 hjk).le hmem)
  have hb := fun k => RB.exists_b u hli X huX k (fun j hj => hmono k j hj)
  choose b hbX hbV hb0 hb1 hbmin hbnrm hbd using hb
  have hspan := RB.span_flag u hli X b hbX hbV hb0 hb1 hbmin
  have hVtop : RB.V u (finrank ℝ E) = ⊤ := by
    have h1 : RB.V u (finrank ℝ E) = Submodule.span ℝ (Set.range u) := by
      simp only [RB.V]
      congr 1
      ext x
      simp
    rw [h1]
    first
    | exact hli.span_eq_top_of_card_eq_finrank (by simp)
    | exact hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hbnot : ∀ k : Fin (finrank ℝ E), b k ∉ RB.V b k.val := by
    intro k hmem
    have hsub : RB.V b k.val ≤ RB.V u k.val := by
      rw [RB.V, Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact RB.V_mono u (show l.val + 1 ≤ k.val from hl) (hbV l)
    have h0 := RB.phi_V u k (hsub hmem)
    exact (hb0 k).ne' h0
  have hliR : LinearIndependent ℝ b := RB.indep_of_flag rfl b hbnot
  have hliZ : LinearIndependent ℤ b := by
    first
    | exact hliR.restrict_scalars' ℤ
    | exact hliR.restrict_scalars (fun a c h => by simpa using h)
  let bX : Fin (finrank ℝ E) → X := fun k => ⟨b k, hbX k⟩
  have hliX : LinearIndependent ℤ bX := LinearIndependent.of_comp X.subtype hliZ
  have hspX : ⊤ ≤ Submodule.span ℤ (Set.range bX) := by
    rintro x -
    have hx := hspan (finrank ℝ E) le_rfl x.1 x.2 (by rw [hVtop]; exact Submodule.mem_top)
    have hrange : Set.range b = X.subtype '' Set.range bX := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  let B := Basis.mk hliX hspX
  have hBj : ∀ j, (B j : E) = b j := fun j => by
    simp only [B, Basis.mk_apply, bX]
  refine ⟨B, ?_, ?_⟩
  · intro j
    rw [hBj]
    obtain ⟨i, hi⟩ := (hu j).2.2.1
    have h1 := hbd j
    have h2 : ‖u j‖ ^ 2 ≤ ‖v i‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
    have h3 := hvM i
    have hd0 : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h2 hd0, mul_le_mul_of_nonneg_left h3 hd0]
  · intro j z hz
    rw [hBj]
    by_cases hzV : z ∈ RB.V u j.val
    · have hzV1 : z ∈ RB.V u (j.val + 1) := RB.V_mono u (Nat.le_succ _) hzV
      have hphz : RB.phi u j z = 0 := RB.phi_V u j hzV
      have hp : ‖b j‖ ≤ ‖b j + z‖ := hbnrm j (b j + z) (X.add_mem (hbX j) hz)
        (Submodule.add_mem _ (hbV j) hzV1) (by rw [RB.phi_add, hphz, add_zero])
      have hm : ‖b j‖ ≤ ‖b j - z‖ := hbnrm j (b j - z) (X.sub_mem (hbX j) hz)
        (Submodule.sub_mem _ (hbV j) hzV1) (by rw [RB.phi_sub, hphz, sub_zero])
      have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      have hm2 := pow_le_pow_left₀ (norm_nonneg _) hm 2
      rw [norm_add_sq_real] at hp2
      rw [norm_sub_sq_real] at hm2
      have hz0 : 0 ≤ ‖z‖ ^ 2 := by positivity
      have hd1 : (1 : ℝ) ≤ Real.sqrt (finrank ℝ E) := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_of_lt (Fin.pos j))
      rw [abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_right hd1 hz0]
    · have hle : ‖u j‖ ≤ ‖z‖ := (hu j).2.2.2 z hz hzV
      have hb' : ‖b j‖ ≤ Real.sqrt (finrank ℝ E) * ‖u j‖ := by
        calc ‖b j‖ = Real.sqrt (‖b j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt ((finrank ℝ E : ℝ) * ‖u j‖ ^ 2) := Real.sqrt_le_sqrt (hbd j)
          _ = Real.sqrt (finrank ℝ E) * ‖u j‖ := by
            rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      calc |inner ℝ (b j) z| ≤ ‖b j‖ * ‖z‖ := abs_real_inner_le_norm _ _
        _ ≤ (Real.sqrt (finrank ℝ E) * ‖u j‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
        _ ≤ (Real.sqrt (finrank ℝ E) * ‖z‖) * ‖z‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _))
            (norm_nonneg _)
        _ = 2 * Real.sqrt (finrank ℝ E) * (‖z‖ ^ 2 / 2) := by ring

end ReciprocityTheory.ChartRestriction.G.H1
