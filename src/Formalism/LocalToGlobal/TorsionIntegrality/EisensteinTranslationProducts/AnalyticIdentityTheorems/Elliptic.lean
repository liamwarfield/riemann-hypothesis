module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

theorem elliptic_entire_const : EllipticEntire := by
  intro L f hf hper z
  have key : ∀ x : ℂ, ∃ ω ∈ L.lattice, ‖x - ω‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ := by
    intro x
    have hx := L.basis.sum_repr x
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at hx
    refine ⟨(⌊L.basis.repr x 0⌋ : ℂ) * L.ω₁ + (⌊L.basis.repr x 1⌋ : ℂ) * L.ω₂,
      PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩, ?_⟩
    generalize L.basis.repr x 0 = a at hx ⊢
    generalize L.basis.repr x 1 = b at hx ⊢
    subst hx
    have e : a • L.ω₁ + b • L.ω₂ - ((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂)
        = ((Int.fract a : ℝ) : ℂ) * L.ω₁ + ((Int.fract b : ℝ) : ℂ) * L.ω₂ := by
      simp only [Complex.real_smul, Int.fract]; push_cast; ring
    rw [e]
    have hfr : ∀ (r : ℝ) (v : ℂ), ‖((Int.fract r : ℝ) : ℂ) * v‖ ≤ ‖v‖ := by
      intro r v
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    exact (norm_add_le _ _).trans (add_le_add (hfr a _) (hfr b _))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (‖L.ω₁‖ + ‖L.ω₂‖)).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  have hb : Bornology.IsBounded (Set.range f) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    rintro _ ⟨x, rfl⟩
    obtain ⟨ω, hω, hxω⟩ := key x
    have : f x = f (x - ω) := by
      have := hper ω hω (x - ω)
      rwa [sub_add_cancel] at this
    rw [this]
    exact hC _ (by simpa using hxω)
  exact hf.apply_eq_apply_of_bounded hb z 0

namespace Elliptic

lemma eq_of_eventuallyEq_nhdsNE {g₁ g₂ : ℂ → ℂ} {z : ℂ} (h₁ : ContinuousAt g₁ z)
    (h₂ : ContinuousAt g₂ z) (h : g₁ =ᶠ[𝓝[≠] z] g₂) : g₁ z = g₂ z :=
  tendsto_nhds_unique (h₁.tendsto.mono_left nhdsWithin_le_nhds)
    ((h₂.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

lemma tendsto_add_nhdsNE (z ω : ℂ) : Tendsto (fun w : ℂ => w + ω) (𝓝[≠] z) (𝓝[≠] (z + ω)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨((continuous_add_const ω).tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun h => hw (add_right_cancel h)

end Elliptic

theorem elliptic_no_pole_const : EllipticNoPole := by
  intro L f hmer hper hord
  have hM : MeromorphicOn f Set.univ := fun z _ => hmer z
  set g := toMeromorphicNFOn f Set.univ with hg_def
  have heq : ∀ z, g =ᶠ[𝓝[≠] z] f := fun z =>
    hM.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han : ∀ z, AnalyticAt ℂ g z := fun z => by
    have hnf := meromorphicNFOn_toMeromorphicNFOn f Set.univ (Set.mem_univ z)
    rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt, meromorphicOrderAt_congr (heq z)]
    exact hord z
  have hcont : ∀ z, ContinuousAt g z := fun z => (han z).continuousAt
  have hdiff : Differentiable ℂ g := fun z => (han z).differentiableAt
  have hpg : IsPeriodic L g := by
    intro ω hω z
    have hc1 : ContinuousAt (fun w => g (w + ω)) z :=
      show ContinuousAt (g ∘ fun w => w + ω) z from
        (hcont (z + ω)).comp_of_eq (continuous_add_const ω).continuousAt rfl
    have h1 : ∀ᶠ w in 𝓝[≠] z, g (w + ω) = f (w + ω) :=
      (Elliptic.tendsto_add_nhdsNE z ω).eventually (heq (z + ω))
    have h2 : (fun w => g (w + ω)) =ᶠ[𝓝[≠] z] g := by
      filter_upwards [h1, heq z] with w hw1 hw2
      rw [hw1, hper ω hω w, hw2]
    exact Elliptic.eq_of_eventuallyEq_nhdsNE hc1 (hcont z) h2
  refine ⟨g 0, fun z hz => ?_⟩
  rw [← elliptic_entire_const L g hdiff hpg z]
  exact Elliptic.eq_of_eventuallyEq_nhdsNE hz (hcont z) (heq z).symm

end Formalism.L2.Th1.F
end
end

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
noncomputable section
open scoped Topology

namespace Formalism.L2.Th1.F

namespace PDeriv

lemma hasDerivAt_P (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd := (L.differentiableOn_weierstrassP.differentiableAt
    (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  rwa [L.deriv_weierstrassP] at hd

lemma eventually_notMem (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz

lemma notMem_of_rat (L : PeriodPair) (α β : ℚ) {x : ℂ} (hx : x = α * L.ω₁ + β * L.ω₂)
    (h : ¬ (α.den = 1 ∧ β.den = 1)) : x ∉ L.lattice := by
  intro hmem
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hmem
  rw [hx] at hmn
  have key := (LinearIndependent.pair_iff.mp L.indep) ((α : ℝ) - m) ((β : ℝ) - n) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination -hmn)
  have ha : α = m := by exact_mod_cast sub_eq_zero.mp key.1
  have hb : β = n := by exact_mod_cast sub_eq_zero.mp key.2
  exact h ⟨by rw [ha]; simp, by rw [hb]; simp⟩

lemma disc_alg (g2 g3 e1 e2 e3 : ℂ) (h1 : 4 * e1 ^ 3 - g2 * e1 - g3 = 0)
    (h2 : 4 * e2 ^ 3 - g2 * e2 - g3 = 0) (h3 : 4 * e3 ^ 3 - g2 * e3 - g3 = 0)
    (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3) : g2 ^ 3 - 27 * g3 ^ 2 ≠ 0 := by
  have hA : g2 = 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) := by
    have h0 : (e1 - e2) * (4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) - g2) = 0 := by
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h12
    · linear_combination -h
  have hB : g2 = 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) := by
    have h0 : (e1 - e3) * (4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) - g2) = 0 := by
      linear_combination h1 - h3
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h13
    · linear_combination -h
  have hS : e1 + e2 + e3 = 0 := by
    have h0 : (e2 - e3) * (e1 + e2 + e3) = 0 := by linear_combination (hB - hA) / 4
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) h23
    · exact h
  have hD : g2 ^ 3 - 27 * g3 ^ 2 = 16 * ((e1 - e2) * (e1 - e3) * (e2 - e3)) ^ 2 := by
    have h3' : e3 = -e1 - e2 := by linear_combination hS
    have hg3 : g3 = 4 * e1 ^ 3 - g2 * e1 := by linear_combination -h1
    rw [hg3, hA, h3']
    ring
  rw [hD]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero
    (sub_ne_zero.mpr h12) (sub_ne_zero.mpr h13)) (sub_ne_zero.mpr h23)))

end PDeriv

open PDeriv

theorem sigmaDouble_of (h : SigmaAdd) (he : SigmaEntire) (hs : SigmaSimple) : SigmaDouble := by
  intro L z hz
  have h0 : wSigma L 0 = 0 := by simp only [wSigma, zero_mul]
  have hd : ∀ x, HasDerivAt (wSigma L) (deriv (wSigma L) x) x := fun x => (he L x).hasDerivAt
  have hF := (HasDerivAt.comp z (hd (z + z)) ((hasDerivAt_id' z).const_add z)).mul
    (HasDerivAt.comp z (hd (z - z)) ((hasDerivAt_id' z).const_sub z))
  have hG := ((((hd z).mul (hd z)).const_mul (wSigma L z ^ 2)).mul
    ((hasDerivAt_P L hz).const_sub (L.weierstrassP z))).neg
  have hG' : HasDerivAt (fun w => wSigma L (z + w) * wSigma L (z - w)) _ z :=
    hG.congr_of_eventuallyEq ((eventually_notMem L hz).mono fun w hw => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L z w hz hw]
      ring)
  have key := hF.unique hG'
  simp only [Function.comp_apply, Pi.mul_apply, sub_self, h0, (hs L).1] at key
  rw [two_mul]
  linear_combination -key

theorem pDerivZero_of (h : SigmaDouble) (hz : SigmaZero) : PDerivZero := by
  intro L z hz'
  have hσ : wSigma L z ≠ 0 := fun h0 => hz' ((hz L z).mp h0)
  rw [← hz L (2 * z), h L z hz']
  simp [hσ]

theorem discNeZero_of (hp : PDerivZero) (hi : PInjective) : DiscNeZero := by
  intro L
  have root : ∀ x, x ∉ L.lattice → 2 * x ∈ L.lattice →
      4 * L.weierstrassP x ^ 3 - L.g₂ * L.weierstrassP x - L.g₃ = 0 := by
    intro x hx h2
    have hsq := L.derivWeierstrassP_sq x hx
    rw [(hp L x hx).mpr h2] at hsq
    linear_combination -hsq
  have ne : ∀ x y, x ∉ L.lattice → y ∉ L.lattice → x - y ∉ L.lattice → x + y ∉ L.lattice →
      L.weierstrassP x ≠ L.weierstrassP y := fun x y hx hy h1 h2 he =>
    ((hi L x y hx hy).mp he).elim h1 h2
  have hw1 : L.ω₁ ∈ L.lattice := L.ω₁_mem_lattice
  have hw2 : L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨0, 1, by push_cast; ring⟩
  have n1 : L.ω₁ / 2 ∉ L.lattice :=
    notMem_of_rat L 2⁻¹ 0 (by push_cast; ring) (by first | decide | norm_num | simp)
  have n2 : L.ω₂ / 2 ∉ L.lattice :=
    notMem_of_rat L 0 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)
  have n3 : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice :=
    notMem_of_rat L 2⁻¹ 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)
  have d1 : 2 * (L.ω₁ / 2) ∈ L.lattice := by
    rw [show 2 * (L.ω₁ / 2) = L.ω₁ by ring]
    exact hw1
  have d2 : 2 * (L.ω₂ / 2) ∈ L.lattice := by
    rw [show 2 * (L.ω₂ / 2) = L.ω₂ by ring]
    exact hw2
  have d3 : 2 * ((L.ω₁ + L.ω₂) / 2) ∈ L.lattice := by
    rw [show 2 * ((L.ω₁ + L.ω₂) / 2) = L.ω₁ + L.ω₂ by ring]
    exact add_mem hw1 hw2
  exact disc_alg _ _ _ _ _ (root _ n1 d1) (root _ n2 d2) (root _ n3 d3)
    (ne _ _ n1 n2 (notMem_of_rat L 2⁻¹ (-2⁻¹) (by push_cast; ring) (by first | decide | norm_num | simp))
      (notMem_of_rat L 2⁻¹ 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)))
    (ne _ _ n1 n3 (notMem_of_rat L 0 (-2⁻¹) (by push_cast; ring) (by first | decide | norm_num | simp))
      (notMem_of_rat L 1 2⁻¹ (by push_cast; ring) (by first | decide | norm_num | simp)))
    (ne _ _ n2 n3 (notMem_of_rat L (-2⁻¹) 0 (by push_cast; ring) (by first | decide | norm_num | simp))
      (notMem_of_rat L 2⁻¹ 1 (by push_cast; ring) (by first | decide | norm_num | simp)))

theorem zetaAdd_of (h : SigmaAdd) (hl : SigmaLogDeriv) (hz : SigmaZero) : ZetaAdd := by
  intro L a b ha hb hab hamb
  have hσ : ∀ x, x ∉ L.lattice → wSigma L x ≠ 0 := fun x hx h0 => hx ((hz L x).mp h0)
  have hadd := h L a b ha hb
  have hK : wSigma L a ^ 2 * wSigma L b ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (hσ a ha)) (pow_ne_zero _ (hσ b hb))
  have hD : L.weierstrassP a - L.weierstrassP b ≠ 0 := by
    intro h0
    rw [h0, mul_zero, neg_zero] at hadd
    exact mul_ne_zero (hσ _ hab) (hσ _ hamb) hadd

  have hF1 := (HasDerivAt.comp a (hl L (a + b) hab) ((hasDerivAt_id' a).add_const b)).mul
    (HasDerivAt.comp a (hl L (a - b) hamb) ((hasDerivAt_id' a).sub_const b))
  have hG1 := ((((hl L a ha).mul (hl L a ha)).mul_const (wSigma L b ^ 2)).mul
    ((hasDerivAt_P L ha).sub_const (L.weierstrassP b))).neg
  have hG1' : HasDerivAt (fun x => wSigma L (x + b) * wSigma L (x - b)) _ a :=
    hG1.congr_of_eventuallyEq ((eventually_notMem L ha).mono fun x hx => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L x b hx hb]
      ring)
  have k1 := hF1.unique hG1'
  simp only [Function.comp_apply, Pi.mul_apply] at k1

  have hF2 := (HasDerivAt.comp b (hl L (a + b) hab) ((hasDerivAt_id' b).const_add a)).mul
    (HasDerivAt.comp b (hl L (a - b) hamb) ((hasDerivAt_id' b).const_sub a))
  have hG2 := ((((hl L b hb).mul (hl L b hb)).const_mul (wSigma L a ^ 2)).mul
    ((hasDerivAt_P L hb).const_sub (L.weierstrassP a))).neg
  have hG2' : HasDerivAt (fun y => wSigma L (a + y) * wSigma L (a - y)) _ b :=
    hG2.congr_of_eventuallyEq ((eventually_notMem L hb).mono fun y hy => by
      simp only [Pi.neg_apply, Pi.mul_apply]
      rw [h L a y ha hy]
      ring)
  have k2 := hF2.unique hG2'
  simp only [Function.comp_apply, Pi.mul_apply] at k2
  have e1 : (wSigma L a ^ 2 * wSigma L b ^ 2) *
      ((L.weierstrassP a - L.weierstrassP b) * (wZeta L (a + b) + wZeta L (a - b))
        - 2 * wZeta L a * (L.weierstrassP a - L.weierstrassP b) - L.derivWeierstrassP a) = 0 := by
    linear_combination (wZeta L (a + b) + wZeta L (a - b)) * hadd - k1
  have e2 : (wSigma L a ^ 2 * wSigma L b ^ 2) *
      ((L.weierstrassP a - L.weierstrassP b) * (wZeta L (a + b) - wZeta L (a - b))
        - 2 * wZeta L b * (L.weierstrassP a - L.weierstrassP b) + L.derivWeierstrassP b) = 0 := by
    linear_combination (wZeta L (a + b) - wZeta L (a - b)) * hadd - k2
  have f1 := (mul_eq_zero.mp e1).resolve_left hK
  have f2 := (mul_eq_zero.mp e2).resolve_left hK
  have hq : wZeta L (a + b) - (wZeta L a + wZeta L b)
      = (L.derivWeierstrassP a - L.derivWeierstrassP b) /
        (2 * (L.weierstrassP a - L.weierstrassP b)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hD)]
    linear_combination f1 + f2
  linear_combination hq

end Formalism.L2.Th1.F
end
end
