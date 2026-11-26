module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOperators
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FixedPointImaginarySpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousRl
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatMulVec

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

theorem Data.fj_flow_real (X : Data E r) (la : Wt X.Ψ r) (ξ : Fin r → E) (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ)
    (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (hbdd : ∃ C, ∀ x ∈ X.dom, X.pnorm la P x ≤ C)
    (x : Frame X.Ψ r) (hx : x ∈ X.dom) (s : X.Ψ → ℝ) :
    X.fj la ξ ν P (X.flow ξ (fun τ => (s τ : ℂ)) x) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * X.fj la ξ ν P x := by
  classical
  obtain ⟨hΛ, hξ0, -⟩ : ξ ∈ X.Λ ∧ herm X.Gm ξ ξ = 0 ∧ ξ ≠ 0 := hξ
  unfold Data.fj
  by_cases hc : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k
  swap
  · rw [if_neg hc, if_neg hc, mul_zero]
  rw [if_pos hc, if_pos hc]
  by_cases hD : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤
  swap
  · rw [dite_eq_right hD, dite_eq_right hD, mul_zero]
  rw [dite_eq_left hD, dite_eq_left hD]
  have hFD : IsAddFundamentalDomain (X.periods la) hD.choose volume := hD.choose_spec.2.1

  set F : (X.Ψ → ℝ) → ℂ := fun t => P (X.flow ξ (fun τ => (t τ : ℂ)) x) *
    cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) with hF
  have hsum : ∀ a b : X.Ψ → ℝ, ∑ τ, (ν τ : ℂ) * (((a + b) τ : ℝ) : ℂ) =
      ∑ τ, (ν τ : ℂ) * a τ + ∑ τ, (ν τ : ℂ) * b τ := by
    intro a b
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Pi.add_apply, Complex.ofReal_add]
    ring

  have hFper : ∀ p ∈ X.periods la, ∀ t, F (p + t) = F t := by
    intro p hp t
    simp only [hF]
    have hfl : (fun τ => (((p + t) τ : ℝ) : ℂ)) = cR X p + (fun τ => (t τ : ℂ)) := by
      funext τ
      simp only [cR, Pi.add_apply, Complex.ofReal_add]
    have hdom : X.flow ξ (fun τ => (t τ : ℂ)) x ∈ X.dom :=
      flow_real_mem_dom (X := X) hξ0 t x hx
    rw [hfl, ← flow_flow (X := X) hξ0, sec_periodic (X := X) la P hP hΛ hξ0 hp _ hdom]
    obtain ⟨k, hk⟩ := hc p hp
    have h1 : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * p τ) = 1 := by
      have hk' : ∑ τ, (ν τ : ℂ) * p τ = (k : ℂ) / 2 := by
        have h2 := congrArg (fun y : ℝ => (y : ℂ)) hk
        push_cast at h2
        linear_combination h2 / 2
      rw [hk', show -(4 * Real.pi * I) * ((k : ℂ) / 2) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    rw [hsum p t, mul_add, Complex.exp_add, h1, one_mul]

  have hstep : ∀ t : X.Ψ → ℝ, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (s τ : ℂ)) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * F (s + t) := by
    intro t
    have hfl : (fun τ => (t τ : ℂ)) + (fun τ => (s τ : ℂ)) = fun τ => (((s + t) τ : ℝ) : ℂ) := by
      funext τ
      simp only [Pi.add_apply, Complex.ofReal_add]
      ring
    rw [flow_flow (X := X) hξ0, hfl]
    simp only [hF]
    rw [hsum s t]
    have he : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) *
          cexp (-(4 * Real.pi * I) * (∑ τ, (ν τ : ℂ) * s τ + ∑ τ, (ν τ : ℂ) * t τ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hint : ∫ t in hD.choose, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (s τ : ℂ)) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * t τ) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * ∫ t in hD.choose, F t := by
    simp_rw [hstep]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    exact fd_translate (X.periods la) hD.choose hFD F hFper s
  rw [hint]
  ring

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicThreshold
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace IsotropicThreshold

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem c_pos (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  positivity

theorem iso_threshold (X : Data E r) : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ x ∈ X.dom, ∀ v ∈ X.Λ,
    ∑ τ, X.c τ * X.maj x τ (Data.emb τ.1 v) < δ0 → herm X.Gm v v = 0 := by
  classical
  have hcpos := c_pos X
  obtain ⟨D, hD, hDb⟩ : ∃ D : ℝ, 0 < D ∧ ∀ σ : E →+* ℂ, ‖σ (X.den : E)‖ ≤ D := by
    refine ⟨∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ + 1, by positivity, fun σ => ?_⟩
    have := Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
    linarith
  set S := ∑ τ : X.Ψ, (X.c τ)⁻¹ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => (inv_pos.2 (hcpos τ)).le
  have hcl : ∀ τ, (S + 1)⁻¹ ≤ X.c τ := fun τ => by
    have h1 : (X.c τ)⁻¹ ≤ S := Finset.single_le_sum (f := fun τ => (X.c τ)⁻¹)
      (fun τ _ => (inv_pos.2 (hcpos τ)).le) (Finset.mem_univ τ)
    rw [inv_le_comm₀ (by linarith) (hcpos τ)]
    linarith
  refine ⟨(S + 1)⁻¹ / D, div_pos (inv_pos.2 (by linarith)) hD, ?_⟩
  intro x hx v hv hsum
  have hmaj0 : ∀ τ : X.Ψ, 0 ≤ X.maj x τ (Data.emb τ.1 v) := fun τ =>
    (norm_nonneg _).trans (UnipotentCoefficientShift.norm_hermC_le_maj hx τ _)
  have hterm : ∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 v) < (S + 1)⁻¹ / D := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (Data.emb τ.1 v))
      (fun τ _ => mul_nonneg (hcpos τ).le (hmaj0 τ)) (Finset.mem_univ τ)) hsum
  have hmaj : ∀ τ : X.Ψ, D * X.maj x τ (Data.emb τ.1 v) < 1 := fun τ => by
    have h3 := hcpos τ
    have h5 : X.c τ * X.maj x τ (Data.emb τ.1 v) < X.c τ / D :=
      lt_of_lt_of_le (hterm τ) (div_le_div_of_nonneg_right (hcl τ) hD.le)
    rw [lt_div_iff₀ hD] at h5
    nlinarith
  have hemb : ∀ τ : E →+* ℂ,
      hermC τ X.Gm (Data.emb τ v) (Data.emb τ v) = τ (herm X.Gm v v) := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]
  have ha : IsIntegral ℤ ((X.den : E) * herm X.Gm v v) := X.Λ_int v hv v hv
  have hzero := UnipotentCoefficientShift.eq_zero_of_conj_lt_one ha (fun σ => by
    obtain ⟨τ, h1, h2⟩ : ∃ τ : X.Ψ, ‖σ (herm X.Gm v v)‖ = ‖τ.1 (herm X.Gm v v)‖ ∧
        ‖σ (X.den : E)‖ = ‖τ.1 (X.den : E)‖ := by
      by_cases hσ : σ ∈ X.Ψ
      · exact ⟨⟨σ, hσ⟩, rfl, rfl⟩
      · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ X.Ψ := by
          by_contra h
          exact hσ ((X.cmType σ).2 h)
        refine ⟨⟨_, hc⟩, ?_, ?_⟩ <;> simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rw [map_mul, norm_mul, h1]
    have hb := UnipotentCoefficientShift.norm_hermC_le_maj hx τ (Data.emb τ.1 v)
    rw [hemb] at hb
    calc ‖σ (X.den : E)‖ * ‖τ.1 (herm X.Gm v v)‖ ≤ D * X.maj x τ (Data.emb τ.1 v) :=
          mul_le_mul (hDb σ) hb (norm_nonneg _) hD.le
      _ < 1 := hmaj τ)
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h (NumberField.RingOfIntegers.coe_ne_zero_iff.2 X.den_ne)
  · exact h

end IsotropicThreshold

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCubeVolume
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices MeasureTheory Set Filter
open scoped ComplexConjugate

noncomputable section

section Gen

variable {ι : Type} [Fintype ι] {N : ℕ} (ω : Fin N → ι → Fin 2 → Fin 2 → ℂ)

def Bv (t : Fin N → ℝ) : ι → Fin 2 → Fin 2 → ℂ := ∑ j, (t j : ℂ) • ω j

lemma Bv_add (t s : Fin N → ℝ) : Bv ω (t + s) = Bv ω t + Bv ω s := by
  simp only [Bv, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

lemma Bv_zero : Bv ω 0 = 0 := by
  simp [Bv]

lemma Bv_herm (hωh : ∀ j, IsHermFam (ω j)) (t : Fin N → ℝ) : IsHermFam (Bv ω t) := by
  intro τ i k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hωh j τ i k]

lemma Bv_cont : Continuous (Bv ω) := continuous_finsetSum _ (fun j _ => (Complex.continuous_ofReal.comp (continuous_apply j)).smul continuous_const)

lemma pair_Bv (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) :
    pr χ (Bv ω t) = ∑ j, t j * pr χ (ω j) := by
  have hadd : ∀ b b' : ι → Fin 2 → Fin 2 → ℂ, pr χ (b + b') = pr χ b + pr χ b' := by
    intro b b'
    simp only [pr, Pi.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]
  have hsm : ∀ (c : ℝ) (b : ι → Fin 2 → Fin 2 → ℂ), pr χ ((c : ℂ) • b) = c * pr χ b := by
    intro c b
    simp only [pr, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun k _ => by ring)))
  let P : (ι → Fin 2 → Fin 2 → ℂ) →+ ℝ := AddMonoidHom.mk' (pr χ) hadd
  have h1 : pr χ (Bv ω t) = P (Bv ω t) := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, Bv, map_sum]
  exact Finset.sum_congr rfl (fun j _ => hsm _ _)

def ech (χ : ι → Fin 2 → Fin 2 → ℂ) (t : Fin N → ℝ) : ℂ :=
  cexp (-(4 * Real.pi * I) * (pr χ (Bv ω t) : ℂ))

lemma ech_cont (χ : ι → Fin 2 → Fin 2 → ℂ) : Continuous (ech ω χ) := by
  have h : ech ω χ = fun t => cexp (-(4 * Real.pi * I) * ((∑ j, t j * pr χ (ω j) : ℝ) : ℂ)) := by
    funext t
    simp only [ech, pair_Bv]
  rw [h]
  fun_prop

lemma ech_add (χ : ι → Fin 2 → Fin 2 → ℂ) (t s : Fin N → ℝ) :
    ech ω χ (t + s) = ech ω χ t * ech ω χ s := by
  simp only [ech, pair_Bv, Pi.add_apply, add_mul, Finset.sum_add_distrib, Complex.ofReal_add, mul_add,
    Complex.exp_add]

lemma ech_int (χ : ι → Fin 2 → Fin 2 → ℂ) {k : Fin N → ℤ} (hk : ∀ j, 2 * pr χ (ω j) = k j)
    (n : Fin N → ℤ) : ech ω χ (fun i => (n i : ℝ)) = 1 := by
  have hk' : ∀ j, pr χ (ω j) = (k j : ℝ) / 2 := fun j => by linarith [hk j]
  rw [ech, pair_Bv, Complex.exp_eq_one_iff]
  refine ⟨-∑ j, n j * k j, ?_⟩
  simp only [hk']
  push_cast
  rw [Finset.mul_sum, neg_mul (∑ x, ((n x : ℂ) * (k x : ℂ))), Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

end Gen

def cube (N : ℕ) : Set (Fin N → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

lemma cube_compact (N : ℕ) : IsCompact (cube N) := isCompact_univ_pi (fun _ => isCompact_Icc)

lemma cube_meas (N : ℕ) : MeasurableSet (cube N) := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

lemma ubox_ae (N : ℕ) : (I2.DimB.ubox N) =ᵐ[volume] cube N := by
  have h1 : I2.DimB.ubox N = Set.pi Set.univ (fun i => Ioc ((0 : Fin N → ℝ) i) ((1 : Fin N → ℝ) i)) := by
    ext x
    simp [I2.DimB.ubox]
  have h2 : cube N = Set.Icc (0 : Fin N → ℝ) 1 := by
    rw [cube, ← Set.pi_univ_Icc]
    rfl
  rw [h1, h2]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

section Mean

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E) (g : ℕ) (ω : Fin (4 * Fintype.card X.Ψ) → X.Ψ → Fin 2 → Fin 2 → ℂ)
  (G : Frame X.Ψ r → ℂ)

def Ich (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∫ t in cube (4 * Fintype.card X.Ψ), G (X.Zb u (Bv ω t) x) * ech ω χ t

variable {X u g ω G}
variable (hω : X.IsLZBasis g ω)
  (hadd : ∀ b b' x, X.Zb u b (X.Zb u b' x) = X.Zb u (b + b') x)
  (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)

include hω in
lemma herm_ω (j : Fin (4 * Fintype.card X.Ψ)) : IsHermFam (ω j) := ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.herm_of_LZ X g (hω.1 j)

include hω in
lemma Bv_LZ (n : Fin (4 * Fintype.card X.Ψ) → ℤ) : Bv ω (fun i => (n i : ℝ)) ∈ X.LZ g := by
  exact ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice.LZ_sum X g hω.1 n

include hω hdomH in
lemma Zb_dom (t : Fin (4 * Fintype.card X.Ψ) → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.Zb u (Bv ω t) x ∈ X.dom := hdomH _ (Bv_herm ω (fun j => herm_ω hω j) t) x hx

include hω hdomH in
lemma psi_cont (hG : DifferentiableOn ℂ G X.dom) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous fun t => G (X.Zb u (Bv ω t) x) := by
  have hB : Continuous (Bv ω) := Bv_cont ω
  have hc : Continuous fun t => X.Zb u (Bv ω t) x := by
    unfold Data.Zb Data.zmat
    fun_prop
  exact hG.continuousOn.comp_continuous hc (fun t => Zb_dom hω hdomH t hx)

include hω hadd hdomH in
lemma psi_per (hper : ∀ b ∈ X.LZ g, ∀ x ∈ X.dom, G (X.Zb u b x) = G x) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (n : Fin (4 * Fintype.card X.Ψ) → ℤ) (t : Fin (4 * Fintype.card X.Ψ) → ℝ) :
    G (X.Zb u (Bv ω (t + fun i => (n i : ℝ))) x) = G (X.Zb u (Bv ω t) x) := by
  have hx' := Zb_dom hω hdomH t hx
  rw [Bv_add, add_comm, ← hadd]
  exact hper _ (Bv_LZ hω n) _ hx'

include hω hdomH in
lemma Ich_diff (hG : DifferentiableOn ℂ G X.dom) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) :
    DifferentiableOn ℂ (Ich X u ω G χ) X.dom := by
  have := FourierCoefficientDomain.diffOn_param (cube_compact _) (cube_meas _)
    (fun t => FourierCoefficientDomain.ZbL X u (Bv ω t)) (FourierCoefficientDomain.cont_ZbL X u (Bv_cont ω))
    (FourierCoefficientDomain.isOpen_dom X) (fun t _ x hx => Zb_dom hω hdomH t hx) G hG (ech ω χ) (ech_cont ω χ)
  exact this

lemma Ich_rmul (la : Wt X.Ψ r) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = bchar la b * G x)
    (hω : X.IsLZBasis g ω) (hdomH : ∀ b, IsHermFam b → ∀ x ∈ X.dom, X.Zb u b x ∈ X.dom)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : Ich X u ω G χ (rmul x b) = bchar la b * Ich X u ω G χ x := by
  have hcomm : ∀ t, X.Zb u (Bv ω t) (rmul x b) = rmul (X.Zb u (Bv ω t) x) b := by
    intro t
    funext τ
    show X.zmat u (Bv ω t) τ * mat (rmul x b) τ = mat (X.Zb u (Bv ω t) x) τ * mat b τ
    change X.zmat u (Bv ω t) τ * (mat x τ * mat b τ) = _
    rw [mat_Zb, Matrix.mul_assoc]
  unfold Ich
  simp_rw [hcomm]
  have h2 : ∀ t, G (rmul (X.Zb u (Bv ω t) x) b) * ech ω χ t = bchar la b * (G (X.Zb u (Bv ω t) x) * ech ω χ t) := by
    intro t
    rw [hB _ (Zb_dom hω hdomH t hx) b hb, mul_assoc]
  simp_rw [h2]
  exact integral_const_mul _ _

end Mean

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCubeVolume
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscrMulHermitianIntegral
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Module Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_smul_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem smul_mem_of_int {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ L) : c • v ∈ L := by
  first
  | exact L.smul_mem (⟨c, hc⟩ : 𝓞 E) hv
  | simpa using L.smul_mem (⟨c, hc⟩ : 𝓞 E) hv

namespace DataX

variable {r : ℕ} (X : DataX E r)

theorem discr_mul_hermitian_integral {v w : Fin r → E} (hv : v ∈ X.Λ) (hw : w ∈ X.Λ) :
    IsIntegral ℤ (((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w)) := by
  have h := d4l2_dual_int' (-(X.ξ0 * herm X.Gm v w)) (fun γ => by
    obtain ⟨k, hk⟩ := X.EF_int ((γ : E) • v) (smul_mem_of_int X.Λ (RingOfIntegers.isIntegral_coe γ) hv) w hw
    refine ⟨k, ?_⟩
    rw [← hk]
    unfold EFf
    rw [herm_smul_left']
    congr 1; ring)
  have : ((NumberField.discr E).natAbs : E) * (X.ξ0 * herm X.Gm v w) =
      -(((NumberField.discr E).natAbs : E) * -(X.ξ0 * herm X.Gm v w)) := by ring
  rw [this]; exact h.neg

theorem Mmat_cong (u : Fin 2 → Fin r → E) (hmem : ∀ i, u i ∈ X.Λ) (β : Matrix (Fin 2) (Fin 2) E)
    (hβ : ∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((X.g * dEnat E : ℕ) : E) / 2 * γ) :
    ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u β *ᵥ v - v = (X.g : E) • y := by
  intro v hv
  choose γ hγi hγ using hβ
  set d := (NumberField.discr E).natAbs with hd
  have hint : ∀ k, IsIntegral ℤ ((d : E) * (X.ξ0 * herm X.Gm v (u k))) :=
    fun k => X.discr_mul_hermitian_integral hv (hmem k)
  have hc : ∀ i k, IsIntegral ℤ (X.κ0 / 2 * d * γ i k * herm X.Gm v (u k)) := by
    intro i k
    rcases X.κ0_xi with h | h
    · have e1 : X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) = γ i k * ((d : E) * (X.ξ0 * herm X.Gm v (u k))) := by
        rw [h]; ring
      rw [e1]; exact (hγi i k).mul (hint k)
    · have e1 : X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) = -(γ i k * ((d : E) * (X.ξ0 * herm X.Gm v (u k)))) := by
        rw [h]; ring
      rw [e1]; exact ((hγi i k).mul (hint k)).neg
  set c : Fin 2 → E := fun i => ∑ k, X.κ0 / 2 * d * γ i k * herm X.Gm v (u k) with hcdef
  have hci : ∀ i, IsIntegral ℤ (c i) := fun i => by
    simp only [hcdef, Fin.sum_univ_two]; exact (hc i 0).add (hc i 1)
  refine ⟨∑ i, c i • u i, Submodule.sum_mem _ fun i _ => smul_mem_of_int X.Λ (hci i) (hmem i), ?_⟩
  rw [X.Mmat_mulVec, add_sub_cancel_left, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  congr 1
  simp only [hcdef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hγ i k, hd]
  unfold dEnat
  push_cast
  ring

theorem g_smul_mem {y : Fin r → E} (hy : y ∈ X.Λ) : (X.g : E) • y ∈ X.Λ := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hy _

theorem exists_gamma (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (hmem : ∀ i, u i ∈ X.Λ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : b ∈ X.LZ X.g) :
    ∃ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) ∧
      ∀ τ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.zmat u b τ := by
  obtain ⟨β, hβh, hβi, rfl⟩ := hb
  have hiso := hu.1
  have hγc : ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u β *ᵥ v - v = (X.g : E) • y :=
    X.Mmat_cong u hmem β hβi
  have hγc' : ∀ v ∈ X.Λ, ∃ y ∈ X.Λ, X.Mmat u (-β) *ᵥ v - v = (X.g : E) • y :=
    X.Mmat_cong u hmem (-β) (fun i k => by
      obtain ⟨γ', h1, h2⟩ := hβi i k
      exact ⟨-γ', h1.neg, by simp [h2]⟩)
  have hstab : IsUStab X.Gm X.Λ (X.gam u hiso β) := by
    refine ⟨fun x y => X.herm_Mmat u hiso β hβh x y, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨y, hy, hyeq⟩ := hγc x hx
      have e1 : X.Mmat u β *ᵥ x = x + (X.g : E) • y := by rw [← hyeq]; abel
      show X.Mmat u β *ᵥ x ∈ X.Λ
      rw [e1]; exact X.Λ.add_mem hx (X.g_smul_mem hy)
    · change X.Mmat u β *ᵥ x ∈ X.Λ at hx
      have hinv : X.Mmat u (-β) *ᵥ (X.Mmat u β *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, X.Mmat_mul u hiso, neg_add_cancel, Data.Mmat_zero, Matrix.one_mulVec]
      obtain ⟨y, hy, hyeq⟩ := hγc' _ hx
      have e1 : X.Mmat u (-β) *ᵥ (X.Mmat u β *ᵥ x) = X.Mmat u β *ᵥ x + (X.g : E) • y := by
        rw [← hyeq]; abel
      rw [← hinv, e1]; exact X.Λ.add_mem hx (X.g_smul_mem hy)
  exact ⟨X.gam u hiso β, X.cong _ hstab hγc, hγc, fun τ => X.Mmat_map u β τ⟩

theorem LZ_periodic (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (hmem : ∀ i, u i ∈ X.Λ)
    (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P)
    (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
        Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (hb : b ∈ X.LZ X.g) (x : Frame X.Ψ r) (hx : x ∈ X.dom) :
    P (X.Zb u b x) = P x := by
  obtain ⟨γ, hγΓ, hγc, hmap⟩ := X.exists_gamma u hu hmem b hb
  have e1 : X.Zb u b x = lact γ x := funext fun τ => by
    show X.zmat u b τ * mat x τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
    rw [hmap]
  rw [e1, hP.2.2 γ hγΓ x hx, hχ γ hγΓ hγc, one_mul]

noncomputable def c0E : E := ((X.g * dEnat E : ℕ) : E) / 2

theorem cc_c0E : cc X.c0E = X.c0E := by
  unfold c0E cc
  first
  | rw [map_div₀, map_natCast, map_ofNat]
  | simp

theorem tau_c0E (τ : E →+* ℂ) : τ X.c0E = ((((X.g * dEnat E : ℕ) : ℝ) / 2 : ℝ) : ℂ) := by
  unfold c0E
  rw [map_div₀, map_natCast, map_ofNat]
  push_cast
  try ring

theorem mem_LZ_of (w : Fin 2 → Fin 2 → E) (hwi : ∀ i k, IsIntegral ℤ (w i k))
    (hwh : ∀ i k, cc (w i k) = w k i) :
    X.embH (Matrix.of fun i k => X.c0E * w i k) ∈ X.LZ X.g := by
  refine ⟨Matrix.of fun i k => X.c0E * w i k, fun i k => ?_, fun i k => ⟨w i k, hwi i k, rfl⟩, rfl⟩
  show cc (X.c0E * w i k) = X.c0E * w k i
  have hm : cc (X.c0E * w i k) = cc X.c0E * cc (w i k) := map_mul (IsCMField.complexConj E) _ _
  rw [hm, X.cc_c0E, hwh i k]

theorem pairR_of (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (w : Fin 2 → Fin 2 → E) :
    X.pairR χ (X.embH (Matrix.of fun i k => X.c0E * w i k)) =
      (((X.g * dEnat E : ℕ) : ℝ) / 2) *
        (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w i k)).re := by
  unfold Data.pairR Data.embH
  simp only [Matrix.of_apply, map_mul, tau_c0E]
  rw [← Complex.re_ofReal_mul]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem freq_entry (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hf : X.IsFreqZ X.g χ) (z : X.Ψ → ℂ)
    (w : 𝓞 E → Fin 2 → Fin 2 → E) (hwi : ∀ γ i k, IsIntegral ℤ (w γ i k))
    (hwh : ∀ γ i k, cc (w γ i k) = w γ k i)
    (hterm : ∀ γ : 𝓞 E, (∑ τ : X.Ψ, ∑ i, ∑ k, χ τ i k * τ.1 (w γ i k)).re =
      2 * (∑ τ : X.Ψ, z τ * τ.1 (γ : E)).re) :
    ∃ ω : E, (∀ τ : X.Ψ, z τ = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
  refine X.exists_emb_int z X.g X.g_pos fun γ => ?_
  obtain ⟨k, hk⟩ := hf _ (X.mem_LZ_of (w γ) (hwi γ) (hwh γ))
  rw [X.pairR_of, hterm γ] at hk
  refine ⟨k, ?_⟩
  rw [← hk]
  unfold dEnat
  push_cast
  ring

theorem freq_to_beta (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hχ : IsHermFam χ) (hf : X.IsFreqZ X.g χ) :
    ∃ β : Matrix (Fin 2) (Fin 2) E, (∀ i k, cc (β i k) = β k i) ∧ χ = X.embH β ∧
      ∀ i k, IsIntegral ℤ (((X.g * dEnat E ^ 2 : ℕ) : E) * β i k) := by
  have hreal : ∀ τ i, (χ τ i i).im = 0 := fun τ i => by
    have := congrArg Complex.im (hχ τ i i)
    simp only [Complex.conj_im] at this
    linarith
  have hcc_int : ∀ γ : 𝓞 E, IsIntegral ℤ (cc (γ : E)) := fun γ => isIntegral_cc γ.isIntegral_coe

  obtain ⟨ω01, hω01, hi01⟩ := X.freq_entry χ hf (fun τ => χ τ 0 1)
    (fun γ => ![![0, (γ : E)], ![cc (γ : E), 0]])
    (fun γ i k => by fin_cases i <;> fin_cases k <;> simp [isIntegral_zero, γ.isIntegral_coe, hcc_int])
    (fun γ i k => by fin_cases i <;> fin_cases k <;> simp [cc_cc, cc_zero])
    (fun γ => by
      rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_zero, mul_zero, zero_add, add_zero, emb_cc]
      rw [hχ τ 0 1]
      simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring)

  have hdiag : ∀ j : Fin 2, ∃ ω : E, (∀ τ : X.Ψ, χ τ j j = τ.1 ω) ∧
      IsIntegral ℤ (((X.g * (NumberField.discr E).natAbs ^ 2 : ℕ) : E) * ω) := by
    intro j
    refine X.freq_entry χ hf (fun τ => χ τ j j)
      (fun γ i k => if i = j ∧ k = j then (γ : E) + cc (γ : E) else 0)
      (fun γ i k => by split_ifs; exact γ.isIntegral_coe.add (hcc_int γ); exact isIntegral_zero)
      (fun γ i k => by
        by_cases h : i = j ∧ k = j
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩, show cc ((γ : E) + cc (γ : E)) = cc (γ : E) + cc (cc (γ : E)) from
            map_add (IsCMField.complexConj E) _ _, cc_cc, add_comm]
        · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), cc_zero])
      (fun γ => ?_)
    rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hs : ∑ i, ∑ k, χ τ i k * τ.1 (if i = j ∧ k = j then (γ : E) + cc (γ : E) else 0) =
        χ τ j j * τ.1 ((γ : E) + cc (γ : E)) := by
      rw [Finset.sum_eq_single j, Finset.sum_eq_single j]
      · simp
      · intro k _ hk; simp [hk]
      · simp
      · intro i _ hi; apply Finset.sum_eq_zero; intro k _; simp [hi]
      · simp
    rw [hs, map_add (f := _), emb_cc]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, hreal]
    ring
  obtain ⟨ω00, hω00, hi00⟩ := hdiag 0
  obtain ⟨ω11, hω11, hi11⟩ := hdiag 1
  obtain ⟨τ0⟩ := X.nonempty_Psi
  have hcc_diag : ∀ (ω : E) (j : Fin 2), (∀ τ : X.Ψ, χ τ j j = τ.1 ω) → cc ω = ω := by
    intro ω j hω
    apply τ0.1.injective
    rw [emb_cc, ← hω τ0, ← hχ τ0 j j]
  refine ⟨!![ω00, ω01; cc ω01, ω11], fun i k => ?_, ?_, fun i k => ?_⟩
  · fin_cases i <;> fin_cases k <;> simp [cc_cc, hcc_diag ω00 0 hω00, hcc_diag ω11 1 hω11]
  · funext τ i k
    fin_cases i <;> fin_cases k
    · simp [Data.embH, hω00 τ]
    · simp [Data.embH, hω01 τ]
    · simp only [Data.embH]
      simp [hχ τ 0 1, hω01 τ, emb_cc]
    · simp [Data.embH, hω11 τ]
  · unfold dEnat
    fin_cases i <;> fin_cases k
    · simpa using hi00
    · simpa using hi01
    · have := isIntegral_cc hi01
      simpa [cc_mul, cc] using this
    · simpa using hi11

end DataX

end ReciprocityTheory.ChartRestriction.G.FD
end
