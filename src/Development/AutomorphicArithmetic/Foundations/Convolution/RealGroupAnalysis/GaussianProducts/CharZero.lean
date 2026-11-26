module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CharZero
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealDiff
open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.one_side {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) :
    ∫ x, G x ∂Measure.map X (ν.withDensity fun ω ↦ ENNReal.ofReal (f ω)) =
      ∫ ω, G (X ω) * ((max (f ω) 0 : ℝ) : ℂ) ∂ν := by
  rw [integral_map hX.aemeasurable hG.aestronglyMeasurable]
  have h : AEMeasurable (fun ω ↦ (f ω).toNNReal) ν := hf.aemeasurable.real_toNNReal
  have h2 := integral_withDensity_eq_integral_smul₀ h (fun ω ↦ G (X ω))
  refine Eq.trans h2 ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul, mul_comm]

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.int_mul {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hb : ∀ x, ‖G x‖ ≤ (1 : ℝ)) :
    Integrable (fun ω ↦ G (X ω) * ((max (f ω) 0 : ℝ) : ℂ)) ν := by
  have h1 : Integrable (fun ω ↦ ((max (f ω) 0 : ℝ) : ℂ)) ν := hf.pos_part.ofReal
  exact h1.bdd_mul (c := 1) (hG.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ hb _)

theorem UpperTheory.Reformulated.B.Qh3.real_diff :
    ∀ {Ω ι : Type} [inst : MeasurableSpace Ω] [Fintype ι]
    (ν : MeasureTheory.Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ),
    Measurable X →
      MeasureTheory.Integrable f ν →
        ∀ (G : (ι → ℝ) → ℂ),
          Measurable G →
            (∀ (x : ι → ℝ), ‖G x‖ ≤ (1 : ℝ)) →
              ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (f ω)) -
                  ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (-f ω)) =
                ∫ (ω : Ω), G (X ω) * (↑(f ω) : ℂ) ∂ν := by
  intro Ω ι _ _ ν X f hX hf G hG hb
  have hn : MeasureTheory.Integrable (fun ω ↦ -f ω) ν := hf.neg
  rw [UpperTheory.Reformulated.B.Qh3.one_side ν X f hX hf G hG,
    UpperTheory.Reformulated.B.Qh3.one_side ν X (fun ω ↦ -f ω) hX hn G hG,
    ← MeasureTheory.integral_sub (UpperTheory.Reformulated.B.Qh3.int_mul ν X f hX hf G hG hb)
      (UpperTheory.Reformulated.B.Qh3.int_mul ν X (fun ω ↦ -f ω) hX hn G hG hb)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  have h : max (f ω) 0 - max (-f ω) 0 = f ω := max_zero_sub_max_neg_zero_eq_self (f ω)
  simp only
  rw [← mul_sub, ← Complex.ofReal_sub, h]
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private lemma bdd_int {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (u g : Ω → ℂ)
    (hu : Measurable u) (hb : ∀ ω, ‖u ω‖ ≤ 1) (hg : Integrable g ν) :
    Integrable (fun ω => u ω * g ω) ν := by
  refine Integrable.mono' hg.norm (hu.aestronglyMeasurable.mul hg.1) (ae_of_all _ fun ω => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb ω)

private lemma real_diff {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hGb : ∀ x, ‖G x‖ ≤ 1) :
    ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X)
      - ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X)
      = ∫ ω, G (X ω) * (f ω : ℂ) ∂ν :=
  _root_.UpperTheory.Reformulated.B.Qh3.real_diff ν X f hX hf G hG hGb

private lemma real_case {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (h : ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (f ω : ℂ) ∂ν = 0)
    (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
    ∫ ω, S.indicator 1 (X ω) * (f ω : ℂ) ∂ν = 0 := by
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (-f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hEq : (ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X
      = (ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply]
    have key := real_diff ν X f hX hf (fun x => Complex.exp ((L x : ℂ) * Complex.I))
      (by fun_prop) (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
    have h0 := h (fun i => L (fun j => if i = j then 1 else 0))
    have hL : ∀ x : ι → ℝ, L x = ∑ i, L (fun j => if i = j then 1 else 0) * x i := by
      intro x
      have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
      simpa [mul_comm] using this
    simp only [← hL] at h0
    rw [h0] at key
    exact sub_eq_zero.mp key
  have key := real_diff ν X f hX hf (S.indicator 1)
    (measurable_one.indicator hS) (fun x => by
      by_cases hx : x ∈ S <;> simp [hx])
  rw [hEq, sub_self] at key
  exact key.symm

theorem UpperTheory.ConvolutionTheory.R2.G.charZero :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X → Integrable ρ ν →
    (∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0) →
    ∀ S : Set (ι → ℝ), MeasurableSet S → ∫ ω, S.indicator 1 (X ω) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hρ h S hS
  have hconjI : Integrable (fun ω => (starRingEnd ℂ) (ρ ω)) ν := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hρ
  have hE : ∀ t : ι → ℝ, Measurable fun ω =>
      Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) := by
    intro t
    have : ∀ i, Measurable fun ω => X ω i := fun i => (measurable_pi_apply i).comp hX
    fun_prop
  have hEb : ∀ (t : ι → ℝ) (ω : Ω),
      ‖Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro t ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hc : ∀ t : ι → ℝ,
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω) ∂ν = 0 := by
    intro t
    have h1 := congrArg (starRingEnd ℂ) (h (-t))
    rw [← integral_conj, map_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    simp
  have hlin : ∀ (a b : ℂ) (t : ι → ℝ),
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) ∂ν = 0 := by
    intro a b t
    have e1 := bdd_int ν _ ρ (hE t) (hEb t) hρ
    have e2 := bdd_int ν _ _ (hE t) (hEb t) hconjI
    have : ∀ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω))
        = a * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
          + b * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω)) := by
      intro ω; ring
    simp only [this]
    rw [integral_add (e1.const_mul a) (e2.const_mul b), integral_const_mul, integral_const_mul,
      h t, hc t]
    simp
  have hre : Integrable (fun ω => (ρ ω).re) ν := hρ.re
  have him : Integrable (fun ω => (ρ ω).im) ν := hρ.im
  have r1 := real_case ν X (fun ω => (ρ ω).re) hX hre (fun t => by
    rw [← hlin (1 / 2) (1 / 2) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).re : ℂ) = 1 / 2 * ρ ω + 1 / 2 * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.re_eq_add_conj]; ring
    simp only [this]) S hS
  have r2 := real_case ν X (fun ω => (ρ ω).im) hX him (fun t => by
    rw [← hlin (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).im : ℂ) = 1 / (2 * Complex.I) * ρ ω
        + -(1 / (2 * Complex.I)) * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.im_eq_sub_conj]; ring
    simp only [this]) S hS
  have hind : Measurable fun ω => S.indicator (1 : (ι → ℝ) → ℂ) (X ω) :=
    (measurable_one.indicator hS).comp hX
  have hindb : ∀ ω, ‖S.indicator (1 : (ι → ℝ) → ℂ) (X ω)‖ ≤ 1 := by
    intro ω
    by_cases hx : X ω ∈ S <;> simp [hx]
  have i1 := bdd_int ν _ (fun ω => ((ρ ω).re : ℂ)) hind hindb hre.ofReal
  have i2 := bdd_int ν _ (fun ω => ((ρ ω).im : ℂ)) hind hindb him.ofReal
  have hsplit : ∀ ω, S.indicator 1 (X ω) * ρ ω
      = S.indicator 1 (X ω) * ((ρ ω).re : ℂ)
        + Complex.I * (S.indicator 1 (X ω) * ((ρ ω).im : ℂ)) := by
    intro ω
    conv_lhs => rw [← Complex.re_add_im (ρ ω)]
    ring
  simp only [hsplit]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, r1, r2]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.EAddRight
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open GroundTheory.Automorphic.FourierWhittaker

variable {F : Type} [Field F] [NumberField F]

private noncomputable def E (κ : Fin 2 → F) (u : Fin 2 → A F) : ℂ := ψ (rt (κ 0) * u 0 + rt (κ 1) * u 1)

private theorem E_cont (κ : Fin 2 → F) : Continuous (E κ) :=
  continuous_ψ.comp (((continuous_const).mul (continuous_apply 0)).add ((continuous_const).mul (continuous_apply 1)))

private theorem E_norm (κ : Fin 2 → F) (u : Fin 2 → A F) : ‖E κ u‖ = 1 := norm_ψ _

private theorem E_add_left (κ κ' : Fin 2 → F) (u : Fin 2 → A F) : E (κ + κ') u = E κ u * E κ' u := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply, map_add (f := _)]
  ring

private theorem E_add_right (κ : Fin 2 → F) (u v : Fin 2 → A F) : E κ (u + v) = E κ u * E κ v := by
  simp only [E, ← UpperTheory.ConvolutionTheory.R2.ψ_add]
  congr 1
  simp only [Pi.add_apply]
  ring

private theorem E_zero (u : Fin 2 → A F) : E (0 : Fin 2 → F) u = 1 := by
  simp [E]

private theorem E_per (κ : Fin 2 → F) : ∀ ξ ∈ vecLattice F (Fin 2), ∀ x, E κ (ξ + x) = E κ x := by
  intro ξ hξ x
  obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
  rw [E_add_right]
  have : E κ (fun i => algebraMap F (A F) (η i)) = 1 := by
    simp only [E]
    rw [← map_mul, ← map_mul, ← map_add (f := _)]
    exact ψ_rt _
  rw [this, one_mul]

private theorem exists_ne (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∃ a, E κ a ≠ 1 := by
  obtain ⟨x, hx⟩ : ∃ x, adelicChar F x ≠ 1 := by
    by_contra h
    push_neg at h
    exact adelicChar_ne_one (K := F) (DFunLike.ext _ _ fun x => by simpa using h x)
  have hx' : ψ x ≠ 1 := fun h => hx (Circle.ext (by simpa [ψ] using h))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hκ
  have hr : rt (κ i) * rt (κ i)⁻¹ = (1 : A F) := by
    rw [← map_mul, mul_inv_cancel₀ hi, map_one]
  refine ⟨Pi.single i (rt (κ i)⁻¹ * x), ?_⟩
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, add_zero,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'
  · simp only [Fin.mk_one, Fin.isValue] at hr ⊢
    simp only [E, Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, zero_add,
      ← mul_assoc, hr, one_mul, Fin.isValue, one_ne_zero]
    exact hx'

private theorem E_int (κ : Fin 2 → F) (hκ : κ ≠ 0) : ∫ u in FS2 F, E κ u ∂(adeleMeasurePi F) = 0 := by
  obtain ⟨a, ha⟩ := exists_ne κ hκ
  change ∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2)) = 0
  have h := setIntegral_comp_add (K := F) (ι := Fin 2) a (h := E κ) (E_per κ)
  simp only [E_add_right] at h
  rw [integral_mul_const] at h
  have h1 : (∫ u in vecDomain F (Fin 2), E κ u ∂(vecMeasure F (Fin 2))) * (E κ a - 1) = 0 := by
    rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 ha)

private theorem vol : (adeleMeasurePi F).restrict (FS2 F) Set.univ = 1 := by
  rw [Measure.restrict_apply_univ]
  exact vecMeasure_vecDomain

private theorem fin_inst : IsFiniteMeasure ((adeleMeasurePi F).restrict (FS2 F)) :=
  ⟨by rw [vol]; exact ENNReal.one_lt_top⟩

private theorem int_const (a : ℝ) : ∫ _ in FS2 F, a ∂(adeleMeasurePi (ι := Fin 2) F) = a := by
  rw [integral_const, measureReal_def, vol]
  simp

private theorem E_int_zero : ∫ u in FS2 F, E (0 : Fin 2 → F) u ∂(adeleMeasurePi F) = 1 := by
  simp only [E_zero]
  rw [integral_const, measureReal_def, vol]
  simp

private theorem cont_int {g : (Fin 2 → A F) → ℂ} (hg : Continuous g) : IntegrableOn g (FS2 F) (adeleMeasurePi F) := by
  obtain ⟨C, hC, hs⟩ := exists_isCompact_superset_vecDomain (K := F) (ι := Fin 2)
  exact (hg.continuousOn.integrableOn_compact (μ := vecMeasure F (Fin 2)) hC).mono_set hs

private theorem core (κ₀ : Fin 2 → F) (L : (Fin 2 → F) → Fin 2 → F) (c₀ : ℂ) (c : (Fin 2 → F) → ℂ)
    (hc : Summable fun ξ => ‖c ξ‖) (Φ : (Fin 2 → A F) → ℂ) (hΦ : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ) :
    IntegrableOn (fun u => Φ u * E κ₀ u) (FS2 F) (adeleMeasurePi F) ∧
    HasSum (fun ξ => (∫ u in FS2 F, E (κ₀ + L ξ) u ∂(adeleMeasurePi F)) * c ξ)
      ((∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F)) := by
  haveI := countable_numberField F
  haveI := fin_inst (F := F)
  set g : (Fin 2 → F) → (Fin 2 → A F) → ℂ := fun ξ u => E (κ₀ + L ξ) u * c ξ with hgdef
  have hgc : ∀ ξ, Continuous (g ξ) := fun ξ => (E_cont _).mul continuous_const
  have hgn : ∀ ξ u, ‖g ξ u‖ = ‖c ξ‖ := fun ξ u => by simp [hgdef, norm_mul, E_norm]
  have hsum : ∀ u, Summable fun ξ => E (L ξ) u * c ξ := fun u =>
    Summable.of_norm (by simpa [norm_mul, E_norm] using hc)
  have e : ∀ u, Φ u * E κ₀ u = c₀ * E κ₀ u + ∑' ξ, g ξ u := by
    intro u
    rw [hΦ, add_mul, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun ξ => ?_
    simp only [hgdef, E_add_left]
    ring
  have hcont : Continuous fun u => ∑' ξ, g ξ u := continuous_tsum hgc hc fun ξ u => (hgn ξ u).le
  have hI := cont_int hcont
  have hT := cont_int (E_cont κ₀)
  have hT' : IntegrableOn (fun u => c₀ * E κ₀ u) (FS2 F) (adeleMeasurePi F) := hT.const_mul c₀
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact hT'.add hI
  · have hS := hasSum_integral_of_summable_integral_norm (μ := (adeleMeasurePi F).restrict (FS2 F))
      (F := g) (fun ξ => cont_int (hgc ξ)) (by
        simp only [hgn]
        simpa only [int_const] using hc)
    have h2 : (∫ u in FS2 F, Φ u * E κ₀ u ∂(adeleMeasurePi F)) - c₀ * ∫ u in FS2 F, E κ₀ u ∂(adeleMeasurePi F) =
        ∫ u in FS2 F, ∑' ξ, g ξ u ∂(adeleMeasurePi F) := by
      simp only [e]
      rw [integral_add hT' hI, integral_const_mul]
      ring
    rw [h2]
    simpa only [hgdef, integral_mul_const] using hS

end UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors

open UpperTheory.ConvolutionTheory.R2.G.OrthogonalVectors in
theorem UpperTheory.ConvolutionTheory.R2.G.orth :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (c₀ : ℂ) (c : (Fin 2 → F) → ℂ) (Φ : (Fin 2 → A F) → ℂ), Summable (fun ξ => ‖c ξ‖) →
    (∀ u, Φ u = c₀ + ∑' ξ, chi δ ξ u * c ξ) → IntegrableOn Φ (FS2 F) (adeleMeasurePi F) ∧
    IntegrableOn (fun u => Φ u * ψ (2 * u 0)) (FS2 F) (adeleMeasurePi F) ∧
    ∫ u in FS2 F, Φ u ∂(adeleMeasurePi F) = c₀ + c 0 ∧ ∫ u in FS2 F, Φ u * ψ (2 * u 0) ∂(adeleMeasurePi F) = c ![1, 0] := by
  intro F _ _ δ hδ c₀ c Φ hc hΦ
  set L : (Fin 2 → F) → Fin 2 → F := fun ξ => ![-(2 * ξ 0), 2 * δ * ξ 1] with hL
  have hchi : ∀ ξ u, chi δ ξ u = E (L ξ) u := by
    intro ξ u
    simp only [chi, E, hL]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_mul, map_ofNat]
    ring
  have hΦ' : ∀ u, Φ u = c₀ + ∑' ξ, E (L ξ) u * c ξ := fun u => by
    rw [hΦ]; simp only [hchi]
  set κ : Fin 2 → F := ![2, 0] with hκ
  have hψ : ∀ u : Fin 2 → A F, ψ (2 * u 0) = E κ u := by
    intro u
    have h2A : rt (2 : F) = (2 : A F) := map_ofNat _ 2
    simp only [E, hκ]
    congr 1
    simp [h2A]
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hκ0 : κ ≠ 0 := fun h => h2 (by simpa [hκ] using congrFun h 0)
  obtain ⟨i0, s0⟩ := core 0 L c₀ c hc Φ hΦ'
  obtain ⟨i1, s1⟩ := core κ L c₀ c hc Φ hΦ'
  simp only [E_zero, mul_one, zero_add] at i0 s0
  simp only [← hψ] at i1
  refine ⟨i0, i1, ?_, ?_⟩
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c 0) := by
      have hL0 : L 0 = 0 := by
        ext i; fin_cases i <;> simp [hL]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (L ξ) u ∂(adeleMeasurePi F)) * c ξ) (0 : Fin 2 → F) (fun ξ hξ => by
        have hne : L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · exact a0
          · exact a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s0.unique t
    have e2 : ∫ u in FS2 F, (1 : ℂ) ∂(adeleMeasurePi F) = 1 := by
      simpa only [E_zero] using E_int_zero (F := F)
    rw [e2, mul_one] at e1
    rw [sub_eq_iff_eq_add] at e1
    rw [e1, add_comm]
  · have t : HasSum (fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (c ![1, 0]) := by
      have hL0 : κ + L ![1, 0] = 0 := by
        ext i; fin_cases i <;> simp [hL, hκ]
      have := hasSum_single (f := fun ξ => (∫ u in FS2 F, E (κ + L ξ) u ∂(adeleMeasurePi F)) * c ξ) (![1, 0] : Fin 2 → F) (fun ξ hξ => by
        have hne : κ + L ξ ≠ 0 := fun h => hξ (by
          have a0 := congrFun h 0
          have a1 := congrFun h 1
          simp only [hL, hκ, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_add, mul_eq_zero, h2, hδ, false_or] at a0 a1
          ext i; fin_cases i
          · have : 2 * (1 - ξ 0) = 0 := by linear_combination a0
            have := (mul_eq_zero.1 this).resolve_left h2
            simpa using (sub_eq_zero.1 this).symm
          · simpa using a1)
        rw [E_int _ hne, zero_mul])
      simpa only [hL0, E_int_zero, one_mul] using this
    have e1 := s1.unique t
    rw [E_int κ hκ0, mul_zero, sub_zero] at e1
    simpa only [hψ] using e1
end
