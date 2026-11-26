module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Lemmata.GeneralBFactLeftExtra.Imports
public import Lemmata.GeneralBFactLast.Imports
public import Lemmata.GeneralBFactTail.Imports

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem ae_eval_ne_zero_of_ne_zero_fin : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℂ)), MvPolynomial.eval x f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℂ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hmeas : MeasurableSet {z : ℂ × (Fin m → ℂ) | MvPolynomial.eval (e.symm z) f ≠ 0} :=
      ((MvPolynomial.continuous_eval f).measurable.comp e.symm.measurable)
        (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℂ × (Fin m → ℂ))), MvPolynomial.eval (e.symm z) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (e.symm (y, s)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      have hQ : Polynomial.map (MvPolynomial.eval s) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval s) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := hfin.measure_zero (volume : Measure ℂ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (e.symm (y, s) : Fin (m + 1) → ℂ) = Fin.cons y s := by
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

theorem ae_eval_ne_zero_linear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] (L : V ≃ₗ[ℂ] (ι → ℂ))
    (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ x ∂μ, MvPolynomial.eval (L x) f ≠ 0 := by
  set e := Fintype.equivFin ι
  set g := MvPolynomial.rename e f
  have hg : g ≠ 0 := by
    intro h
    apply hf
    exact MvPolynomial.rename_injective _ e.injective (by rw [map_zero]; exact h)
  set L' : V ≃ₗ[ℂ] (Fin (Fintype.card ι) → ℂ) := L.trans (LinearEquiv.funCongrLeft ℂ ℂ e.symm)
  have hL' : ∀ x, MvPolynomial.eval (L' x) g = MvPolynomial.eval (L x) f := by
    intro x
    have hc : (L' x : Fin (Fintype.card ι) → ℂ) ∘ e = L x := by
      funext i
      simp [L', LinearEquiv.funCongrLeft_apply]
    simp only [g, MvPolynomial.eval_rename, hc]
  have hac : μ.map L' ≪ volume := Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h1 : ∀ᵐ y ∂(μ.map L'), MvPolynomial.eval y g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_of_ne_zero_fin _ g hg)
  have hmeasL : Measurable L' := L'.toContinuousLinearEquiv.continuous.measurable
  have hmeasS : MeasurableSet {y : Fin (Fintype.card ι) → ℂ | MvPolynomial.eval y g ≠ 0} :=
    (MvPolynomial.continuous_eval g).measurable (measurableSet_singleton 0).compl
  rw [ae_map_iff hmeasL.aemeasurable hmeasS] at h1
  filter_upwards [h1] with x hx
  rwa [← hL']

theorem eval_blockScale_eq_prod_pow_mul {B n : ℕ} (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF : IsMultiHomogeneous a F) (r : Fin B → ℂ) (x : Fin B × Fin n → ℂ) :
    MvPolynomial.eval (fun p => r p.1 * x p) F = (∏ b, r b ^ a b) * MvPolynomial.eval x F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h1 : ∏ p, (r p.1 * x p) ^ s p = (∏ b, r b ^ a b) * ∏ p, x p ^ s p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun b _ => ?_
    show ∏ j, r b ^ s (b, j) = r b ^ a b
    rw [Finset.prod_pow_eq_pow_sum, hF s hs b]
  rw [h1]
  ring

def blockCoordEquiv (B n : ℕ) : (Fin B → EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ] (Fin B × Fin n → ℂ) :=
  (LinearEquiv.piCongrRight fun _ => WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (LinearEquiv.curry ℂ ℂ (Fin B) (Fin n)).symm

theorem blockCoordEquiv_apply {B n : ℕ} (y : Fin B → EuclideanSpace ℂ (Fin n)) (p : Fin B × Fin n) :
    blockCoordEquiv B n y p = WithLp.ofLp (y p.1) p.2 := rfl

theorem ae_toSphere (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere),
      MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  set E := EuclideanSpace ℂ (Fin n)
  set νS := (volume : Measure E).toSphere
  set ρ := Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  set Z : Set (Fin B → sphere (0 : E) 1) := {z | MvPolynomial.eval (blockPoint z) F = 0}
  have hZ : MeasurableSet Z := by
    have : Continuous fun z : Fin B → sphere (0 : E) 1 => MvPolynomial.eval (blockPoint z) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      refine continuous_pi fun p => ?_
      unfold blockPoint spherePoint
      fun_prop
    exact this.measurable (measurableSet_singleton 0)
  have : (Measure.pi fun _ : Fin B => (volume : Measure E)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : IsFiniteMeasure νS := by show IsFiniteMeasure ((volume : Measure E).toSphere); infer_instance
  have : SigmaFinite ρ := by show SigmaFinite (Measure.volumeIoiPow (Module.finrank ℝ E - 1)); infer_instance
  have hlin : ∀ᵐ y ∂(Measure.pi fun _ : Fin B => (volume : Measure E)),
      MvPolynomial.eval (blockCoordEquiv B n y) F ≠ 0 :=
    ae_eval_ne_zero_linear _ (blockCoordEquiv B n) F hF0
  set S : Set (Fin B → E) := {y | MvPolynomial.eval (blockCoordEquiv B n y) F = 0}
  have hS0 : (Measure.pi fun _ : Fin B => (volume : Measure E)) S = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hlin] with y hy
    exact hy
  have hSm : MeasurableSet S := by
    have : Continuous fun y : Fin B → E => MvPolynomial.eval (blockCoordEquiv B n y) F := by
      refine (MvPolynomial.continuous_eval F).comp ?_
      exact (blockCoordEquiv B n).toContinuousLinearEquiv.continuous
    exact this.measurable (measurableSet_singleton 0)
  have h1 := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
  have hprodSF : SigmaFinite (νS.prod ρ) := inferInstance
  have hT := measurePreserving_pi (hν := fun _ => hprodSF)
    (fun _ : Fin B => (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
    (fun _ => νS.prod ρ) (fun _ => h1)
  have hA := measurePreserving_arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
    (fun _ => νS) (fun _ => ρ)
  set A := MeasurableEquiv.arrowProdEquivProdArrow (sphere (0 : E) 1) (Set.Ioi (0 : ℝ)) (Fin B)
  set T : (Fin B → ({0}ᶜ : Set E)) → (Fin B → sphere (0 : E) 1 × Set.Ioi (0 : ℝ)) :=
    fun x b => homeomorphUnitSphereProd E (x b)
  have hW : MeasurableSet (Z ×ˢ (Set.univ : Set (Fin B → Set.Ioi (0 : ℝ)))) :=
    hZ.prod MeasurableSet.univ
  have hAW : MeasurableSet (A ⁻¹' (Z ×ˢ Set.univ)) := A.measurable hW
  have e1 := Measure.prod_prod (μ := Measure.pi fun _ : Fin B => νS)
    (ν := Measure.pi fun _ : Fin B => ρ) Z Set.univ
  rw [← hA.measure_preimage hW.nullMeasurableSet, ← hT.measure_preimage hAW.nullMeasurableSet] at e1
  set G : (Fin B → ({0}ᶜ : Set E)) → (Fin B → E) := fun x b => (x b : E)
  have hsub : T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ)) ⊆ G ⁻¹' S := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true] at hx
    have hx' : MvPolynomial.eval (blockPoint fun b => (homeomorphUnitSphereProd E (x b)).1) F = 0 := by
      simpa [A, T, Z, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow] using hx
    have hcoord : blockCoordEquiv B n (G x) = fun p => ((‖(x p.1 : E)‖ : ℝ) : ℂ) *
        blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1) p := by
      funext p
      have hne : ‖(x p.1 : E)‖ ≠ 0 := norm_ne_zero_iff.2 (x p.1).2
      simp only [blockCoordEquiv_apply, G, blockPoint, spherePoint, homeomorphUnitSphereProd_apply_fst_coe]
      rw [← Complex.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one, one_mul]
    show MvPolynomial.eval (blockCoordEquiv B n (G x)) F = 0
    have hsc := eval_blockScale_eq_prod_pow_mul a F hF (fun b => ((‖(x b : E)‖ : ℝ) : ℂ))
      (blockPoint (fun b => (homeomorphUnitSphereProd E (x b)).1))
    rw [hcoord, hsc, hx', mul_zero]
  have hmap : ∀ _ : Fin B, ((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map
      Subtype.val = (volume : Measure E).restrict {0}ᶜ :=
    fun _ => map_comap_subtype_coe (measurableSet_singleton 0).compl _
  have hmSF : ∀ i : Fin B, SigmaFinite
      (((volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map Subtype.val) := by
    intro i; rw [hmap i]; infer_instance
  have hG : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E)).map G =
      Measure.pi fun _ : Fin B => (volume : Measure E).restrict {0}ᶜ := by
    rw [Measure.pi_map_pi (hμ := hmSF) (fun _ => measurable_subtype_coe.aemeasurable)]
    exact congrArg _ (funext hmap)
  have hGm : Measurable G := Measurable.of_eval fun b => measurable_subtype_coe.comp
    (measurable_pi_apply b)
  have hzero : (Measure.pi fun _ : Fin B =>
      (volume : Measure E).comap (Subtype.val : ({0}ᶜ : Set E) → E))
      (T ⁻¹' (A ⁻¹' (Z ×ˢ Set.univ))) = 0 := by
    refine measure_mono_null hsub ?_
    rw [← Measure.map_apply hGm hSm, hG, ← Measure.restrict_pi_pi]
    exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hS0.le)
  have hρ : ρ Set.univ ≠ 0 := by
    intro h
    have h2 := measure_mono_null (Set.subset_univ (Set.Iio (⟨1, by norm_num⟩ : Set.Ioi (0 : ℝ)))) h
    have h3 := Measure.volumeIoiPow_apply_Iio (Module.finrank ℝ E - 1) ⟨1, by norm_num⟩
    rw [show ρ (Set.Iio ⟨1, by norm_num⟩) = _ from h3] at h2
    rw [ENNReal.ofReal_eq_zero] at h2
    have h4 : (0 : ℝ) < (1 : ℝ) ^ (Module.finrank ℝ E - 1 + 1) / ((Module.finrank ℝ E - 1 : ℕ) + 1) := by
      positivity
    exact absurd h2 (not_le.2 h4)
  have hpiρ : (Measure.pi fun _ : Fin B => ρ) Set.univ ≠ 0 := by
    rw [Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hρ
  rw [hzero] at e1
  have hZ0 : (Measure.pi fun _ : Fin B => νS) Z = 0 := by
    rcases mul_eq_zero.1 e1.symm with h | h
    · exact h
    · exact absurd h hpiρ
  rw [measure_eq_zero_iff_ae_notMem] at hZ0
  filter_upwards [hZ0] with z hz
  exact hz

theorem blockSphereMeasure_eq (B n : ℕ) :
    blockSphereProb B n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ)⁻¹ ^ B •
      Measure.pi fun _ : Fin B => (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere := by
  unfold blockSphereProb
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [sphereProb, ProbabilityTheory.cond_apply MeasurableSet.univ, Set.univ_inter,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem ae_blockSphere_eval_ne_zero (B n : ℕ) (a : Fin B → ℕ) (F : MvPolynomial (Fin B × Fin n) ℂ)
    (hF0 : F ≠ 0) (hF : IsMultiHomogeneous a F) :
    ∀ᵐ z ∂(blockSphereProb B n), MvPolynomial.eval (blockPoint z) F ≠ 0 := by
  rw [blockSphereMeasure_eq]
  exact Measure.ae_smul_measure (ae_toSphere B n a F hF0 hF) _

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.LatSemiSt
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def UnipotentStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (γ : Matrix (Fin r) (Fin r) K)
    (Q : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) →
    (Real.exp (1 / 3) + 1) * r < g → (∀ σ, (Q σ).det ≠ 0) →
    (∀ σ (u : Fin r → ℂ), normSq ((Q σ * γ.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * normSq u) →
    (γ - 1) ^ r = 0 ∧ ∀ σ, ∑ a, ∑ b, ‖(Q σ * (γ.map σ - 1) * (Q σ)⁻¹) a b‖ ^ 2 < 1

def hq {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) : ℝ := (star u ⬝ᵥ (H *ᵥ u)).re

structure Majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) where

  H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ
  posDef : ∀ σ, (H σ).PosDef
  major : ∀ σ, H σ * (S.G.map σ)⁻¹ * H σ = S.G.map σ
  conj_compat : ∀ σ, H ((starRingEnd ℂ).comp σ) = (H σ).map (starRingEnd ℂ)

def gramC {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (b j))

def IsKBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) : Prop :=
  (∀ i, b i ∈ B) ∧ LinearIndependent K b ∧ ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)

def latDeg {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℝ :=
  Real.log ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re

def IsSemistableZero {K : Type} [Field K] [NumberField K] {r : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  (∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn L b → latDeg H L b = 0) ∧
  ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L →
    ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg H B b ≤ 0

def gramX {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin k) (Fin m) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (c j))

def quotGramC {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin m) (Fin m) ℂ :=
  gramC H σ c - gramX H σ c b * (gramC H σ b)⁻¹ * gramX H σ b c

def satSub {K : Type} [Field K] [NumberField K] {r k : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin r → K) :=
  L ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)

def quotDeg {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : ℝ :=
  Real.log ((satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re

def DegAddStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k m : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K),
    (∀ σ, (H σ).PosDef) → L.FG → (∀ i, b i ∈ L) → (∀ j, c j ∈ L) →
    LinearIndependent K (Fin.append b c) →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c))) →
    latDeg H L (Fin.append b c) = latDeg H (satSub L b) b + quotDeg H L b c

def SemiPointStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L

def SemistableStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L ∧
      ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
        (∀ σ (u : Fin r → ℂ), u ≠ 0 → hq (M.H σ) (N.map σ *ᵥ u) < hq (M.H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.ShareDetA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Filter Topology Set

theorem analyticOnNhd_V_of_differentiableOn {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) :
    AnalyticOnNhd ℂ f B := by
  intro x hx
  let e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' B) := hB.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' B) :=
    hf.comp e.symm.differentiable.differentiableOn (fun y hy => hy)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU hg (e x) (by simpa using hx)
  have hfe : f = (f ∘ e.symm) ∘ e := by ext y; simp
  rw [hfe]
  exact ha.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)).analyticAt x)

theorem differentiableOn_finset_prod' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] {F : ι → E → ℂ} {B : Set E}
    (hF : ∀ i, DifferentiableOn ℂ (F i) B) (s : Finset ι) :
    DifferentiableOn ℂ (fun v => ∏ i ∈ s, F i v) B := by
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a).mul ih

theorem differentiableOn_det_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Type} [Fintype U] [DecidableEq U] {F : U → U → E → ℂ} {B : Set E}
    (hF : ∀ a b, DifferentiableOn ℂ (F a b) B) :
    DifferentiableOn ℂ (fun v => (Matrix.of fun a b => F a b v).det) B := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  exact (differentiableOn_const _).mul
    (differentiableOn_finset_prod' (F := fun i v => F (σ i) i v) (fun i => hF _ _) _)

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.GaussAbsMulOfMonomialOrder
namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

section Gauss

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

theorem coeff_le_gauss_abs (w : FinitePlace K) (f : MvPolynomial σ K) (s : σ →₀ ℕ) :
    w (f.coeff s) ≤ gaussAbs w f := by
  unfold gaussAbs
  by_cases hs : s ∈ f.support
  · have h := Finset.le_sup (f := fun s => (w (f.coeff s)).toNNReal) hs
    have h2 : ((w (f.coeff s)).toNNReal : ℝ) ≤ _ := NNReal.coe_le_coe.2 h
    rwa [Real.coe_toNNReal _ (apply_nonneg w _)] at h2
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero]
    exact NNReal.coe_nonneg _

theorem gauss_abs_le_of_coeff_le (w : FinitePlace K) (f : MvPolynomial σ K) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s, w (f.coeff s) ≤ M) : gaussAbs w f ≤ M := by
  unfold gaussAbs
  have h1 : (f.support.sup fun s => (w (f.coeff s)).toNNReal) ≤ M.toNNReal :=
    Finset.sup_le fun s _ => Real.toNNReal_le_toNNReal (h s)
  have h2 := NNReal.coe_le_coe.2 h1
  rwa [Real.coe_toNNReal _ hM] at h2

theorem gauss_abs_attained_at_coeff (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ s ∈ f.support, gaussAbs w f = w (f.coeff s) := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup f.support
    (MvPolynomial.support_nonempty.2 hf) (fun s => (w (f.coeff s)).toNNReal)
  refine ⟨s, hs, ?_⟩
  unfold gaussAbs
  rw [hsup, Real.coe_toNNReal _ (apply_nonneg w _)]

theorem gauss_abs_pos_of_ne_zero (w : FinitePlace K) (f : MvPolynomial σ K) (hf : f ≠ 0) :
    0 < gaussAbs w f := by
  obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
  rw [h]
  exact FinitePlace.pos_iff.2 (MvPolynomial.mem_support_iff.1 hs)

theorem finite_place_sum_le {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  first | exact Bl.general_b_fact_left_extra.goal1 .. | (apply Bl.general_b_fact_left_extra.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_extra.goal1 <;> assumption)

theorem finite_place_sum_lt {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 < M) (h : ∀ i ∈ t, w (a i) < M) : w (∑ i ∈ t, a i) < M := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hM
  | insert j t hj ih =>
    rw [Finset.sum_insert hj]
    refine (FinitePlace.add_le w _ _).trans_lt (max_lt (h j (Finset.mem_insert_self j t)) ?_)
    exact ih fun i hi => h i (Finset.mem_insert_of_mem hi)

theorem finite_place_add_eq_of_lt (w : FinitePlace K) (x y : K) (h : w y < w x) : w (x + y) = w x := by
  apply le_antisymm
  · exact (FinitePlace.add_le w x y).trans (max_le le_rfl h.le)
  · have h1 : w x ≤ max (w (x + y)) (w (-y)) := by
      have := FinitePlace.add_le w (x + y) (-y)
      rwa [add_neg_cancel_right] at this
    rw [map_neg_eq_map] at h1
    rcases le_max_iff.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 (not_le.2 h)

theorem gauss_abs_mul_of_monomial_order (m : MonomialOrder σ) (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  classical
  have hGf := gauss_abs_pos_of_ne_zero w f hf
  have hGg := gauss_abs_pos_of_ne_zero w g hg
  apply le_antisymm
  · refine gauss_abs_le_of_coeff_le w _ (mul_nonneg hGf.le hGg.le) fun u => ?_
    rw [MvPolynomial.coeff_mul]
    refine finite_place_sum_le w _ _ (mul_nonneg hGf.le hGg.le) fun x _ => ?_
    rw [map_mul]
    exact mul_le_mul (coeff_le_gauss_abs w f _) (coeff_le_gauss_abs w g _) (apply_nonneg w _) hGf.le
  ·
    set Sf := f.support.filter (fun s => w (f.coeff s) = gaussAbs w f)
    set Sg := g.support.filter (fun s => w (g.coeff s) = gaussAbs w g)
    have hSf : Sf.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w f hf
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    have hSg : Sg.Nonempty := by
      obtain ⟨s, hs, h⟩ := gauss_abs_attained_at_coeff w g hg
      exact ⟨s, Finset.mem_filter.2 ⟨hs, h.symm⟩⟩
    obtain ⟨s0, hs0, hs0max⟩ := Finset.exists_max_image Sf (fun s => m.toSyn s) hSf
    obtain ⟨t0, ht0, ht0max⟩ := Finset.exists_max_image Sg (fun s => m.toSyn s) hSg
    have hfs0 : w (f.coeff s0) = gaussAbs w f := (Finset.mem_filter.1 hs0).2
    have hgt0 : w (g.coeff t0) = gaussAbs w g := (Finset.mem_filter.1 ht0).2
    have hbigf : ∀ s, m.toSyn s0 < m.toSyn s → w (f.coeff s) < gaussAbs w f := by
      intro s hs
      refine lt_of_le_of_ne (coeff_le_gauss_abs w f s) fun heq => ?_
      have hmem : s ∈ Sf := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGf.ne heq
      exact absurd (hs0max s hmem) (not_le.2 hs)
    have hbigg : ∀ t, m.toSyn t0 < m.toSyn t → w (g.coeff t) < gaussAbs w g := by
      intro t ht
      refine lt_of_le_of_ne (coeff_le_gauss_abs w g t) fun heq => ?_
      have hmem : t ∈ Sg := by
        refine Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 fun h0 => ?_, heq⟩
        rw [h0, map_zero] at heq
        exact hGg.ne heq
      exact absurd (ht0max t hmem) (not_le.2 ht)
    have hmemu : (s0, t0) ∈ Finset.HasAntidiagonal.antidiagonal (s0 + t0) := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    have hrest : w (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (s0 + t0)).erase (s0, t0),
        f.coeff x.1 * g.coeff x.2) < gaussAbs w f * gaussAbs w g := by
      refine finite_place_sum_lt w _ _ (mul_pos hGf hGg) fun x hx => ?_
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.1 hx
      have hsum : x.1 + x.2 = s0 + t0 := Finset.HasAntidiagonal.mem_antidiagonal.1 hxmem
      have hsyn : m.toSyn x.1 + m.toSyn x.2 = m.toSyn s0 + m.toSyn t0 := by
        rw [← map_add (f := _), ← map_add (f := _), hsum]
      rw [map_mul]
      rcases lt_trichotomy (m.toSyn x.1) (m.toSyn s0) with h1 | h1 | h1
      · have h2 : m.toSyn t0 < m.toSyn x.2 := by
          by_contra h2
          have := add_lt_add_of_lt_of_le h1 (not_lt.1 h2)
          rw [hsyn] at this
          exact lt_irrefl _ this
        calc w (f.coeff x.1) * w (g.coeff x.2) ≤ gaussAbs w f * w (g.coeff x.2) :=
              mul_le_mul_of_nonneg_right (coeff_le_gauss_abs w f _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_left (hbigg _ h2) hGf
      · exfalso
        have e1 : x.1 = s0 := m.toSyn.injective h1
        have e2 : x.2 = t0 := by
          rw [e1] at hsum
          exact add_left_cancel hsum
        exact hxne (Prod.ext e1 e2)
      · calc w (f.coeff x.1) * w (g.coeff x.2) ≤ w (f.coeff x.1) * gaussAbs w g :=
              mul_le_mul_of_nonneg_left (coeff_le_gauss_abs w g _) (apply_nonneg w _)
          _ < gaussAbs w f * gaussAbs w g := mul_lt_mul_of_pos_right (hbigf _ h1) hGg
    have hcoeff : w ((f * g).coeff (s0 + t0)) = gaussAbs w f * gaussAbs w g := by
      rw [MvPolynomial.coeff_mul, ← Finset.add_sum_erase _ _ hmemu]
      rw [finite_place_add_eq_of_lt w _ _ (by rwa [map_mul, hfs0, hgt0]), map_mul, hfs0, hgt0]
    rw [← hcoeff]
    exact coeff_le_gauss_abs w _ _

theorem gauss_abs_mul [Fintype σ] (w : FinitePlace K)
    (f g : MvPolynomial σ K) (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussAbs w (f * g) = gaussAbs w f * gaussAbs w g := by
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  exact gauss_abs_mul_of_monomial_order MonomialOrder.lex w f g hf hg

end Gauss

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.FinrankRestrictTotalDegree
namespace ReciprocityTheory.MultiplicativeHeights

noncomputable def degreeLeEquivAntidiag (D e : ℕ) :
    {α : Fin D →₀ ℕ // α.degree ≤ e} ≃
      ((Finset.univ : Finset (Fin (D + 1))).finsuppAntidiag e) where
  toFun α := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (e - α.1.degree) (⇑α.1)), by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fin.sum_univ_succ]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ]
    rw [← Finsupp.degree_eq_sum]
    have := α.2
    omega⟩
  invFun β := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail ⇑β.1), by
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    ext i
    simp
  right_inv β := by
    apply Subtype.ext
    ext i
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero]
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
      omega
    · simp [Fin.tail]

theorem card_degree_le (D e : ℕ) :
    Nat.card {α : Fin D →₀ ℕ // α.degree ≤ e} = (e + D).choose D := by
  rw [Nat.card_congr (degreeLeEquivAntidiag D e), Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin,
    show D + 1 + e - 1 = D + e by omega, ← Nat.choose_symm_add, add_comm]

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.DetSubtypeCompAssociatedProd
namespace ReciprocityTheory.MultiplicativeHeights

open Module Submodule

theorem det_subtype_comp_associated_prod {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) (N : Submodule R M)
    (h : finrank R N = finrank R M) (e : M ≃ₗ[R] N) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by
  first | exact Bl.general_b_fact_tail.goal1 .. | (apply Bl.general_b_fact_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_tail.goal1 <;> assumption)

theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  first | exact Bl.general_b_fact'''''''.goal1 .. | (apply Bl.general_b_fact'''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''''''.goal1 <;> assumption)

theorem gaugeSplitting_holds : NormLengthStatement := by
  intro O B _ _ _ _ _ _ _ _ g hg
  classical
  have : Module.Free O B := Module.free_iff_isTorsionFree.mpr inferInstance
  set b := Module.Free.chooseBasis O B
  set I : Ideal B := Ideal.span ({g} : Set B)
  have hI : I ≠ ⊥ := by simpa [I] using hg
  have h := Ideal.finrank_eq_finrank b I hI
  have hlen : Module.length O (B ⧸ I) =
      ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i) := by
    rw [(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i) := by
    rw [Algebra.norm_apply]
    have key := det_subtype_comp_associated_prod b (I.restrictScalars O) h
      (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))
    convert key using 2
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have h1 := Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i
    refine Eq.trans ?_ (congrArg Subtype.val h1).symm
    rw [Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
    rfl
  rw [hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]
  exact Ring.ord_eq_of_associated hdet

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.GaussValExists
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial

noncomputable def gaussRed {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    MvPolynomial σ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) :=
  ∑ α ∈ p.support, monomial α (IsLocalRing.residue _ ⟨p.coeff α, hc α⟩)

theorem gaussRed_coeff {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (V : ValuationSubring U) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) (α : σ →₀ ℕ) :
    (gaussRed V p hc).coeff α = IsLocalRing.residue _ ⟨p.coeff α, hc α⟩ := by
  classical
  unfold gaussRed
  rw [MvPolynomial.coeff_sum]
  by_cases h : α ∈ p.support
  · rw [Finset.sum_eq_single α]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [MvPolynomial.coeff_monomial, if_neg hb]
    · intro h'
      exact absurd h h'
  · have h0 : p.coeff α = 0 := by simpa [MvPolynomial.mem_support_iff] using h
    have hz : (⟨p.coeff α, hc α⟩ : V.comap (algebraMap Ω U)) = 0 := Subtype.ext h0
    rw [Finset.sum_eq_zero, hz, map_zero]
    intro b hb
    rw [MvPolynomial.coeff_monomial, if_neg]
    rintro rfl
    exact h hb

theorem gaussRed_eval {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V) (p : MvPolynomial σ Ω)
    (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U)) :
    letI := residueAlgebra V (algebraMap Ω U)
    ∃ h : aeval t p ∈ V, IsLocalRing.residue V ⟨aeval t p, h⟩ =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V p hc) := by
  try dsimp only
  letI := residueAlgebra V (algebraMap Ω U)
  classical
  obtain ⟨y, hydef⟩ : ∃ y : V, y = ∑ α ∈ p.support,
      comapInclusion V (algebraMap Ω U) ⟨p.coeff α, hc α⟩ *
        ∏ s ∈ α.support, (⟨t s, ht s⟩ : V) ^ α s := ⟨_, rfl⟩
  have hy : (y : U) = aeval t p := by
    change V.subtype y = _
    rw [hydef, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_prod, map_pow]
    rfl
  have hmem : aeval t p ∈ V := by
    rw [← hy]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyy : (⟨aeval t p, hmem⟩ : V) = y := Subtype.ext hy.symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hyy, hydef, map_sum]
  unfold gaussRed
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.aeval_monomial]
  simp only [map_mul, map_prod, map_pow]
  congr 1

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.IntCoresA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

theorem continuous_spherePoint (n : ℕ) : Continuous (spherePoint : UnitSphereC n → Fin n → ℂ) := by
  unfold spherePoint
  fun_prop

theorem sphere_zero_null (hSJ : SJStatement) {n a : ℕ} (g : MvPolynomial (Fin n) ℂ)
    (hg : g.IsHomogeneous a) (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1)
    (hgu : MvPolynomial.eval (WithLp.ofLp u) g ≠ 0) :
    sphereProb n {z | MvPolynomial.eval (spherePoint z) g = 0} = 0 := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [EuclideanSpace.norm_eq] at hu
    · exact h
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℂ) (by simp [hn])
  have h0 : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ 0 := by
    rw [Measure.toSphere_apply_univ]
    refine mul_ne_zero ?_ (measure_ball_pos _ _ one_pos).ne'
    exact_mod_cast Module.finrank_pos.ne'
  have htop : (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere Set.univ ≠ ⊤ := by
    rw [Measure.toSphere_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) measure_ball_lt_top.ne
  haveI : IsProbabilityMeasure (sphereProb n) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite h0 htop
  set μ := sphereProb n with hμ
  set Z := {z : UnitSphereC n | MvPolynomial.eval (spherePoint z) g = 0} with hZdef
  have hZ : MeasurableSet Z :=
    (isClosed_eq ((MvPolynomial.continuous_eval g).comp (continuous_spherePoint n))
      continuous_const).measurableSet
  obtain ⟨hint, -⟩ := hSJ n a g u hg hu hgu
  have key : ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤
      (∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ) -
        Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ + (a : ℝ) / 2 * (harmonic (n - 1) : ℝ) := by
    intro c hc
    have hgc : (MvPolynomial.C c * g).IsHomogeneous a := by
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) c).mul hg
    obtain ⟨-, hle⟩ := hSJ n a (MvPolynomial.C c * g) u hgc hu (by simp [hc, hgu])
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C] at hle
    have hpt : ∀ z : UnitSphereC n, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ =
        Zᶜ.indicator (fun _ ↦ Real.log ‖c‖) z + Real.log ‖MvPolynomial.eval (spherePoint z) g‖ := by
      intro z
      by_cases hz : MvPolynomial.eval (spherePoint z) g = 0
      · have hzZ : z ∈ Z := hz
        simp [Set.indicator_apply, hzZ, hz]
      · have hzZ : z ∈ Zᶜ := hz
        rw [Set.indicator_of_mem hzZ, norm_mul,
          Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hz)]
    have hI : ∫ z, Real.log ‖c * MvPolynomial.eval (spherePoint z) g‖ ∂μ =
        (μ Zᶜ).toReal * Real.log ‖c‖ + ∫ z, Real.log ‖MvPolynomial.eval (spherePoint z) g‖ ∂μ := by
      simp_rw [hpt]
      rw [integral_add ((integrable_const _).indicator hZ.compl) hint,
        integral_indicator_const _ hZ.compl, smul_eq_mul]
      try rfl
    have hcomp : (μ Zᶜ).toReal = 1 - (μ Z).toReal := by
      rw [prob_compl_eq_one_sub hZ, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
        ENNReal.toReal_one]
    have hL : Real.log ‖c * MvPolynomial.eval (WithLp.ofLp u) g‖ =
        Real.log ‖c‖ + Real.log ‖MvPolynomial.eval (WithLp.ofLp u) g‖ := by
      rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hgu)]
    rw [hI, hcomp, hL] at hle
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ c : ℂ, c ≠ 0 → (μ Z).toReal * Real.log ‖c‖ ≤ K := ⟨_, key⟩
  by_contra hne
  have hp : 0 < (μ Z).toReal := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have h1 := hK ((Real.exp ((|K| + 1) / (μ Z).toReal) : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_exp] at h1
  have h2 : (μ Z).toReal * ((|K| + 1) / (μ Z).toReal) = |K| + 1 := by
    field_simp
  linarith [le_abs_self K]

end ReciprocityTheory.MultiplicativeHeights
end
end
