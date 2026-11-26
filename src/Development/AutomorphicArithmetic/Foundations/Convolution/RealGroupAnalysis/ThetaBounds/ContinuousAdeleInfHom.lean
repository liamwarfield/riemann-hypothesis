module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K]

private theorem inv_map_mulVec {R : Type} [CommRing R] (h : A K →+* R) (g : GL (Fin 4) (A K))
    (v : Fin 4 → A K) :
    (g⁻¹).val.map h *ᵥ (fun i => h ((g.val *ᵥ v) i)) = fun i => h (v i) := by
  rw [map_mulVec_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.map_one h (map_zero h) (map_one h), Matrix.one_mulVec]

private theorem continuous_adeleInfHom : Continuous (adeleInfHom : A K → mixedSpace K) :=
  (homeomorphMixedSpace K).continuous.comp continuous_fst

private theorem continuous_adeleFinHom : Continuous (adeleFinHom : A K → FiniteAdeleRing (𝓞 K) K) :=
  continuous_snd

private theorem continuous_invEntry (i j : Fin 4) :
    Continuous fun x : GL (Fin 4) (A K) => (x⁻¹).val i j :=
  (Units.continuous_val.comp continuous_inv).matrix_elem i j

private theorem wt_nonneg (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) :
    0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_le_of {S S' : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)} {N : ℕ} {v w : V4 K} {m : ℝ}
    (hm1 : 1 ≤ m) (h : finPartPi w ∈ S → finPartPi v ∈ S' ∧ ‖infPartPi v‖ ≤ m * ‖infPartPi w‖) :
    wt S N w ≤ m ^ N * wt S' N v := by
  have hm0 : 0 ≤ m ^ N := by positivity
  by_cases hv : finPartPi w ∈ S
  · obtain ⟨hfin, hs⟩ := h hv
    generalize hsd : ‖infPartPi v‖ = s at hs
    generalize htd : ‖infPartPi w‖ = t at hs
    have ht0 : 0 ≤ t := htd ▸ norm_nonneg _
    have hs0 : 0 ≤ s := hsd ▸ norm_nonneg _
    have h1 : 1 + s ≤ m * (1 + t) := by nlinarith
    have hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 N
    have e1 : wt S N w = ((1 + t) ^ N)⁻¹ := by rw [← htd]; exact if_pos hv
    have e2 : wt S' N v = ((1 + s) ^ N)⁻¹ := by rw [← hsd]; exact if_pos hfin
    rw [e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have : wt S N w = 0 := if_neg hv
    rw [this]
    exact mul_nonneg hm0 (wt_nonneg _ _ _)

private theorem norm_mulVec_le (M : Matrix (Fin 4) (Fin 4) (mixedSpace K))
    (u : Fin 4 → mixedSpace K) : ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

end

end UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding in
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtLin :
    ∀ (F : Type) [Field F] [NumberField F], WtLin F := by
  intro F _ _ C hC K hK

  let ψ : GL (Fin 4) (A F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) → (Fin 4 → FiniteAdeleRing (𝓞 F) F) :=
    fun p => (p.1⁻¹).val.map adeleFinHom *ᵥ p.2
  have hψ : Continuous ψ := by
    exact (Continuous.matrix_map (Units.continuous_val.comp (continuous_inv.comp continuous_fst))
      continuous_adeleFinHom).matrix_mulVec continuous_snd
  refine ⟨ψ '' (C ×ˢ K), (hC.prod hK).image hψ, fun N => ?_⟩

  let β : GL (Fin 4) (A F) → ℝ := fun x => ∑ i, ∑ j, ‖(x⁻¹).val.map (adeleInfHom (K := F)) i j‖
  have hβ : Continuous β := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_adeleInfHom.comp (continuous_invEntry i j)).norm
  obtain ⟨B₀, hB₀⟩ := (hC.image hβ).bddAbove
  have hβle : ∀ x ∈ C, β x ≤ B₀ := fun x hx => hB₀ ⟨x, hx, rfl⟩
  set m : ℝ := max 1 B₀ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  refine ⟨m ^ N, fun x hx v => ?_⟩
  refine wt_le_of hm1 fun hv => ?_
  have hfin : finPartPi v ∈ ψ '' (C ×ˢ K) := by
    refine ⟨(x, finPartPi (x.val *ᵥ v)), ⟨hx, hv⟩, ?_⟩
    have := inv_map_mulVec (adeleFinHom (K := F)) x v
    simpa only [ψ, finPartPi_eq_adeleFinHom] using this
  have hinf : infPartPi v = (x⁻¹).val.map adeleInfHom *ᵥ infPartPi (x.val *ᵥ v) := by
    have := inv_map_mulVec (adeleInfHom (K := F)) x v
    simpa only [infPartPi_eq_adeleInfHom] using this.symm
  refine ⟨hfin, ?_⟩
  rw [hinf]
  exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
    ((hβle x hx).trans (le_max_right _ _)) (norm_nonneg _))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DifferentiableSchwartzTranslate
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem infPart_add (a b : V4 F) : infPartPi (a + b) = infPartPi a + infPartPi b := by
  funext i
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

variable [IsTotallyReal F]

private noncomputable def ell : (Fin 4 → TR.Rinf F) →L[ℝ] (Fin 4 → mixedEmbedding.mixedSpace F) :=
  AddMonoidHom.toRealLinearMap
    { toFun := fun x => infPartPi fun i => TR.sInf F (x i)
      map_zero' := by
        funext i
        simp only [infPartPi, map_zero, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun x y => by
        have : (fun i => TR.sInf F ((x + y) i)) = (fun i => TR.sInf F (x i)) + fun i => TR.sInf F (y i) := by
          funext i
          simp only [Pi.add_apply, map_add (f := _)]
        rw [this, infPart_add] }
    (continuous_pi fun i => (homeomorphMixedSpace F).continuous.comp
      ((TR.continuous_infEq F).comp (continuous_apply i)))

private theorem differentiable_schwartz_translate (v : V4 F) {Φ : V4 F → ℂ} (h : Φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    Differentiable ℝ fun x : Fin 4 → TR.Rinf F => Φ fun i => v i + TR.sInf F (x i) := by
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : ∀ x : Fin 4 → TR.Rinf F, schwartzBruhatTensorPi f g (fun i => v i + TR.sInf F (x i)) =
        f (infPartPi v + ell x) * g (finPartPi v) := by
      intro x
      have h1 : infPartPi (fun i => v i + TR.sInf F (x i)) = infPartPi v + ell x :=
        infPart_add v fun i => TR.sInf F (x i)
      have h2 : finPartPi (fun i => v i + TR.sInf F (x i)) = finPartPi v := by
        funext i
        exact add_zero (v i).2
      simp only [schwartzBruhatTensorPi, h1, h2]
    simp_rw [e]
    exact (f.differentiable.comp ((differentiable_const _).add ell.differentiable)).mul_const _
  | zero => exact differentiable_const _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.sDiff :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Fo.Ops F), SDiff O := by
  intro F _ _ _ O φ v x x' h0 hx
  set G : (Fin 4 → TR.Rinf F) → ℂ := fun y => φ.1 fun i => v i + TR.sInf F (y i) with hG
  have hd : DifferentiableAt ℝ G 0 := differentiable_schwartz_translate v φ.2 0
  have hF : HasFDerivAt G (fderiv ℝ G 0) (x 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have hc : HasDerivAt (fun t => G (x t)) (fderiv ℝ G 0 x') 0 := hF.comp_hasDerivAt 0 hx
  have hb : ∀ i w, fderiv ℝ G 0 (Pi.single i (Pi.single w 1)) = (O.d w i φ).1 v := by
    intro i w
    set e : Fin 4 → TR.Rinf F := Pi.single i (Pi.single w 1) with he
    have hl : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
    have hF0 : HasFDerivAt G (fderiv ℝ G 0) ((0 : ℝ) • e) := by
      rw [zero_smul]
      exact hd.hasFDerivAt
    have h1 := hF0.comp_hasDerivAt (0 : ℝ) hl
    have h2 := O.d_spec w i φ v
    have hfun : (fun t : ℝ => G (t • e)) = fun t : ℝ => φ.1 (v + Pi.single i (Fo.at1 w t)) := by
      funext t
      refine congrArg φ.1 ?_
      funext j
      by_cases hj : j = i
      · subst hj
        have : (t • e) j = Pi.single w t := by
          funext u
          by_cases hu : u = w
          · subst hu
            simp [he]
          · simp [he, hu]
        simp [this, Fo.at1]
      · have : (t • e) j = 0 := by simp [he, hj]
        simp [this, hj]
    exact (HasDerivAt.unique (by simpa [Function.comp_def, hfun] using h1) h2)
  have hs : x' = ∑ i, ∑ w, x' i w • (Pi.single i (Pi.single w 1) : Fin 4 → TR.Rinf F) := by
    funext i w
    have h1 : ∀ c, c ≠ i → (∑ u, x' c u • (Pi.single c (Pi.single u 1) : Fin 4 → TR.Rinf F)) i = 0 := by
      intro c hc
      simp [Finset.sum_apply, Pi.single_eq_of_ne hc.symm]
    have h2 : (∑ u, x' i u • (Pi.single i (Pi.single u 1) : Fin 4 → TR.Rinf F)) i w = x' i w := by
      simp [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun c _ hc => h1 c hc) (by simp), h2]
  have key : fderiv ℝ G 0 x' = ∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v := by
    conv_lhs => rw [hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hb, Complex.real_smul]
  rw [← key]
  exact hc
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OmGrowth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem abs_le_of_continuous_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →+ ℝ) (hf : Continuous f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |f z| ≤ B * ‖z‖ := by
  refine ⟨‖f.toRealLinearMap hf‖, norm_nonneg _, fun z => ?_⟩
  have h := (f.toRealLinearMap hf).le_opNorm z
  simpa using h

private noncomputable def eU {E : Type} [Field E] [NumberField E] (z : InfinitePlace E → ℂ) : (Cinf E)ˣ where
  val := fun w => Complex.exp (z w)
  inv := fun w => Complex.exp (-z w)
  val_inv := by
    funext w
    change Complex.exp (z w) * Complex.exp (-z w) = 1
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by
    funext w
    change Complex.exp (-z w) * Complex.exp (z w) = 1
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

private theorem continuous_eU {E : Type} [Field E] [NumberField E] :
    Continuous (eU (E := E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w)
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w).neg

private theorem eU_add {E : Type} [Field E] [NumberField E] (z z' : InfinitePlace E → ℂ) :
    eU (z + z') = eU z * eU z' := by
  refine Units.ext ?_
  funext w
  change Complex.exp (z w + z' w) = Complex.exp (z w) * Complex.exp (z' w)
  rw [Complex.exp_add]

private theorem eU_log {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) :
    eU (fun w => Complex.log (s.val w)) = s := by
  refine Units.ext ?_
  funext w
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  change Complex.exp (Complex.log (s.val w)) = s.val w
  exact Complex.exp_log h0

private theorem norm_log_le {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) (w : InfinitePlace E) :
    ‖Complex.log (s.val w)‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) + Real.pi := by
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  have h1 : s⁻¹.val w ≠ 0 := right_ne_zero_of_mul_eq_one h
  have p0 : 0 < ‖s.val w‖ := norm_pos_iff.2 h0
  have p1 : 0 < ‖s⁻¹.val w‖ := norm_pos_iff.2 h1
  have hprod : ‖s.val w‖ * ‖s⁻¹.val w‖ = 1 := by rw [← norm_mul, h, norm_one]
  have b0 : ‖s.val w‖ ≤ ‖s.val‖ := norm_le_pi_norm s.val w
  have b1 : ‖s⁻¹.val w‖ ≤ ‖s⁻¹.val‖ := norm_le_pi_norm s⁻¹.val w
  have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
  have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
  have l0 : Real.log ‖s.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p0 (by linarith)
  have l1 : Real.log ‖s⁻¹.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p1 (by linarith)
  have hs : Real.log ‖s.val w‖ + Real.log ‖s⁻¹.val w‖ = 0 := by
    rw [← Real.log_mul p0.ne' p1.ne', hprod, Real.log_one]
  have hre : |(Complex.log (s.val w)).re| ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) := by
    rw [Complex.log_re, abs_le]
    constructor <;> linarith
  have him : |(Complex.log (s.val w)).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

theorem UpperTheory.ConvolutionTheory.R2.Ff.omGrowth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), OmGrowth F E := by
  intro F E _ _ _ _ _ _ _ _D
  have hN : Continuous (fun s : (Cinf E)ˣ => ideleNorm F E (infId E s)) :=
    continuous_ideleNorm.comp (continuous_infId E)
  refine ⟨hN, fun ω hω => ?_⟩
  let c : (Cinf E)ˣ → ℝ := fun s => ‖((ω (ideleNorm F E (infId E s)) : ℂˣ) : ℂ)‖
  have hc : Continuous c := (Units.continuous_val.comp (hω.comp hN)).norm
  have hpos : ∀ s, 0 < c s := fun s => norm_pos_iff.2 (Units.ne_zero _)
  have hmul : ∀ s s', c (s * s') = c s * c s' := by
    intro s s'
    simp only [c, map_mul, Units.val_mul, norm_mul]
  let f : (InfinitePlace E → ℂ) →+ ℝ :=
    { toFun := fun z => Real.log (c (eU z))
      map_zero' := by
        have h1 : eU (0 : InfinitePlace E → ℂ) = 1 := by
          have := eU_add (0 : InfinitePlace E → ℂ) 0
          rw [add_zero] at this
          exact left_eq_mul.1 this
        have h2 : c 1 = 1 := by simp [c]
        change Real.log (c (eU 0)) = 0
        rw [h1, h2, Real.log_one]
      map_add' := fun z z' => by
        change Real.log (c (eU (z + z'))) = Real.log (c (eU z)) + Real.log (c (eU z'))
        rw [eU_add, hmul, Real.log_mul (hpos _).ne' (hpos _).ne'] }
  have hf : Continuous f :=
    (hc.comp continuous_eU).log fun z => (hpos _).ne'
  obtain ⟨B, hB0, hB⟩ := abs_le_of_continuous_add f hf
  refine ⟨Real.exp (B * Real.pi), ⌈B⌉₊, fun s => ?_⟩
  change c s ≤ _
  set H : ℝ := 1 + ‖s.val‖ + ‖s⁻¹.val‖ with hH
  have hH1 : 1 ≤ H := by
    have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
    have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
    linarith
  have hH0 : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg hH1
  let z : InfinitePlace E → ℂ := fun w => Complex.log (s.val w)
  have hz : ‖z‖ ≤ Real.log H + Real.pi :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => norm_log_le s w
  have hfz : f z = Real.log (c s) := by
    change Real.log (c (eU z)) = _
    rw [eU_log]
  have h1 : Real.log (c s) ≤ B * (Real.log H + Real.pi) := by
    rw [← hfz]
    exact (le_abs_self _).trans ((hB z).trans (mul_le_mul_of_nonneg_left hz hB0))
  have h2 : B * (Real.log H + Real.pi) ≤ B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H := by
    have : B * Real.log H ≤ (⌈B⌉₊ : ℝ) * Real.log H :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil B) hL
    linarith
  calc c s = Real.exp (Real.log (c s)) := (Real.exp_log (hpos s)).symm
    _ ≤ Real.exp (B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H) := Real.exp_le_exp.2 (h1.trans h2)
    _ = Real.exp (B * Real.pi) * H ^ ⌈B⌉₊ := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hH0]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActInf
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem cont_coord (τ : E →+* ℂ) : Continuous (coord (E := E) τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using UpperTheory.V.FieldIso.norm_coord_le τ x

private theorem cont_pInfE : Continuous (pInf E) := continuous_pi fun w =>
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    ((continuous_apply w).comp continuous_fst)

private theorem cont_pInfF : Continuous (TR.pInf F) := continuous_pi fun w =>
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
    ((continuous_apply w).comp continuous_fst)

private theorem tau_real (τ : E →+* ℂ) (k : F) :
    τ (algebraMap F E k) =
      ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)) k : ℝ) : ℂ) := by
  have hv := IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)
  rw [InfinitePlace.embedding_of_isReal_apply hv]
  have hr : ComplexEmbedding.conjugate (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding :=
    InfinitePlace.isReal_iff.1 hv
  rcases InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h
  · exact (congrArg (fun f : F →+* ℂ => f k) h).symm
  · have h' : (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = ComplexEmbedding.conjugate (τ.comp (algebraMap F E)) := h
    have h2 : τ.comp (algebraMap F E) = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding := by
      rw [← hr, h']
      exact (star_star _).symm
    exact congrArg (fun f : F →+* ℂ => f k) h2

private theorem pInfF_rat (k : F) (w : InfinitePlace F) :
    TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k := by
  have hw := IsTotallyReal.isReal w
  change (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap F (InfiniteAdeleRing F) k w) = _
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfiniteAdeleRing.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw]
  rfl

private theorem r_am (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (am E a)) = ((TR.pInf F a (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
  have key : (fun x : InfiniteAdeleRing F => coord τ (pInf E (am E ((x, 0) : A F)))) =
      fun x => ((TR.pInf F ((x, 0) : A F) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
    have hc : Continuous fun x : InfiniteAdeleRing F => ((x, 0) : A F) := Continuous.prodMk_left 0
    refine (InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer
      ((cont_coord τ).comp (cont_pInfE.comp (continuous_am.comp hc)))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp (cont_pInfF.comp hc))) (funext fun k => ?_)
    have e1 : pInf E (am E ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F)) = pInf E (am E (rt k)) := rfl
    have e2 : TR.pInf F ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F) = TR.pInf F (rt k) := rfl
    simp only [Function.comp_apply]
    rw [e1, e2, am_rt, pInfF_rat, ← tau_real]
    exact coord_algebraMap τ _
  exact congrFun key a.1

variable (D : Dat F E)

private theorem r_mk (τ : E →+* ℂ) (u t : A F) :
    coord τ (pInf E (D.mkE u t)) = ((TR.pInf F u (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) +
      τ D.θ * ((TR.pInf F t (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
  have e : coord τ (pInf E (rt D.θ)) = τ D.θ := coord_algebraMap τ _
  rw [D.mkE_def, map_add (f := _), map_add (f := _), map_mul, map_mul, r_am, r_am, e, mul_comm]

private theorem conj_θ (τ : E →+* ℂ) : starRingEnd ℂ (τ D.θ) = -τ D.θ := by
  have hv := IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)
  have hc := D.neg (InfinitePlace.embedding_of_isReal hv)
  have hz : τ D.θ ^ 2 = ((InfinitePlace.embedding_of_isReal hv D.δ : ℝ) : ℂ) := by
    rw [← map_pow, D.sq, tau_real]
  generalize τ D.θ = z at hz
  generalize InfinitePlace.embedding_of_isReal hv D.δ = c at hz hc
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  have hre : z.re = 0 := by
    by_contra h
    have h3 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [h3] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

private theorem r_bar (τ : E →+* ℂ) (z : A E) :
    coord τ (pInf E (D.bar z)) = starRingEnd ℂ (coord τ (pInf E z)) := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  rw [D.bar_mkE, r_mk, r_mk, map_add (f := _), map_mul, conj_θ, Complex.conj_ofReal, Complex.conj_ofReal, map_neg, Pi.neg_apply]
  push_cast
  ring

private theorem map_herm (τ : E →+* ℂ) (v : V4 F) :
    (D.herm v).map ((coord τ).comp (pInf E)) =
      Hm (τ D.θ) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) fun i => TR.pInf F (v i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dat.herm, Hm, r_mk, r_am, sub_eq_add_neg]

private theorem fin_part (y : GL (Fin 2) (Cinf E)) (v : V4 F) :
    finPartPi (D.act (infGL E 2 y) v) = finPartPi v := by
  let eF : A F := ((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have heF : eF * eF = eF := Prod.ext (mul_zero _) (mul_one _)
  set e : A E := am E eF with he
  have he2 : e * e = e := by rw [he, ← map_mul, heF]
  have hbar : D.bar e = e := D.bar_am eF
  have hfst : e.1 = 0 := map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  have hsnd : e.2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap F E)
  have hM : e • (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
    ext1 i j
    have h := congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)
    refine Prod.ext ?_ ?_
    · change e.1 * _ = e.1 * _
      rw [hfst, zero_mul, zero_mul]
    · change e.2 * _ = e.2 * _
      rw [hsnd, one_mul, one_mul]
      exact h.trans (by
        change (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = _
        by_cases hij : i = j
        · subst hij; simp <;> rfl
        · simp [Matrix.one_apply_ne hij] <;> rfl)
  have hS : e • D.star2 (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
    have hs : ∀ X : Matrix (Fin 2) (Fin 2) (A E), D.star2 (e • X) = e • D.star2 X := fun X => by
      ext1 i j
      simp [Dat.conjTransposeGal_apply, hbar]
    rw [← hs, hM, hs, Dat.conjTransposeGal_one]
  have L : ∀ X Y : Matrix (Fin 2) (Fin 2) (A E), (e • X) * D.herm v * (e • Y) = e • (X * D.herm v * Y) := fun X Y => by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he2]
  have main : D.act (infGL E 2 y) (eF • v) = eF • v := D.herm_injective (by
    rw [D.herm_act, D.herm_smul]
    calc (infGL E 2 y).val * (am E eF • D.herm v) * D.star2 (infGL E 2 y).val
        = e • ((infGL E 2 y).val * D.herm v * D.star2 (infGL E 2 y).val) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, he]
      _ = (e • (infGL E 2 y).val) * D.herm v * (e • D.star2 (infGL E 2 y).val) := (L _ _).symm
      _ = (e • 1) * D.herm v * (e • 1) := by rw [hM, hS]
      _ = am E eF • D.herm v := by rw [L]; simp [he])
  rw [D.act_smul] at main
  funext i
  have h := congrArg (fun x : V4 F => (x i).2) main
  exact (one_mul _).symm.trans (h.trans (one_mul _))

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.actInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), ActInf D := by
  intro F E _ _ _ _ _ _ _ D y v
  refine ⟨fin_part D y v, fun τ => ?_⟩
  have hy : ((infGL E 2 y).val).map ((coord τ).comp (pInf E)) = y.val.map (coord τ) := by
    ext1 i j
    exact congrArg (coord τ) (congrArg (fun g : GL (Fin 2) (Cinf E) => g.val i j) (pInf_infGL y))
  have hs : (D.star2 (infGL E 2 y).val).map ((coord τ).comp (pInf E)) = (y.val.map (coord τ))ᴴ := by
    rw [← hy]
    ext1 i j
    exact r_bar D τ _
  have h := congrArg (fun X => X.map ((coord τ).comp (pInf E))) (D.herm_act (infGL E 2 y) v)
  simp only [Matrix.map_mul, map_herm, hy, hs] at h
  exact h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.OpsFock
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private lemma infiniteProjection_placeEmbed (w : InfinitePlace F) (t : ℝ) : TR.pInf F (Fo.at1 w t) = Pi.single w t := by
  change (TR.infEq F).symm (TR.infEq F (Pi.single w t)) = _
  exact RingEquiv.symm_apply_apply _ _

private lemma placeEmbedReal_zero (w : InfinitePlace F) : Fo.at1 w 0 = 0 := by
  simp [Fo.at1]

private lemma placeEmbedReal_finitePart (w : InfinitePlace F) (t : ℝ) : (Fo.at1 w t).2 = 0 := rfl

private lemma shift_zero (w : InfinitePlace F) (i : Fin 4) (v : V4 F) :
    v + Pi.single i (Fo.at1 w 0) = v := by
  simp [placeEmbedReal_zero]

private lemma finPart_shift (w : InfinitePlace F) (i : Fin 4) (v : V4 F) (t : ℝ) :
    finPartPi (v + Pi.single i (Fo.at1 w t)) = finPartPi v := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + (Fo.at1 w t).2 = (v j).2
    rw [placeEmbedReal_finitePart, add_zero]
  · simp [finPartPi, Pi.single_eq_of_ne h]

private lemma coord_shift (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ) =
      ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) := by
  by_cases h : j = i
  · subst h
    by_cases h' : w' = w
    · subst h'
      simp [map_add (f := _), infiniteProjection_placeEmbed]
    · simp [map_add (f := _), infiniteProjection_placeEmbed, h', Pi.single_eq_of_ne h']
  · simp [h, Pi.single_eq_of_ne h]

private lemma lin_der (a c : ℂ) : HasDerivAt (fun t : ℝ => a + c * (t : ℂ)) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).const_add a
  simpa using h

private lemma coord_mem (j : Fin 4) (w : InfinitePlace F) :
    (fun v : V4 F => ((TR.pInf F (v j) w : ℝ) : ℂ)) ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) :=
  Algebra.subset_adjoin ⟨j, w, rfl⟩

private lemma poly_der (w : InfinitePlace F) (i : Fin 4) {p : V4 F → ℂ}
    (hp : p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F)) :
    ∃ p' ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v,
      HasDerivAt (fun t : ℝ => p (v + Pi.single i (Fo.at1 w t))) (p' v) 0 := by
  unfold UpperTheory.ConvolutionTheory.R2.polyFn at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, w', rfl⟩ := hx
    refine ⟨algebraMap ℂ _ (if j = i ∧ w' = w then 1 else 0), Subalgebra.algebraMap_mem _ _, fun v => ?_⟩
    have e : (fun t : ℝ => ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ)) =
        fun t : ℝ => ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) :=
      funext fun t => coord_shift w w' i j v t
    rw [e]
    exact lin_der _ _
  | algebraMap r =>
    exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | mul x y hxa hya hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    refine ⟨x' * y + x * y', add_mem (mul_mem hxm hya) (mul_mem hxa hym), fun v => ?_⟩
    have h := (hx v).mul (hy v)
    simp only [shift_zero] at h
    exact h

private noncomputable def Qf (δ : F) (v : V4 F) : ℂ :=
  ((∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ)

private lemma Qf_mem (δ : F) : Qf δ ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) := by
  have e : Qf δ = ∑ w, ((fun v : V4 F => ((TR.pInf F (v 0) w : ℝ) : ℂ)) ^ 2 +
      (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ^ 2 +
      algebraMap ℂ (V4 F → ℂ) 2 * ((fun v : V4 F => ((TR.pInf F (v 2) w : ℝ) : ℂ)) ^ 2 -
        algebraMap ℂ (V4 F → ℂ) ((TR.pInf F (rt δ) w : ℝ) : ℂ) *
          (fun v : V4 F => ((TR.pInf F (v 3) w : ℝ) : ℂ)) ^ 2)) := by
    funext v
    have h2 : ∀ x, TR.pInf F (2 : A F) x = 2 := fun x => by
      rw [map_ofNat]; rfl
    simp [Qf, Finset.sum_apply, map_add (f := _), map_mul, map_sub, map_pow, h2]
  rw [e]
  refine sum_mem fun w _ => ?_
  exact add_mem (add_mem (pow_mem (coord_mem 0 w) 2) (pow_mem (coord_mem 1 w) 2))
    (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (pow_mem (coord_mem 2 w) 2)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (coord_mem 3 w) 2))))

private lemma gauss_der (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    ∃ q ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v, HasDerivAt
      (fun t : ℝ => UpperTheory.ConvolutionTheory.R2.gauss δ (v + Pi.single i (Fo.at1 w t)))
      (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v) 0 := by
  obtain ⟨q, hq, hd⟩ := poly_der w i (Qf_mem δ)
  refine ⟨algebraMap ℂ _ (-(Real.pi : ℂ)) * q, mul_mem (Subalgebra.algebraMap_mem _ _) hq, fun v => ?_⟩
  have h := ((hd v).const_mul (-(Real.pi : ℂ))).cexp
  simp only [shift_zero] at h
  exact h

private def Gen (δ : F) : Set (V4 F → ℂ) :=
  {φ : V4 F → ℂ | ∃ p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v)}

private lemma cw_coord_mul_mem_span_gen_of_mem (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    (fun v => Fo.cw w (v i) * f v) ∈ Submodule.span ℂ (Gen δ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨(fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) * p,
      mul_mem (coord_mem i w) hp, g, hg, ?_⟩
    funext v
    simp [Fo.cw, mul_assoc]
  | zero =>
    have : (fun v : V4 F => Fo.cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v; simp
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun v : V4 F => Fo.cw w (v i) * (x + y) v) =
        (fun v => Fo.cw w (v i) * x v) + fun v => Fo.cw w (v i) * y v := by
      funext v; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : (fun v : V4 F => Fo.cw w (v i) * (c • x) v) = c • fun v => Fo.cw w (v i) * x v := by
      funext v; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hx

private lemma span_d (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    ∃ f' ∈ Submodule.span ℂ (Gen δ), ∀ v,
      HasDerivAt (fun t : ℝ => f (v + Pi.single i (Fo.at1 w t))) (f' v) 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    obtain ⟨p', hp', hdp⟩ := poly_der w i hp
    obtain ⟨q, hq, hdq⟩ := gauss_der δ w i
    refine ⟨fun v => (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v),
      Submodule.subset_span ⟨p' + p * q, add_mem hp' (mul_mem hp hq), g, hg, rfl⟩, fun v => ?_⟩
    have h := ((hdp v).mul (hdq v)).mul_const (g (finPartPi v))
    simp only [shift_zero] at h
    simp only [finPart_shift]
    have e : (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v) =
        (p' v * UpperTheory.ConvolutionTheory.R2.gauss δ v + p v * (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v)) * g (finPartPi v) := by
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [e]
    exact h
  | zero => exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | smul c x _ hx =>
    obtain ⟨x', hxm, hx⟩ := hx
    exact ⟨c • x', Submodule.smul_mem _ _ hxm, fun v => (hx v).const_mul c⟩

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.opsFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), OpsFock D O := by
  intro F E _ _ _ _ _ _ _ D O w i φ hφ
  have hs : φ.1 ∈ Submodule.span ℂ (Gen D.δ) := hφ
  refine ⟨?_, ?_⟩
  · have e : (O.x w i φ).1 = fun v => Fo.cw w (v i) * φ.1 v := funext fun v => O.x_apply w i φ v
    change (O.x w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact cw_coord_mul_mem_span_gen_of_mem D.δ w i hs
  · obtain ⟨f', hf', hd⟩ := span_d D.δ w i hs
    have e : (O.d w i φ).1 = f' := funext fun v => (O.d_spec w i φ v).unique (hd v)
    change (O.d w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact hf'
end
