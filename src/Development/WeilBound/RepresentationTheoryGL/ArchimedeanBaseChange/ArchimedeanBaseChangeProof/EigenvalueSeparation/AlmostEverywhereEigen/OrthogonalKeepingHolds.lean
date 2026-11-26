module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowsex

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Gelf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem gelf : Gelf := by
  intro K _ _ _ B _ _ _ _ R
  let A0 : StarSubalgebra ℂ (K →L[ℂ] K) := R.range
  have hc : ∀ x y : A0, x * y = y * x := by
    rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩
    apply Subtype.ext
    change R b * R c = R c * R b
    rw [← map_mul, ← map_mul, mul_comm]
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := A0.topologicalClosure
  have : IsClosed (A : Set (K →L[ℂ] K)) := A0.isClosed_topologicalClosure
  let cr : CommRing A := A0.commRingTopologicalClosure hc
  let _ : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }
  let G := gelfandStarTransform A
  have hmem : ∀ b, R b ∈ A := fun b => A0.le_topologicalClosure ⟨b, rfl⟩
  refine ⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance,
    A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩
  · intro f
    have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _
    rw [G.apply_symm_apply] at h1
    rw [h1]
    rfl
  · intro b
    change ((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b
    rw [G.symm_apply_apply]

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Desint
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PositivityTheory.Rg.BcB.E2.P

theorem desint : JointRep → Tonelli → WeakAE → EigAE → LocInt → NonZero → Smooth → Desint := by
  intro hJR hTon hWk hEig hLoc hNZ hSm
  intro X ι κ S _ _ _ ν _ _ F W Φ σ g c₀ P hd hW hΦ hσ hc₀ hP
  let _ : MeasurableSpace (Lp ℂ 2 ν) := borel _
  have : BorelSpace (Lp ℂ 2 ν) := ⟨rfl⟩
  obtain ⟨Ψ, hΨm, hΨ⟩ := hJR S ν
  obtain ⟨f, hrep, hinv⟩ : ∃ f : ι → X.G → S → ℂ, (∀ i, IsRep (F i) (f i)) ∧
      ∀ i, ∀ γ ∈ X.Γ, ∀ x s, f i (γ * x) s = f i x s :=
    ⟨fun i x s => Ψ (F i x) s, fun i =>
      ⟨hΨm.comp (((hd.cont i).measurable.comp measurable_fst).prodMk measurable_snd), fun x => hΨ (F i x)⟩,
      fun i γ hγ x s => by simp only [hd.inv i γ hγ x]⟩
  have : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hT : ∀ᵐ s ∂ν, ∀ i, ∫⁻ x, W x * ‖f i x s‖ₑ ^ 2 ∂X.ν < ⊤ :=
    ae_all_iff.2 fun i => hTon X.G S X.ν ν (F i) (f i) W (hrep i) hW (hd.wt i)
  have hE : ∀ᵐ s ∂ν, ∀ c i, ∀ᵐ x ∂X.μ,
      ∑ j, ∫ y, Φ c i j y * conj (f j (x * y) s) ∂X.μ = σ c s * conj (f i x s) :=
    ae_all_iff.2 fun c => hEig X ι S ν F f (Φ c) (σ c) (hσ c).2.choose hd.cont hrep (hΦ c) (hσ c).1
      (hσ c).2.choose_spec (hd.eig c)
  have hL : ∀ᵐ s ∂ν, ∀ i, LocallyIntegrable (fun x => f i x s) X.μ :=
    ae_all_iff.2 fun i => hLoc X S ν (F i) (f i) (hd.cont i) (hrep i)
  have hO : ∀ᵐ s ∂ν, ∀ n, ∑ i, ∫ x, g n i x * conj (f i x s) ∂X.ν = 0 :=
    ae_all_iff.2 fun n => hWk X.G S ι X.ν ν F f (g n) 0 hrep (fun i => (hd.gint n i).1)
      (fun i => (hd.gint n i).2) MemLp.zero (fun h => by rw [hd.orth n h]; simp)
  have hN : ¬ ∀ᵐ s ∂ν, ∀ i, ∀ᵐ x ∂X.μ, f i x s = 0 := by
    intro h
    apply hd.ne
    funext i
    exact hNZ X S ν (F i) (f i) (hd.cont i) (hrep i) (h.mono fun s hs => hs i)
  obtain ⟨s, hsN, hsP, hs0, hsT, hsE, hsL, hsO⟩ :=
    ((not_eventually.1 hN).and_eventually (hP.and (hc₀.and (hT.and (hE.and (hL.and hO)))))).exists
  have huL : ∀ i, LocallyIntegrable (fun x => conj (f i x s)) X.μ := fun i =>
    (hsL i).mono (Complex.continuous_conj.comp_aestronglyMeasurable (hsL i).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simp)
  obtain ⟨f', hf', heig⟩ := hSm X ι κ (fun i x => conj (f i x s)) Φ (fun c => σ c s) c₀ huL
    (fun i γ hγ x => by simp only [hinv i γ hγ x s]) hΦ hs0 hsE
  have hae : ∀ i, f' i =ᵐ[X.ν] fun x => conj (f i x s) := fun i => by
    unfold Ctx.ν; exact ae_restrict_of_ae (hf' i).2.1
  refine ⟨s, hsP, f', ⟨fun i => (hf' i).1, ?_, fun i => (hf' i).2.2, fun i => ?_, heig, fun n => ?_⟩⟩
  · intro h0
    apply hsN
    intro i
    filter_upwards [(hf' i).2.1] with x hx
    simp only [h0, Pi.zero_apply] at hx
    simpa using hx.symm
  · rw [lintegral_congr_ae (g := fun x => W x * ‖f i x s‖ₑ ^ 2)
      ((hae i).mono fun x hx => by simp only [hx, RCLike.enorm_conj])]
    exact hsT i
  · rw [← hsO n]
    refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
    filter_upwards [hae i] with x hx
    rw [hx]

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Eigae
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem eigae : WeakAE → EigAE := by
  intro hW X ι S _ _ ν _ F f Φ σ A hFc hrep hΦ hσ hσA hE
  have hfm : ∀ j, Measurable (Function.uncurry (f j)) := fun j => (hrep j).1
  have hfx : ∀ j x, Measurable (f j x) := fun j x => (hfm j).comp measurable_prodMk_left
  have key : ∀ i x, ∀ᵐ s ∂ν, ∑ j, ∫ y, Φ i j y * conj (f j (x * y) s) ∂X.μ = σ s * conj (f i x s) := by
    intro i x
    refine hW X.G S ι X.μ ν (fun j y => F j (x * y)) (fun j y => f j (x * y)) (fun j => Φ i j)
      (fun s => σ s * conj (f i x s)) (fun j => ⟨?_, fun y => (hrep j).2 (x * y)⟩)
      (fun j => (hΦ i j).1.aestronglyMeasurable) (fun j => ?_) ?_ (fun h => ?_)
    · exact (hfm j).comp ((measurable_const_mul x).prodMap measurable_id)
    · have hc : Continuous fun y => Φ i j y • F j (x * y) :=
        (hΦ i j).1.smul ((hFc j).comp (continuous_const.mul continuous_id))
      have hi := (hc.integrable_of_hasCompactSupport (μ := X.μ) ((hΦ i j).2.smul_right)).2
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hi)
      refine lintegral_congr fun y => ?_
      simp [enorm_smul]
    · have hm : MemLp (f i x) 2 ν := (Lp.memLp (F i x)).ae_eq ((hrep i).2 x).symm
      refine MemLp.of_le_mul (c := A) hm ?_ (ae_of_all _ fun s => ?_)
      · exact (hσ.mul (Complex.continuous_conj.measurable.comp (hfx i x))).aestronglyMeasurable
      · simp only [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hσA s) (norm_nonneg _)
    · rw [hE x i h]
      refine integral_congr_ae ?_
      filter_upwards [(hrep i).2 x] with s hs
      simp [hs]
  refine ae_all_iff.2 fun i => ?_
  have hmeas : MeasurableSet {p : X.G × S |
      ∑ j, ∫ y, Φ i j y * conj (f j (p.1 * y) p.2) ∂X.μ = σ p.2 * conj (f i p.1 p.2)} := by
    refine measurableSet_eq_fun ?_ ?_
    · refine Finset.measurable_sum _ fun j _ => ?_
      have : StronglyMeasurable fun q : (X.G × S) × X.G => Φ i j q.2 * conj (f j (q.1.1 * q.2) q.1.2) := by
        refine Measurable.stronglyMeasurable ?_
        refine ((hΦ i j).1.measurable.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp ?_)
        exact (hfm j).comp ((measurable_fst.fst.mul measurable_snd).prodMk measurable_fst.snd)
      exact (this.integral_prod_right' (ν := X.μ)).measurable
    · exact (hσ.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp (hfm i))
  exact (Measure.ae_ae_comm hmeas).1 (ae_of_all _ fun x => key i x)

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Specmeas
noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder CompactlySupported
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P.Specmeas

variable {X : Type} [TopologicalSpace X]

def ofR (g : C(X, ℝ)) : C(X, ℂ) := ⟨fun x => (g x : ℂ), by fun_prop⟩

@[simp] lemma ofR_apply (g : C(X, ℝ)) (x : X) : ofR g x = (g x : ℂ) := rfl

lemma ofR_add (g h : C(X, ℝ)) : ofR (g + h) = ofR g + ofR h := by
  ext x; simp

lemma ofR_sub (g h : C(X, ℝ)) : ofR (g - h) = ofR g - ofR h := by
  ext x; simp

lemma ofR_smul (c : ℝ) (g : C(X, ℝ)) : ofR (c • g) = (c : ℂ) • ofR g := by
  ext x; simp

def reC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).re, by fun_prop⟩
def imC (f : C(X, ℂ)) : C(X, ℝ) := ⟨fun x => (f x).im, by fun_prop⟩

lemma eq_ofR_re_add_im (f : C(X, ℂ)) : f = ofR (reC f) + Complex.I • ofR (imC f) := by
  ext x
  simp [reC, imC, mul_comm Complex.I, Complex.re_add_im]

section
variable (Λ : C(X, ℂ) →ₗ[ℂ] ℂ) (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f))
include hΛ

lemma nonneg_ofR {g : C(X, ℝ)} (hg : ∀ x, 0 ≤ g x) : 0 ≤ Λ (ofR g) := by
  let s : C(X, ℝ) := ⟨fun x => Real.sqrt (g x), by fun_prop⟩
  have : ofR g = star (ofR s) * ofR s := by
    ext x
    simp only [ofR_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply, s,
      ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]
  rw [this]; exact hΛ _

lemma im_ofR (g : C(X, ℝ)) : (Λ (ofR g)).im = 0 := by
  let p : C(X, ℝ) := ⟨fun x => max (g x) 0, by fun_prop⟩
  let n : C(X, ℝ) := ⟨fun x => max (-g x) 0, by fun_prop⟩
  have hg : g = p - n := by
    ext x
    simp only [p, n, ContinuousMap.sub_apply, ContinuousMap.coe_mk]
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hp := nonneg_ofR Λ hΛ (g := p) (fun x => le_max_right _ _)
  have hn := nonneg_ofR Λ hΛ (g := n) (fun x => le_max_right _ _)
  rw [Complex.le_def] at hp hn
  rw [hg, ofR_sub, map_sub, Complex.sub_im, ← hp.2, ← hn.2]; simp

lemma ofR_eq_re (g : C(X, ℝ)) : Λ (ofR g) = ((Λ (ofR g)).re : ℂ) := by
  apply Complex.ext <;> simp [im_ofR Λ hΛ g]

end

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

theorem exists_measure_of_positive (Λ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ f : C(X, ℂ), 0 ≤ Λ (star f * f)) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ.Regular ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ := by
  let Λr : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  { toFun g := (Λ (ofR g.toContinuousMap)).re
    map_add' g g' := by
      have : (g + g').toContinuousMap = g.toContinuousMap + g'.toContinuousMap := rfl
      rw [this, ofR_add, map_add (f := _), Complex.add_re]
    map_smul' c g := by
      have : (c • g).toContinuousMap = c • g.toContinuousMap := rfl
      rw [this, ofR_smul, map_smul]; simp
    monotone' g g' hgg' := by
      have h := nonneg_ofR Λ hΛ (g := g'.toContinuousMap - g.toContinuousMap)
        (fun x => sub_nonneg.2 (hgg' x))
      rw [ofR_sub, map_sub, Complex.le_def] at h
      have := h.1
      simp only [Complex.zero_re, Complex.sub_re] at this
      linarith }
  refine ⟨RealRMK.rieszMeasure Λr, inferInstance, inferInstance, fun f => ?_⟩
  have key : ∀ g : C(X, ℝ), Λ (ofR g) = ((∫ x, g x ∂(RealRMK.rieszMeasure Λr) : ℝ) : ℂ) := by
    intro g
    have := RealRMK.integral_rieszMeasure Λr (CompactlySupportedContinuousMap.continuousMapEquiv g)
    rw [ofR_eq_re Λ hΛ g]
    congr 1
    exact this.symm
  have hint : Integrable (fun x => f x) (RealRMK.rieszMeasure Λr) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  conv_lhs => rw [eq_ofR_re_add_im f]
  rw [map_add (f := _), map_smul, key, key, ← integral_re_add_im hint, smul_eq_mul, mul_comm]
  rfl

end PositivityTheory.Rg.BcB.E2.P.Specmeas

namespace PositivityTheory.Rg.BcB.E2.P

theorem specmeas : SpecMeas := by
  intro K _ _ _ S _ _ _ _ _ π v
  let Λ : C(S, ℂ) →ₗ[ℂ] ℂ :=
  { toFun f := inner ℂ v (π f v)
    map_add' f g := by simp [map_add (f := _)]
    map_smul' c f := by simp }
  have hΛ : ∀ f : C(S, ℂ), 0 ≤ Λ (star f * f) := by
    intro f
    show 0 ≤ inner ℂ v (π (star f * f) v)
    rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    exact pow_nonneg (Complex.zero_le_real.mpr (norm_nonneg (π f v))) 2
  obtain ⟨ν, h1, h2, h3⟩ := Specmeas.exists_measure_of_positive Λ hΛ
  exact ⟨ν, h1, h2, fun f => (h3 f).symm⟩

end PositivityTheory.Rg.BcB.E2.P

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowseig
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem rowseig : AeEq → Unfold → RowsEig := by
  intro hAe hUn X ι _ Φ T T₁ k u u' hΦ hT hk heq x i
  have wc : ∀ j, Continuous fun y => inner ℂ (k j y) u := fun j => (hk.cont j).inner continuous_const
  have winv : ∀ j, ∀ γ ∈ X.Γ, ∀ y, (fun y => inner ℂ (k j y) u) (γ * y) = (fun y => inner ℂ (k j y) u) y :=
    fun j γ hγ y => by simp only [hk.inv j γ hγ y]
  have hLc : Continuous fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ :=
    continuous_finsetSum _ fun j _ => (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).2
  have hRc : Continuous fun x => inner ℂ (k i x) u' := (hk.cont i).inner continuous_const
  have hLinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) (γ * x)
      = (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc, hk.inv j γ hγ]
  have hRinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => inner ℂ (k i x) u') (γ * x) = (fun x => inner ℂ (k i x) u') x :=
    fun γ hγ x => by simp only [hk.inv i γ hγ x]
  have h3 : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ)
      = fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (T₁ u j : X.G → ℂ) y ∂X.ν := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).1 x
    refine e1.symm.trans (integral_congr_ae ((hk.rep u j).mono fun y hy => ?_))
    simp only [hy]
  have hae : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) =ᵐ[X.ν]
      fun x => inner ℂ (k i x) u' := by
    rw [h3]
    have h1 := hT (T₁ u) i
    rw [heq] at h1
    exact h1.symm.trans (hk.rep u' i)
  exact congrFun (hAe X _ _ hLc hRc hLinv hRinv hae) x

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Convcont
open MeasureTheory Topology
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Convcont

theorem shift (X : Ctx) (φ u : X.G → ℂ) (x : X.G) :
    ∫ y, φ y * u (x * y) ∂X.μ = ∫ z, φ (x⁻¹ * z) * u z ∂X.μ := by
  have := integral_mul_left_eq_self (μ := X.μ) (fun z => φ (x⁻¹ * z) * u z) x
  simp only [inv_mul_cancel_left] at this
  exact this

end Convcont

open Convcont in
theorem convcont : ConvCont := by
  intro X φ u hφ hu
  have hfun : (fun x => ∫ y, φ y * u (x * y) ∂X.μ) = fun x => ∫ z, φ (x⁻¹ * z) * u z ∂X.μ :=
    funext fun x => shift X φ u x
  rw [hfun]
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  have hK : IsCompact (N * tsupport φ) := hNc.mul hφ.2
  have hcx : ∀ z : X.G, Continuous fun x : X.G => φ (x⁻¹ * z) :=
    fun z => hφ.1.comp (continuous_inv.mul continuous_const)
  refine continuousAt_of_dominated (bound := (N * tsupport φ).indicator fun z => B * ‖u z‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hu.aestronglyMeasurable
  · filter_upwards [hN] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ N * tsupport φ
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      have h0 : φ (x⁻¹ * z) = 0 := by
        by_contra h
        apply hz
        refine ⟨x, hx, x⁻¹ * z, subset_tsupport _ h, ?_⟩
        simp
      simp [h0]
  · rw [integrable_indicator_iff hK.measurableSet]
    exact ((hu.integrableOn_isCompact hK).norm.const_mul B)
  · exact Filter.Eventually.of_forall fun z => ((hcx z).mul continuous_const).continuousAt

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Smooth
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem smooth : ConvCont → Smooth := by
  classical
  intro hconv X ι κ _ u Φ lam c₀ hu hinv hΦ hlam heq
  set f : ι → X.G → ℂ := fun i x => (lam c₀)⁻¹ * ∑ j, ∫ y, Φ c₀ i j y * u j (x * y) ∂X.μ with hf
  have hcont : ∀ i, Continuous (f i) := fun i =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c₀ i j) (hu j))
  have hae : ∀ i, f i =ᵐ[X.μ] u i := fun i => (heq c₀ i).mono fun x hx => by
    simp only [hf]
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  refine ⟨f, fun i => ⟨hcont i, hae i, fun γ hγ x => ?_⟩, fun c i x => ?_⟩
  · simp only [hf]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext y
    rw [mul_assoc, hinv j γ hγ]
  · have hconv' : ∀ x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ := by
      intro x
      refine Finset.sum_congr rfl fun j _ => ?_
      refine integral_congr_ae ?_
      have h1 := (measurePreserving_mul_left X.μ x).quasiMeasurePreserving.ae_eq_comp (hae j)
      filter_upwards [h1] with y hy
      simp only [Function.comp] at hy
      rw [hy]
    have hc1 : Continuous fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ :=
      continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c i j) (hu j)
    have hc2 : Continuous fun x => lam c * f i x := continuous_const.mul (hcont i)
    have hae2 : (fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ) =ᵐ[X.μ] fun x => lam c * f i x := by
      filter_upwards [heq c i, hae i] with x h1 h2
      rw [h1, h2]
    have := (Continuous.ae_eq_iff_eq X.μ hc1 hc2).1 hae2
    rw [hconv' x]
    exact congrFun this x

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Jointrep
open MeasureTheory Filter Topology
open scoped ENNReal

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Jointrep

theorem geom : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ j) ^ 2) ≠ ⊤ := by
  have h2 : (∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  refine ne_top_of_le_ne_top h2 (ENNReal.tsum_le_tsum fun j => ?_)
  exact pow_le_of_le_one (by simp) (pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 one_le_two)) two_ne_zero

theorem ae_tendsto {S : Type} [MeasurableSpace S] {ν : Measure S} (h : Lp ℂ 2 ν) (v : ℕ → Lp ℂ 2 ν)
    (hv : ∀ j, edist h (v j) < (2⁻¹ : ℝ≥0∞) ^ j) :
    ∀ᵐ s ∂ν, Tendsto (fun j => (v j : S → ℂ) s) atTop (𝓝 (h s)) := by
  let g : ℕ → S → ℝ≥0∞ := fun j s => ‖(v j : S → ℂ) s - h s‖ₑ ^ (2:ℝ)
  have gm : ∀ j, Measurable (g j) := fun j =>
    (((Lp.stronglyMeasurable (v j)).measurable.sub (Lp.stronglyMeasurable h).measurable).enorm).pow_const _
  have hint : ∀ j, ∫⁻ s, g j s ∂ν ≤ ((2⁻¹ : ℝ≥0∞) ^ j) ^ 2 := by
    intro j
    have e1 : ∫⁻ s, g j s ∂ν = eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν ^ (2:ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' two_pos
    have e2 : eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν = edist (v j) h := by
      rw [Lp.edist_def, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      · rfl
      · exact (Lp.stronglyMeasurable (v j)).aestronglyMeasurable.sub (Lp.stronglyMeasurable h).aestronglyMeasurable
    rw [e1, e2, ENNReal.rpow_two]
    gcongr
    rw [edist_comm]; exact (hv j).le
  have hsum : ∫⁻ s, ∑' j, g j s ∂ν ≠ ⊤ := by
    rw [lintegral_tsum fun j => (gm j).aemeasurable]
    exact ne_top_of_le_ne_top geom (ENNReal.tsum_le_tsum hint)
  filter_upwards [ae_lt_top (Measurable.tsum gm) hsum] with s hs
  have h0 : Tendsto (fun j => g j s) atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne
  have h1 : Tendsto (fun j => (g j s) ^ (2⁻¹ : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (2⁻¹:ℝ))).tendsto 0).comp h0
    simpa [Function.comp_def] using this
  rw [tendsto_iff_edist_tendsto_0]
  refine h1.congr fun j => ?_
  simp only [g, edist_eq_enorm_sub]
  rw [← ENNReal.rpow_mul]
  norm_num

end Jointrep

open Jointrep in
theorem jointrep : JointRep := by
  classical
  intro S _ ν _ _ _
  set u := TopologicalSpace.denseSeq (Lp ℂ 2 ν) with hu
  have hex : ∀ (j : ℕ) (h : Lp ℂ 2 ν), ∃ n, edist h (u n) < (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j h
    obtain ⟨y, ⟨n, rfl⟩, hy⟩ := EMetric.mem_closure_iff.1
      (TopologicalSpace.denseRange_denseSeq (Lp ℂ 2 ν) h) _
      (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp : (2 : ℝ≥0∞) ≠ ⊤)) j)
    exact ⟨n, hy⟩
  let N : ℕ → Lp ℂ 2 ν → ℕ := fun j h => Nat.find (hex j h)
  have hN : ∀ j, Measurable (N j) := fun j =>
    measurable_find (hex j) fun n => Metric.isOpen_eball.measurableSet
  refine ⟨fun h s => limUnder atTop (fun j => (u (N j h) : S → ℂ) s), ?_, fun h => ?_⟩
  · have hf : ∀ j, StronglyMeasurable (fun p : Lp ℂ 2 ν × S => (u (N j p.1) : S → ℂ) p.2) := by
      intro j
      have m : Measurable (fun q : S × ℕ => (u q.2 : S → ℂ) q.1) :=
        measurable_from_prod_countable_left fun n => (Lp.stronglyMeasurable (u n)).measurable
      exact (m.comp (measurable_snd.prodMk ((hN j).comp measurable_fst))).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hf).measurable
  · filter_upwards [ae_tendsto h (fun j => u (N j h)) fun j => Nat.find_spec (hex j h)] with s hs
    exact hs.limUnder_eq

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Speciso
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace PositivityTheory.Rg.BcB.E2.P

namespace Speciso

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {S : Type}
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]

def Lmap (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) : C(S, ℂ) →ₗ[ℂ] K where
  toFun f := π f v
  map_add' f g := by simp
  map_smul' c f := by simp

lemma inner_L (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    inner ℂ (π f v) (π f v) =
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : inner ℂ (π f v) (π f v) = ∫ s, (star f * f) s ∂ν := by
    rw [hν, map_mul, map_star, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [h1]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) f] with s hs
  rw [hs]
  simp [Complex.conj_mul']

lemma norm_L (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    ‖Lmap π v f‖ = ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ f‖ := by
  have h := congrArg RCLike.re (inner_L π v ν hν f)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end Speciso

open Speciso in
theorem speciso : SpecIso := by
  intro K _ _ _ S _ _ _ _ _ π v ν _ _ hν
  set e : C(S, ℂ) →L[ℂ] Lp ℂ 2 ν := ContinuousMap.toLp (E := ℂ) 2 ν ℂ with he
  have hd : DenseRange e := ContinuousMap.toLp_denseRange ℂ ν ℂ (p := 2) (by simp)
  have hcoe : ∀ g, (e g : S → ℂ) =ᵐ[ν] g := fun g =>
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) g
  have hn : ∀ f, ‖Lmap π v f‖ = ‖e.toLinearMap f‖ := fun f => norm_L π v ν hν f
  have hb : ∃ C, ∀ f, ‖Lmap π v f‖ ≤ C * ‖e.toLinearMap f‖ := ⟨1, fun f => by rw [hn, one_mul]⟩
  have hdl : DenseRange e.toLinearMap := hd
  let V : Lp ℂ 2 ν →L[ℂ] K := (Lmap π v).extendOfNorm e.toLinearMap
  have hVe : ∀ f, V (e f) = π f v := fun f => LinearMap.extendOfNorm_eq hdl hb f
  refine ⟨V, fun h => ?_, fun f h h' hh' => ?_⟩
  · refine hd.induction_on (p := fun h => ‖V h‖ = ‖h‖) h
      (isClosed_eq (continuous_norm.comp V.continuous) continuous_norm) ?_
    intro g
    show ‖V (e g)‖ = ‖e g‖
    rw [hVe]
    exact hn g
  · let F : Lp ℂ ∞ ν := ContinuousMap.toLp (E := ℂ) ∞ ν ℂ f
    have hF : (F : S → ℂ) =ᵐ[ν] f := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (μ := ν) f
    let M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 F
    have hM : ∀ g, (M g : S → ℂ) =ᵐ[ν] fun s => f s * g s := by
      intro g
      have h1 : (M g : S → ℂ) =ᵐ[ν] fun s => (ContinuousLinearMap.mul ℂ ℂ) (F s) (g s) :=
        (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) F g
      filter_upwards [h1, hF] with s hs hFs
      rw [hs, ContinuousLinearMap.mul_apply', hFs]
    have key : ∀ g, V (M g) = π f (V g) := by
      intro g
      refine hd.induction_on (p := fun g => V (M g) = π f (V g)) g
        (isClosed_eq (V.continuous.comp M.continuous) ((π f).continuous.comp V.continuous)) ?_
      intro g
      have : M (e g) = e (f * g) := by
        apply Lp.ext
        filter_upwards [hM (e g), hcoe g, hcoe (f * g)] with s h1 h2 h3
        rw [h1, h2, h3]
        rfl
      show V (M (e g)) = π f (V (e g))
      rw [this, hVe, hVe, map_mul, ContinuousLinearMap.mul_apply]
    have : h' = M h := by
      apply Lp.ext
      filter_upwards [hh', hM h] with s h1 h2
      rw [h1, h2]
    rw [this, key]

end PositivityTheory.Rg.BcB.E2.P
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.AeZero
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

namespace PositivityTheory.Rg.BcB.E2.P.Spec

theorem ae_zero {S : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] [ν.Regular] (u : S → ℝ) (hu : Continuous u) (h0 : ∀ s, 0 ≤ u s)
    (hi : ∫ s, (u s : ℂ) ∂ν = 0) : ∀ᵐ s ∂ν, u s = 0 := by
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hi
  have hint : Integrable u ν := integrableOn_univ.1 (hu.continuousOn.integrableOn_compact isCompact_univ)
  exact (integral_eq_zero_iff_of_nonneg (fun s => h0 s) hint).1 hi

end PositivityTheory.Rg.BcB.E2.P.Spec

namespace PositivityTheory.Rg.BcB.E2.P

open PositivityTheory.Rg.BcB.E2.P.Spec in
theorem spec : Gelf → Point → SpecMeas → SpecIso → Spec := by
  classical
  intro hG hP hM hI K _ _ _ B _ _ _ _ R p C₀ ε hp hε
  obtain ⟨S, _, _, _, π, e, hπ, he⟩ := hG K B R
  have hne : ∀ b, ‖e b‖ = ‖R b‖ := fun b => by rw [← hπ, he]
  obtain ⟨s₀, hs₀⟩ := hP B S e p fun b => (hp b).trans (hne b).ge
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩

  let gr : S → ℝ := fun s => max 0 (1 - (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖)
  have hgr : Continuous gr := by
    refine continuous_const.max (continuous_const.sub (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun c _ => continuous_norm.comp ((e c).continuous.sub continuous_const)
  let g : C(S, ℂ) := ⟨fun s => (gr s : ℂ), Complex.continuous_ofReal.comp hgr⟩
  have hg0 : g s₀ = 1 := by
    simp [g, gr, hs₀]
  have hgne : π g ≠ 0 := by
    intro h
    have h1 : ‖g‖ = 0 := by rw [← hπ, h, norm_zero]
    have h2 := ContinuousMap.norm_coe_le_norm g s₀
    rw [hg0, h1] at h2
    norm_num at h2
  obtain ⟨v, hv⟩ : ∃ v, π g v ≠ 0 := by
    by_contra h
    push Not at h
    exact hgne (ContinuousLinearMap.ext h)
  set w := π g v with hw
  obtain ⟨ν, hνf, hνr, hν⟩ := hM K S π w
  obtain ⟨V, hViso, hVmul⟩ := hI K S π w ν hν
  let χ : S → (B →⋆ₐ[ℂ] ℂ) := fun s => (ContinuousMap.evalStarAlgHom ℂ ℂ s).comp e
  have hχ : ∀ s b, χ s b = e b s := fun s b => rfl
  refine ⟨S, borel S, ν, hνf, χ, V, ⟨?_, ?_, ?_, hViso, ?_⟩, ?_⟩
  · intro h0
    have h1 := hν 1
    rw [h0, integral_zero_measure, map_one, ContinuousLinearMap.one_apply] at h1
    exact hv (inner_self_eq_zero.1 h1.symm)
  · intro b
    simp only [hχ]
    exact (e b).continuous.measurable
  · intro b s
    rw [hχ, ← hne]
    exact ContinuousMap.norm_coe_le_norm _ _
  · intro b h h' hh
    rw [← he]
    exact hVmul (e b) h h' (by simpa only [hχ] using hh)
  · rw [Filter.eventually_all_finset]
    intro c hc
    let tr : S → ℝ := fun s => max 0 (‖e c s - p c‖ - ε)
    have htr : Continuous tr :=
      continuous_const.max ((continuous_norm.comp ((e c).continuous.sub continuous_const)).sub continuous_const)
    let t : C(S, ℂ) := ⟨fun s => (tr s : ℂ), Complex.continuous_ofReal.comp htr⟩
    have htg : t * g = 0 := by
      ext s
      simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply, t, g, ContinuousMap.coe_mk]
      rcases le_or_gt (‖e c s - p c‖) ε with h | h
      · have : tr s = 0 := max_eq_left (by linarith)
        simp [this]
      · have hs : ‖e c s - p c‖ ≤ ∑ c ∈ C₀, ‖e c s - p c‖ :=
          Finset.single_le_sum (f := fun c => ‖e c s - p c‖) (fun _ _ => norm_nonneg _) hc
        have h2 : 2 < (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖ := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hε]
          nlinarith
        have : gr s = 0 := max_eq_left (by linarith)
        simp [this]
    have hint : ∫ s, (tr s : ℂ) ∂ν = 0 := by
      have h1 := hν t
      have h2 : π t w = 0 := by
        rw [hw, ← ContinuousLinearMap.mul_apply, ← map_mul, htg, map_zero, ContinuousLinearMap.zero_apply]
      rw [h2, inner_zero_right] at h1
      exact h1
    filter_upwards [ae_zero ν tr htr (fun s => le_max_left _ _) hint] with s hs
    rw [hχ]
    have : ‖e c s - p c‖ - ε ≤ 0 := max_eq_left_iff.1 hs
    linarith

end PositivityTheory.Rg.BcB.E2.P

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Nonzero
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem nonzero : NonZero := by
  intro X S _ ν _ F f hF hf h0
  have hmeas : MeasurableSet {p : X.G × S | f p.1 p.2 = 0} :=
    (measurableSet_singleton (0 : ℂ)).preimage hf.1
  have h1 : ∀ᵐ x ∂X.μ, ∀ᵐ s ∂ν, f x s = 0 :=
    (Measure.ae_ae_comm (μ := X.μ) (ν := ν) (p := fun x s => f x s = 0) hmeas).2 h0
  have h2 : F =ᵐ[X.μ] (0 : X.G → Lp ℂ 2 ν) := by
    filter_upwards [h1] with x hx
    have : (F x : S → ℂ) =ᵐ[ν] 0 := by
      filter_upwards [(hf.2 x).symm, hx, Lp.coeFn_zero ℂ 2 ν] with s h1 h2 h3
      rw [h1, h2]; rfl
    simpa using (Lp.eq_zero_iff_ae_eq_zero).2 this
  exact (Continuous.ae_eq_iff_eq X.μ hF continuous_const).1 h2

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Hssep
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory

theorem hssep : HsSep := by
  intro X ι _
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  haveI : IsSeparable X.ν := inferInstance
  haveI : SecondCountableTopology (Lp ℂ 2 X.ν) := inferInstance
  infer_instance

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Weakae
open MeasureTheory
open scoped ENNReal ComplexConjugate

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Weakae

variable {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S]

theorem lint_slice (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F) :
    ∫⁻ s, ‖f s‖ₑ ∂ν ≤ ‖F‖ₑ * ν Set.univ ^ (1 / 2 : ℝ) := by
  rw [← eLpNorm_one_eq_lintegral_eNorm ((Lp.aestronglyMeasurable F).congr hf.symm),
    eLpNorm_congr_ae hf, Lp.enorm_def]
  have := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (μ := ν) (f := (F : S → ℂ))
    (by norm_num) (Lp.aestronglyMeasurable F)
  convert this using 3
  norm_num

theorem integrable_k (m : Measure Y) [SFinite m] (ν : Measure S) [IsFiniteMeasure ν]
    (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) (c : Y → ℂ) (hf : IsRep F f) (hc : AEStronglyMeasurable c m)
    (hint : ∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m ≠ ⊤) :
    Integrable (fun p : Y × S => c p.1 * conj (f p.1 p.2)) (m.prod ν) := by
  have hcm : AEStronglyMeasurable (fun p : Y × S => c p.1) (m.prod ν) := hc.comp_fst
  have hfm : AEStronglyMeasurable (fun p : Y × S => conj (f p.1 p.2)) (m.prod ν) :=
    (Complex.continuous_conj.measurable.comp hf.1).aestronglyMeasurable
  refine ⟨hcm.mul hfm, ?_⟩
  show ∫⁻ p, ‖c p.1 * conj (f p.1 p.2)‖ₑ ∂(m.prod ν) < ⊤
  have hm : AEMeasurable (fun p : Y × S => ‖c p.1 * conj (f p.1 p.2)‖ₑ) (m.prod ν) :=
    (hcm.mul hfm).enorm
  rw [lintegral_prod _ hm]
  have hC : ν Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top ν _)
  calc ∫⁻ y, ∫⁻ s, ‖c (y, s).1 * conj (f (y, s).1 (y, s).2)‖ₑ ∂ν ∂m
      = ∫⁻ y, ‖c y‖ₑ * ∫⁻ s, ‖f y s‖ₑ ∂ν ∂m := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun s => ?_
        simp [enorm_mul]
    _ ≤ ∫⁻ y, ‖c y‖ₑ * (‖F y‖ₑ * ν Set.univ ^ (1 / 2 : ℝ)) ∂m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact lint_slice ν (F y) (f y) (hf.2 y)
    _ = (∫⁻ y, ‖c y‖ₑ * ‖F y‖ₑ ∂m) * ν Set.univ ^ (1 / 2 : ℝ) := by
        simp_rw [← mul_assoc]
        exact lintegral_mul_const' _ _ hC
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hint) (lt_top_iff_ne_top.2 hC)

theorem inner_ind (ν : Measure S) [IsFiniteMeasure ν] (F : Lp ℂ 2 ν) (f : S → ℂ) (hf : f =ᵐ[ν] F)
    (A : Set S) (hA : MeasurableSet A) (hνA : ν A ≠ ⊤) :
    inner ℂ F (indicatorConstLp 2 hA hνA (1 : ℂ)) = ∫ s in A, conj (f s) ∂ν := by
  rw [← inner_conj_symm, L2.inner_indicatorConstLp_one, integral_conj]
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (hf.mono fun s hs => hs.symm))

end Weakae

open Weakae in
theorem weakae : WeakAE := by
  intro Y S ι _ _ _ m _ ν _ F f c q hf hc hint hq hw
  classical
  have hki : ∀ j, Integrable (fun p : Y × S => c j p.1 * conj (f j p.1 p.2)) (m.prod ν) := fun j =>
    integrable_k m ν (F j) (f j) (c j) (hf j) (hc j) (hint j)
  have hGj : ∀ j, Integrable (fun s => ∫ y, c j y * conj (f j y s) ∂m) ν := fun j =>
    (hki j).integral_prod_right
  have hG : Integrable (fun s => ∑ j, ∫ y, c j y * conj (f j y s) ∂m) ν :=
    integrable_finsetSum _ fun j _ => hGj j
  have hq' : Integrable q ν := hq.integrable (by norm_num)
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hG hq' fun A hA hνA => ?_
  have hR : ∫ s, q s * (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) s ∂ν = ∫ s in A, q s ∂ν := by
    rw [← integral_indicator hA]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hνA.ne) (c := (1 : ℂ))] with s hs
    rw [hs]
    by_cases h : s ∈ A <;> simp [h]
  rw [← hR, ← hw, integral_finsetSum _ fun j _ => (hGj j).integrableOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hres : m.prod (ν.restrict A) = (m.prod ν).restrict (Set.univ ×ˢ A) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hkA : Integrable (Function.uncurry fun y s => c j y * conj (f j y s)) (m.prod (ν.restrict A)) := by
    rw [hres]; exact (hki j).restrict
  symm
  calc ∫ y, c j y * inner ℂ (F j y) (indicatorConstLp 2 hA hνA.ne (1 : ℂ)) ∂m
      = ∫ y, ∫ s in A, c j y * conj (f j y s) ∂ν ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [inner_ind ν (F j y) (f j y) ((hf j).2 y) A hA hνA.ne, integral_const_mul]
    _ = ∫ s in A, ∫ y, c j y * conj (f j y s) ∂m ∂ν := integral_integral_swap hkA

end PositivityTheory.Rg.BcB.E2.P
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.DualityDiagonalClassOfAffineProperBaseChange
noncomputable section

open NumberField Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E2

attribute [local instance] borelH

theorem measurable_wt {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} : Measurable (wt : H E a b → ℝ) :=
  (measurable_const.add ((redBasic E a).2.2.comp
    (@Continuous.measurable _ _ _ _ ⟨le_rfl⟩ _ (borel _) ⟨rfl⟩ _ continuous_fst))).add ((redBasic E b).2.2.comp
    (@Continuous.measurable _ _ _ _ ⟨le_rfl⟩ _ (borel _) ⟨rfl⟩ _ continuous_snd))

theorem orthogonal_keeping_of_estimate (h : OneStep) : OrthogonalKeepingOperator := by
  classical
  intro E _ _ _ a b D ι _ K _ _ _ J hJ B _ _ _ _ R p a₀ C Φ g hp ha hC h1 hΦ hT hg hg'
  set M := 2 * (a + b)
  have hw : ∀ x : H E a b, 0 < wt x := fun x => by
    rw [wt_eq]; linarith [((redBasic E a).2.1 x.1).1, ((redBasic E b).2.1 x.2).1]
  obtain ⟨c, hc⟩ := hC.exists_eq_range ⟨1, h1⟩
  have key := fun k : ℕ => h (ctx ratProper_holds D) ι K J B R p a₀ C Φ g
    (fun x : H E a b => ENNReal.ofReal (wt x ^ (-(2 * M : ℤ)))) hJ hp ha hC h1 hΦ
    (fun x => by
      obtain ⟨T, ht, hv, _⟩ := hT x
      exact ⟨T, ht, hv⟩) (measurable_wt.pow_const _).ennreal_ofReal
    (fun x => ⟨(ENNReal.ofReal_pos.2 (zpow_pos (hw x) _)).ne', ENNReal.ofReal_ne_top⟩)
    (fun Ω hΩ => wtCount E a b D Ω hΩ M le_rfl) hg
    (fun n i => by
      refine ne_of_eq_of_ne (lintegral_congr fun x : H E a b => ?_) (hg' n i M).ne
      have e : (ENNReal.ofReal (wt x ^ (-(2 * M : ℤ))))⁻¹ = ENNReal.ofReal (wt x ^ (2 * M)) := by
        rw [← ENNReal.ofReal_inv_of_pos (zpow_pos (hw x) _), _root_.zpow_neg, inv_inv,
          show (2 * M : ℤ) = ((2 * M : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact congrArg (· * ‖(g n i : H E a b → ℂ) x‖ₑ ^ 2) e)
    ((Finset.range (k + 1)).image c) (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  choose s f h1 h2 _ h3 using key
  refine ⟨M, s, f, fun x hx => ?_, fun k => ⟨h2 k, (h3 k).cont, (h3 k).ne, fun i γ x => (h3 k).inv i γ.1 γ.2 x, (h3 k).wt,
    fun x hx => funext fun i => funext fun y => (h3 k).eig ⟨x, hx⟩ i y, (h3 k).orth⟩⟩
  obtain ⟨n, rfl⟩ : x ∈ Set.range c := hc ▸ hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop n] with k hk
  exact h1 k _ (Finset.mem_image_of_mem c (Finset.mem_range.2 (by omega)))

theorem duality_diagonalClass_of_affineProperBaseChange (h : OrthogonalKeepingOperator) : E.E2 := by
  intro E _ _ _ a b D ι _ K _ _ _ J hJ B _ _ _ _ R p a₀ C Φ hp ha hC h1 hΦ hT
  obtain ⟨M, s, f, a1, a2⟩ := h E a b D ι K J hJ B R p a₀ C Φ (fun _ => 0) hp ha hC h1 hΦ
    (fun x => (hT x).imp fun T t => ⟨t.1, t.2.1, fun u hu v => by rw [t.2.2 u hu, inner_zero_right]⟩)
    (fun _ _ => inner_zero_right _) (fun _ i M => by
      rw [lintegral_congr_ae (g := fun _ => 0), lintegral_zero]
      · exact ENNReal.zero_lt_top
      · filter_upwards [Lp.coeFn_zero ℂ 2 D.ν] with x hx
        have : ((0 : Hs (ι := ι) D) i : H E a b → ℂ) x = 0 := hx
        rw [this, enorm_zero, zero_pow two_ne_zero, mul_zero])
  exact ⟨M, s, f, a1, fun k => ⟨(a2 k).1, (a2 k).2.1, (a2 k).2.2.1, (a2 k).2.2.2.1, (a2 k).2.2.2.2.1, (a2 k).2.2.2.2.2.1⟩⟩

end PositivityTheory.Rg.BcB.E2

end
end

namespace PositivityTheory.Rg.BcB.E2

open E1

theorem spec_holds : Spec := P.spec P.gelf P.point P.specmeas P.speciso

theorem desint_holds : Desint :=
  P.desint P.jointrep P.tonelli P.weakae (P.eigae P.weakae) (P.locint P.tonelli) P.nonzero (P.smooth P.convcont)

theorem fData_holds : FData :=
  P.fdata (P.rowsex kerBasic vecEx vecNorm vecInner) (P.rowseig P.aeeq (P.unfold kerBasic P.convcont))

theorem oneStep_holds : OneStep := oneStep_of spec_holds fData_holds desint_holds P.hssep

theorem orthogonal_keeping_holds : E.OrthogonalKeepingOperator := orthogonal_keeping_of_estimate oneStep_holds

theorem proper_base_change : E.E2 := duality_diagonalClass_of_affineProperBaseChange orthogonal_keeping_holds

end PositivityTheory.Rg.BcB.E2
