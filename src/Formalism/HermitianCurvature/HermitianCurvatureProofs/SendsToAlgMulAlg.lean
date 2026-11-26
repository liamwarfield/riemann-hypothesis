module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroFormIntegrableCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSquareIntegrableOfTransport
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianSquareIntegrableAll
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCfLast
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem cf_last_isEmpty (r : ℕ) : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun l => by have := l.1.isLt; have := l.2; simp at *; omega⟩

theorem integrable_cf_last {r : ℕ} (f : Cf r (Fin.last r) → ℂ) : Integrable f := by
  haveI := cf_last_isEmpty r
  have hvol : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (fun l => isEmptyElim l) := by
    rw [volume_pi, Measure.pi_of_empty]
  haveI : IsFiniteMeasure (volume : Measure (Cf r (Fin.last r))) := by rw [hvol]; infer_instance
  have hf : f = fun _ => f (fun l => isEmptyElim l) := by
    funext c'
    congr 1
    funext l
    exact isEmptyElim l
  rw [hf]
  exact integrable_const _

end Formalism.FourierDecayAlt.P5.HerC
end
end

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapI (i : Fin (r + 1)) (c : Fin r → ℂ) (q : Cf r i × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue i c q.1, Matrix.of q.2)

theorem glueMapI_continuous (i : Fin (r + 1)) (c : Fin r → ℂ) : Continuous (glueMapI (k := k) i c) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun l => ?_
  by_cases h : i.val ≤ l.val
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun q => q.1 ⟨l, h⟩ := by
      funext q; simp [glue, h]
    rw [e]; exact (continuous_apply _).comp continuous_fst
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun _ => c l := by
      funext q; simp [glue, h]
    rw [e]; exact continuous_const

theorem measurableSet_glueMapI_DomR (i : Fin (r + 1)) (c : Fin r → ℂ) :
    MeasurableSet (glueMapI (k := k) i c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapI_continuous i c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapI_continuous i c)).measurableSet

theorem pair_measurableI (i : Fin (r + 1)) (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r i × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMapI (k := k) i c) (glueMapI (k := k) i c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapI_continuous i c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapI_continuous i c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapI_DomR i c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

theorem pairAt_measI (μ : Measure (Mt k r)) [SFinite μ] (i : Fin (r + 1)) (u v : RadSp k r z z' π π')
    (c : Fin r → ℂ) : StronglyMeasurable (fun c' : Cf r i => pairAt μ u v (glue i c c')) :=
  (pair_measurableI i c u v).stronglyMeasurable.integral_prod_right'

def wtI (i : Fin (r + 1)) (c' : Cf r i) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem wtI_measurable (i : Fin (r + 1)) : Measurable (wtI i) := by
  unfold wtI
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelSquareIntegrable (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u u (glue i c c'))

theorem hsInner_self_ofRealI (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_selfI (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofRealI]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_leI (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_selfI, norm_pairAt_selfI]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_crossI (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1))
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelSquareIntegrable μ i u c) (Iv : LevelSquareIntegrable μ i v c) :
    Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u v (glue i c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    ((wtI_measurable i).aestronglyMeasurable.mul (pairAt_measI μ i u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wtI i c' * pairAt μ u v (glue i c c')‖ ≤
    ‖wtI i c' * pairAt μ u u (glue i c c')‖ + ‖wtI i c' * pairAt μ v v (glue i c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hu hv _) (norm_nonneg _)

end Meas

section Red

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntOuter_of_l2I {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1)) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ lcSub k r z z' π π') (hv : ∀ a, v a ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : ∀ a, LevelSquareIntegrable μ i (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ i (v a) c) :
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (u a) (v a) (glue i c c')) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => int_crossI μ hμ i (hu a) (hv a) c (Iu a) (Iv a)

def HermitianSquareIntegrableAt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (i : Fin (P.r + 1)) : Prop :=
  ∀ c ∈ OmX P.r, (∀ u ∈ herKc S P z z' π π' L st l0 D i, LevelSquareIntegrable μ i u c) ∧
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D i) x → ∀ a, LevelSquareIntegrable μ i (act (RRi L st i w) x a) c

def HermitianSquareIntegrableAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ i : Fin (P.r + 1), i.val < P.r → HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D i

theorem outer_form_compact_of_square (h : HermitianSquareIntegrableAll) : FormIntOuterCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy
  by_cases hi : i.val < P.r
  · have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
    have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
      (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
    have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
    have hu : ∀ a, act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' := fun a =>
      (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
    obtain ⟨hK, hR⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
    exact formIntOuter_of_l2I μ hD.2.1 i _ y hu (fun a => hle (hy a)) c (hR w hw x hx) (fun a => hK _ (hy a))
  · have e : i = Fin.last P.r := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst e
    exact integrable_cf_last _

end Red

end Formalism.FourierDecayAlt.P5.HerD
end
end

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Shift

def shIdx {r : ℕ} (i : Fin (r + 1)) : {l : Fin (r - i) // (0 : Fin (r - i + 1)).val ≤ l.val} ≃ {l : Fin r // i.val ≤ l.val} where
  toFun l := ⟨⟨l.1.val + i.val, by have := l.1.isLt; have := i.isLt; omega⟩, Nat.le_add_left _ _⟩
  invFun l := ⟨⟨l.1.val - i.val, by have := l.1.isLt; have := l.2; omega⟩, Nat.zero_le _⟩
  left_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val + i.val - i.val = l.1.val
    omega
  right_inv l := by
    apply Subtype.ext; apply Fin.ext
    show l.1.val - i.val + i.val = l.1.val
    have := l.2; omega

def shEq {r : ℕ} (i : Fin (r + 1)) : Cf (r - i) 0 ≃ᵐ Cf r i :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_mp {r : ℕ} (i : Fin (r + 1)) : MeasurePreserving (shEq i) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ) (shIdx i)

theorem shEq_apply {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) (l : {l : Fin r // i.val ≤ l.val}) :
    shEq i c' l = c' ((shIdx i).symm l) := by
  unfold shEq
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rfl

theorem shiftCf_glue {r : ℕ} (i : Fin (r + 1)) (c'' : Fin (r - i) → ℂ) (c' : Cf (r - i) 0) :
    Formalism.FourierDecayAlt.P.PTie.shiftCf i (glue 0 c'' c') = shEq i c' := by
  funext l
  rw [shEq_apply]
  simp [Formalism.FourierDecayAlt.P.PTie.shiftCf, shIdx]
  rfl

theorem wtI_shEq {r : ℕ} (i : Fin (r + 1)) (c' : Cf (r - i) 0) : wtI i (shEq i c') = wtI 0 c' := by
  unfold wtI
  congr 1
  simp_rw [shEq_apply]
  exact Fintype.prod_equiv (shIdx i).symm _ _ fun l => rfl

end Shift

section Transfer

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem level_square_integrable_of_transport {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (i : Fin (r + 1)) (c : Fin r → ℂ)
    {zi zi' : Fin (2 * (r - i) + k + 1) → ℂ} {πi : Mx k (r - i) → (Wp →L[ℂ] Wp)} {πi' : Mx k (r - i) → (Wq →L[ℂ] Wq)}
    (μi : Measure (Mt k (r - i))) (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - i) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' = (κ : ℂ) * pairAt μ Φ Ψ (glue i c (Formalism.FourierDecayAlt.P.PTie.shiftCf i c'')))
    (v : RadSp k r z z' π π') (c'' : Fin (r - i) → ℂ) (h : LevelSquareIntegrable μi 0 (T v) c'') : LevelSquareIntegrable μ i v c := by
  unfold LevelSquareIntegrable at h ⊢
  have e : (fun c' : Cf r i => wtI i c' * pairAt μ v v (glue i c c')) ∘ (shEq i) =
      fun c' => (κ : ℂ)⁻¹ * (wtI 0 c' * pairAt μi (T v) (T v) (glue 0 c'' c')) := by
    funext c'
    simp only [Function.comp_apply]
    rw [hT, shiftCf_glue, wtI_shEq]
    have : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    field_simp
  have h2 := h.const_mul ((κ : ℂ)⁻¹)
  rw [← e] at h2
  exact ((shEq_mp i).integrable_comp_emb (shEq i).measurableEmbedding).mp h2

end Transfer

section Lev

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem act_tr {k r k' r' : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {zi zi' : Fin (2 * r' + k' + 1) → ℂ} {πi : Mx k' r' → (Wp →L[ℂ] Wp)}
    {πi' : Mx k' r' → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k' r' zi zi' πi πi') {M : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))}
    {M' : SlopeTestRemainingChoices S (Pr (RadSp k' r' zi zi' πi πi'))} (h : Formalism.FourierDecayAlt.P.PBH.ARel T M M')
    (x : Ix S → RadSp k r z z' π π') (a : Ix S) : T (act M x a) = act M' (fun b => T (x b)) a := by
  unfold act
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := congrArg (fun f => f (x b)) (h a b).1
  simpa using this.symm

end Lev

end Formalism.FourierDecayAlt.P5.HerD
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialTransformSquareIntegrable
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section L2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def wt0 (c' : Cf r 0) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem level_zero_weight_measurable : Measurable (wt0 (r := r)) := by
  unfold wt0
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelZeroSquareIntegrable (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u u (glue 0 c c'))

theorem pairAt_meas0 (μ : Measure (Mt k r)) [SFinite μ] (u v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    StronglyMeasurable (fun c' : Cf r 0 => pairAt μ u v (glue 0 c c')) :=
  (pair_measurable c u v).stronglyMeasurable.integral_prod_right'

theorem hsInner_self_ofReal (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_self (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofReal]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_self, norm_pairAt_self]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_cross (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelZeroSquareIntegrable μ u c) (Iv : LevelZeroSquareIntegrable μ v c) :
    Integrable (fun c' : Cf r 0 => wt0 c' * pairAt μ u v (glue 0 c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    (level_zero_weight_measurable.aestronglyMeasurable.mul (pairAt_meas0 μ u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wt0 c' * pairAt μ u v (glue 0 c c')‖ ≤
    ‖wt0 c' * pairAt μ u u (glue 0 c c')‖ + ‖wt0 c' * pairAt μ v v (glue 0 c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_le μ hμ hu hv _) (norm_nonneg _)

theorem pairAt_zero_zero (μ : Measure (Mt k r)) (c : Fin r → ℂ) :
    pairAt μ (0 : RadSp k r z z' π π') 0 c = 0 := by
  unfold pairAt
  simp [hsInner_zero_left]

theorem pairAt_add_add (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {u v : RadSp k r z z' π π'}
    (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (u + v) (u + v) c = pairAt μ u u c + pairAt μ u v c + pairAt μ v u c + pairAt μ v v c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) +
      B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    show B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) + (v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
    rw [Formalism.FourierDecayAlt.P.B6.hsInner_add_left, Formalism.FourierDecayAlt.P.B6.hsInner_add_right, Formalism.FourierDecayAlt.P.B6.hsInner_add_right]
    ring
  have e2 : (∫ g : Mt k r, B.hsInner (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      (((u + v : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ∂μ) =
      ∫ g, ((fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) +
        (fun g : Mt k r => B.hsInner ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((v : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)))) g ∂μ := by
    congr 1; funext g; rw [e g]; rfl
  rw [e2, integral_add' (((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)).add (int_lc μ hμ hv hu c))
      (int_lc μ hμ hv hv c),
    integral_add' ((int_lc μ hμ hu hu c).add (int_lc μ hμ hu hv c)) (int_lc μ hμ hv hu c),
    integral_add' (int_lc μ hμ hu hu c) (int_lc μ hμ hu hv c)]


variable (k r z z' π π') in
def squareIntegrableSmoothSubmoduleGL (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) :
    Submodule ℂ (RadSp k r z z' π π') where
  carrier := {u | u ∈ lcSub k r z z' π π' ∧ ∀ c, LevelZeroSquareIntegrable μ u c}
  zero_mem' := ⟨(lcSub k r z z' π π').zero_mem, fun c => by
    unfold LevelZeroSquareIntegrable
    simp only [pairAt_zero_zero, mul_zero]
    exact integrable_zero _ _ _⟩
  add_mem' := by
    rintro u v ⟨hu, Iu⟩ ⟨hv, Iv⟩
    refine ⟨(lcSub k r z z' π π').add_mem hu hv, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_add_add μ hμ hu hv, mul_add]
    exact (((Iu c).add (int_cross μ hμ hu hv c (Iu c) (Iv c))).add
      (int_cross μ hμ hv hu c (Iv c) (Iu c))).add (Iv c)
  smul_mem' := by
    rintro a u ⟨hu, Iu⟩
    refine ⟨(lcSub k r z z' π π').smul_mem a hu, fun c => ?_⟩
    unfold LevelZeroSquareIntegrable
    simp_rw [pairAt_smul_left, pairAt_smul_right]
    have e : (fun c' : Cf r 0 => wt0 c' * (a * ((starRingEnd ℂ) a * pairAt μ u u (glue 0 c c')))) =
        fun c' => (a * (starRingEnd ℂ) a) * (wt0 c' * pairAt μ u u (glue 0 c c')) := by
      funext c'; ring
    rw [e]
    exact (Iu c).const_mul _

theorem unimodular_multiplier_preserves_L2 (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → Mx k r → ℂ} (hW : multiplicationOperator W m)
    (hm : ∀ c g, ‖m c g‖ = 1) : ∀ u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ, W u ∈ squareIntegrableSmoothSubmoduleGL k r z z' π π' μ hμ := by
  rintro u ⟨hu, Iu⟩
  refine ⟨mul_lc hW u hu, fun c => ?_⟩
  have e : ∀ c0, pairAt μ (W u) (W u) c0 = pairAt μ u u c0 := by
    intro c0
    unfold pairAt
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show B.hsInner ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) ((W u : Fn k r (Wq →L[ℂ] Wp)) c0 (Matrix.of g)) = _
    rw [hW u c0 (Matrix.of g), hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hm]
    simp
  unfold LevelZeroSquareIntegrable
  simp_rw [e]
  exact Iu c

theorem norm_fsv (s t : ℂ) : ‖fsv s t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (s * t - (starRingEnd ℂ) s * (starRingEnd ℂ) t).re = 0 := by
    rw [← map_mul, Complex.sub_re, Complex.conj_re, sub_self]
  rw [this, Real.exp_zero]

end L2

section Classes

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem radial_transform_square_integrable (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (F : Mx P.k P.r → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt P z z' F) (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) :
    Φ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine ⟨jfCptLocAll Wp Wq P z z' π π' D F Φ hP hz hz' hπ hπ' hF hΦ, fun c => ?_⟩
  subst hz hz' hπ hπ'
  have h := level_zero_form_integrable_compact (S := Empty) D μ hμ (fun _ => F) (fun _ => F) (fun _ => Φ) (fun _ => Φ)
    (fun _ => hF.1.1) (fun _ => hF.1.1) (fun _ => hΦ) (fun _ => hΦ) c
  unfold LevelZeroSquareIntegrable
  letI : Unique (Ix Empty) := { default := Empty.elim, uniq := fun _ => funext fun x => x.elim }
  simpa [wt0] using h

theorem compact_kernel_le_L2 (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (D : B.RealPlaceData P.k P.r Wp Wq) (hP : IsPlace P z z' π π')
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') :
    herKc S P z z' π π' L st l0 D 0 ≤ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
  refine Submodule.span_le.mpr fun Φ hΦ => ?_
  have key : ∀ (i : Fin (P.r + 1)) (Ψ : RadSp P.k P.r z z' π π'), HerGenC S P z z' π π' L st l0 D i Ψ →
      i = 0 → Ψ ∈ squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ := by
    intro i Ψ h
    induction h with
    | jf F Φ hF hΦ => exact fun _ => radial_transform_square_integrable P z z' π π' μ hμ D hP hz hz' hπ hπ' F hF Φ hΦ
    | slice l w a b Φ _ _ _ => exact fun h => absurd h (Fin.succ_ne_zero l)
    | waveC l w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun c _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun c _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
    | waveZ w s Wv Wv' a b Φ _ h1 h2 _ ih =>
      intro h
      have hm : (Vw (mkP Wv Wv') s w : SlopeTestRemainingChoices S (Pr (RadSp P.k P.r z z' π π'))) ∈
          entSub (presAlg (squareIntegrableSmoothSubmoduleGL P.k P.r z z' π π' μ hμ)) :=
        (entSub _).mul_mem (Formalism.FourierDecayAlt.P5.HerA.io_mem (show mkP Wv Wv' ∈ presAlg _ from
          ⟨unimodular_multiplier_preserves_L2 μ hμ h1 (fun _ _ => norm_fsv _ _), unimodular_multiplier_preserves_L2 μ hμ h2 (fun _ _ => norm_fsv _ _)⟩)) (UUiw_mem s w)
      exact (hm a b).1 Φ (ih h)
  exact key 0 Φ hΦ rfl

end Classes

end Formalism.FourierDecayAlt.P5.HerC
end
end

open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Pr

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pr_fst_mul (x y : Pr V) : (x * y).1 = x.1 * y.1 := rfl

theorem pr_fst_algebraMap (a : ℂ) : (algebraMap ℂ (Pr V) a).1 = algebraMap ℂ (Module.End ℂ V) a := rfl

def sendsTo (U : Submodule ℂ V) (v : V) : Submodule ℂ (Pr V) where
  carrier := {x | x.1 v ∈ U}
  zero_mem' := by show (0 : Module.End ℂ V) v ∈ U; simp
  add_mem' := by
    intro x y hx hy
    show (x.1 + y.1) v ∈ U
    rw [LinearMap.add_apply]; exact U.add_mem hx hy
  smul_mem' := by
    intro a x hx
    show (a • x.1) v ∈ U
    rw [LinearMap.smul_apply]; exact U.smul_mem a hx

theorem sendsTo_alg_mul_alg (U : Submodule ℂ V) (v : V) {x : Pr V} (hx : x ∈ sendsTo U v) (a b : ℂ) :
    algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b ∈ sendsTo U v := by
  show (algebraMap ℂ (Pr V) a * x * algebraMap ℂ (Pr V) b).1 v ∈ U
  rw [pr_fst_mul, pr_fst_mul, pr_fst_algebraMap, pr_fst_algebraMap, Module.End.mul_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  exact U.smul_mem a (U.smul_mem b hx)

end Pr

section Num

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem UUw_mem {𝒜 : StarSubalgebra ℂ A} (s : ℂ) :
    ∀ w : List (Letter ℂ S), (UUw s w : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  intro w
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [UUw]
    refine (entSub 𝒜).mul_mem (Formalism.FourierDecayAlt.P5.HerA.ins_mem _ fun i j => ?_) ih
    show io ((Formalism.YangianSpanCharacter.T.Um (if l.plus then s else star s) : M2 A) i j) ∈ entSub 𝒜
    apply Formalism.FourierDecayAlt.P5.HerA.io_mem
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Um, 𝒜.algebraMap_mem]

theorem star_entSub {𝒜 : StarSubalgebra ℂ A} {M : SlopeTestRemainingChoices S A} (hM : M ∈ entSub 𝒜) : star M ∈ entSub 𝒜 := by
  intro i j
  rw [Matrix.star_apply]
  exact star_mem (hM j i)

theorem mem_bot_alg {x : A} (hx : x ∈ (⊥ : StarSubalgebra ℂ A)) : ∃ a : ℂ, x = algebraMap ℂ A a := by
  rw [StarSubalgebra.mem_bot] at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.symm⟩

end Num

section Wave

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem QQi_castSucc' (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l : Fin P.r) (Y : ℂ) :
    QQi L st l.castSucc Y = (Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y := by
  have h : ∀ Y' : ℂ, tprod L Y' l.val = tprod L Y' (l.val + 1) * Ts (site L l) Y' := fun Y' => by
    rw [tprod, dite_eq_left l.isLt]
  unfold QQi
  rw [Fin.val_castSucc, Fin.val_succ, h, h, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem diag_comm {A : Type*} [Ring A] {f : A} {M : Matrix (Fin 2) (Fin 2) A} (h : ∀ i j, Commute f (M i j)) :
    Matrix.diagonal (fun _ => f) * M = M * Matrix.diagonal (fun _ => f) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact (h i j).eq

theorem commute_inv_of {A : Type*} [Ring A] {f fi x : A} (h1 : f * fi = 1) (h2 : fi * f = 1) (h : Commute f x) :
    Commute fi x := by
  show fi * x = x * fi
  calc fi * x = fi * x * (f * fi) := by rw [h1, mul_one]
    _ = fi * (f * x) * fi := by rw [h.eq]; simp only [mul_assoc]
    _ = x * fi := by rw [← mul_assoc, h2, one_mul]

theorem waveQQ_castSucc (X : ActualOps P.k P.r z z' π π') (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (hAL : IsActualLevel X L) (l : Fin P.r) (s : ℂ)
    (Wv Wv' : Module.End ℂ (RadSp P.k P.r z z' π π'))
    (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) (hW' : multiplicationOperator Wv' (fun c _ => fsv (-s) (c l)))
    (hC : ∀ Y a b, Commute (mkP Wv Wv') (QQi L st l.succ Y a b)) :
    WaveQQ (QQi L st l.castSucc) (mkP Wv Wv') (mkP Wv' Wv) s := by
  intro Y
  obtain ⟨⟨h1, h2, h3⟩, hc, hci, hp⟩ :=
    Formalism.FourierDecayAlt.P5.waveSiteAll Wp Wq P z z' π π' X L hAL l s Wv Wv' hW hW'
  have hT : ∀ Y' : ℂ, Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') =
      Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
    intro Y'
    obtain ⟨-, hUiU, hE⟩ := Formalism.YangianSpanCharacter.Final.T_PlaneWave ℂ (Pr (RadSp P.k P.r z z' π π')) (site L l).p (site L l).c
      (site L l).ci (mkP Wv Wv') s Y' hc hci hp
    calc Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv')
        = Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * (Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
          rw [hUiU, Matrix.mul_one]
      _ = (Ts (site L l) Y' * Matrix.diagonal (fun _ => mkP Wv Wv') * Formalism.YangianSpanCharacter.T.Uinv (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y' * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by
          unfold Ts; rw [hE]
  have hDf : (Matrix.diagonal (fun _ : Fin 2 => mkP Wv Wv'))ᴴ = Matrix.diagonal (fun _ => mkP Wv' Wv) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
  have ha := congrArg Matrix.conjTranspose (hT (star Y))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDf] at ha
  have hci' : ∀ a b, Commute (mkP Wv' Wv) (QQi L st l.succ Y a b) := fun a b =>
    commute_inv_of h1 h2 (hC Y a b)
  have hb : Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv') =
      QQi L st l.succ Y := by
    rw [diag_comm hci', Matrix.mul_assoc, Matrix.diagonal_mul_diagonal, h2]
    rw [show (Matrix.diagonal fun _ : Fin 2 => (1 : Pr (RadSp P.k P.r z z' π π'))) = 1 from Matrix.diagonal_one,
      Matrix.mul_one]
  rw [QQi_castSucc']
  calc Matrix.diagonal (fun _ => mkP Wv' Wv) *
        ((Ts (site L l) (star Y))ᴴ * QQi L st l.succ Y * Ts (site L l) Y) * Matrix.diagonal (fun _ => mkP Wv Wv')
      = (Matrix.diagonal (fun _ => mkP Wv' Wv) * (Ts (site L l) (star Y))ᴴ) * QQi L st l.succ Y *
          (Ts (site L l) Y * Matrix.diagonal (fun _ => mkP Wv Wv')) := by simp only [Matrix.mul_assoc]
    _ = ((Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * ((Ts (site L l) (star Y))ᴴ * Matrix.diagonal (fun _ => mkP Wv' Wv))) *
          QQi L st l.succ Y * (Matrix.diagonal (fun _ => mkP Wv Wv') * Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s) := by
        rw [ha, hT Y]
    _ = (Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s)ᴴ * (Ts (site L l) (star Y))ᴴ *
          (Matrix.diagonal (fun _ => mkP Wv' Wv) * QQi L st l.succ Y * Matrix.diagonal (fun _ => mkP Wv Wv')) *
          Ts (site L l) Y * Formalism.YangianSpanCharacter.T.Um (R := ℂ) (A := Pr (RadSp P.k P.r z z' π π')) s := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hb]; simp only [Matrix.mul_assoc]

end Wave

section WordWave

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] {S : Type} [Fintype S] [DecidableEq S]

theorem rr_io_wave (QQ : ℂ → M2 A) (f fi : A) (s : ℂ) (w : List (Letter ℂ S)) (hW : IsWave f fi)
    (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    RRw QQ w * io f = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by
  obtain ⟨hVVi, -, hRR, -⟩ := Formalism.FourierDecayAlt.P.plane_wave_word_identity ℂ A S QQ f fi s w hW hQ hw
  obtain ⟨h1, h2, h3⟩ := hW
  have hsfi : star fi = f := by rw [← h3, star_star]
  have e1 : (io fi : SlopeTestRemainingChoices S A) * io f = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Wd11.io_mul, h2, Formalism.FourierDecayAlt.P.Wd11.io_one]
  have hUU : UUiw s w * UUw s w = (1 : SlopeTestRemainingChoices S A) := by
    have hv : io f * UUiw s w * (UUw s w * io fi) = (1 : SlopeTestRemainingChoices S A) := by
      have := hVVi; unfold Vw Viw at this; simpa only [mul_assoc] using this
    calc UUiw s w * UUw s w = (io fi * io f) * (UUiw s w * UUw s w) * (io fi * io f) := by
          rw [e1, one_mul, mul_one]
      _ = io fi * (io f * UUiw s w * (UUw s w * io fi)) * io f := by simp only [mul_assoc]
      _ = 1 := by rw [hv, mul_one, e1]
  have hsVi : star (Viw fi s w) = io f * star (UUw s w) := by
    unfold Viw
    rw [star_mul, Formalism.FourierDecayAlt.P.Wd11.io_star, hsfi]
  have hsVV : star (Viw fi s w) * star (Vw f s w) = 1 := by
    rw [← star_mul, hVVi, star_one]
  have key : RRw QQ w * Vw f s w = star (Viw fi s w) * RRw QQ w := by
    calc RRw QQ w * Vw f s w = (star (Viw fi s w) * star (Vw f s w)) * RRw QQ w * Vw f s w := by
          rw [hsVV, one_mul]
      _ = star (Viw fi s w) * (star (Vw f s w) * RRw QQ w * Vw f s w) := by simp only [mul_assoc]
      _ = star (Viw fi s w) * RRw QQ w := by rw [hRR]
  calc RRw QQ w * io f = RRw QQ w * io f * (UUiw s w * UUw s w) := by rw [hUU, mul_one]
    _ = (RRw QQ w * Vw f s w) * UUw s w := by unfold Vw; simp only [mul_assoc]
    _ = io f * (star (UUw s w) * RRw QQ w * UUw s w) := by rw [key, hsVi]; simp only [mul_assoc]

theorem io_apply_mul (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : ((io x : SlopeTestRemainingChoices S A) * M) a b = x * M a b := by
  simp [io, Matrix.diagonal_mul]

theorem mul_io_apply (x : A) (M : SlopeTestRemainingChoices S A) (a b : Ix S) : (M * (io x : SlopeTestRemainingChoices S A)) a b = M a b * x := by
  simp [io, Matrix.mul_diagonal]

end WordWave

end Formalism.FourierDecayAlt.P5.HerD
