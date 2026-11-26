module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliFreeAction

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Formalism.REAL.Tm]
  split_ifs <;> simp

theorem actU_qdet : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  intro n ε H _ _ σ S E hE u v
  let F : FreeMonoid (Fin n × Fin n) →* Module.End ℂ S := FreeMonoid.lift fun ab => E ab.1 ab.2
  let ψ : MonoidAlgebra ℂ (FreeMonoid (Fin n × Fin n)) →ₐ[ℂ] Module.End ℂ S :=
    MonoidAlgebra.lift ℂ _ _ F
  let φ : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ S :=
    ψ.comp (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ (Fin n × Fin n) ≃ₐ[ℂ] _).toAlgHom
  have hw : ∀ l : List (Fin n × Fin n),
      PI.DSInfCharCap.dsigCW ε σ (l.map PI.DSInfCharCap.unitM) (v : H) =
        ((F (FreeMonoid.ofList l) v : S) : H) := by
    intro l
    induction l with
    | nil => simp [PI.DSInfCharCap.dsigCW]
    | cons a l ih =>
      rw [List.map_cons, PI.DSInfCharCap.dsigCW, ih, FreeMonoid.ofList_cons, map_mul,
        Module.End.mul_apply, ← hE a.1 a.2]
      simp [F]
  have hφ : ∀ p, PI.DSInfCharCap.actU ε σ p v = ((φ p v : S) : H) := by
    intro p
    have : φ p = ψ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) := rfl
    rw [this]
    simp only [ψ, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, Finsupp.sum,
      LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hw]
  have hE' : (fun a b => φ (PI.DSInfCharCap.Egl n a b)) = E := by
    funext a b
    simp [φ, ψ, F, PI.DSInfCharCap.Egl, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hφ, map_qdet, hE']

end GlobalTheory.CapelliFreeAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperatorStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeAlgebraAction_capelliDeterminant_eq_operator : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  first | exact @GlobalTheory.CapelliFreeAction.actU_qdet | exact GlobalTheory.CapelliFreeAction.actU_qdet | (intros; apply GlobalTheory.CapelliFreeAction.actU_qdet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplex
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem unfold_integral_of_lintegral {S X Y E : Type*} [MeasurableSpace S] [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Y) (σ : Measure S) (ν : Measure X) [SFinite σ] (m : S → X → Y)
    (hm : Measurable (fun q : S × X => m q.1 q.2))
    (hq : ∀ g : Y → ℝ≥0∞, Measurable g → ∫⁻ y, g y ∂μ = ∫⁻ x, ∫⁻ s, g (m s x) ∂σ ∂ν)
    (f : Y → E) (hf : StronglyMeasurable f) (hi : Integrable f μ) :
    (∀ᵐ x ∂ν, Integrable (fun s => f (m s x)) σ) ∧ Integrable (fun x => ∫ s, f (m s x) ∂σ) ν ∧
      ∫ y, f y ∂μ = ∫ x, (∫ s, f (m s x) ∂σ) ∂ν := by
  have hmx : ∀ x, Measurable (fun s => m s x) := fun x =>
    hm.comp (measurable_id.prodMk measurable_const)
  let η : ProbabilityTheory.Kernel X Y :=
    { toFun := fun x => σ.map (fun s => m s x)
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
        simp_rw [Measure.map_apply (hmx _) hA]
        exact measurable_measure_prodMk_right (hm hA) }
  have hη : ∀ x, η x = σ.map (fun s => m s x) := fun _ => rfl
  have hμ : (ProbabilityTheory.Kernel.comp η (ProbabilityTheory.Kernel.const Unit ν)) () = μ := by
    ext A hA
    rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ hA, ProbabilityTheory.Kernel.const_apply,
      ← lintegral_indicator_one hA, hq _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    rw [hη, ← lintegral_indicator_one hA, lintegral_map (measurable_one.indicator hA) (hmx x)]
  have hI : ∀ x, ∫ y, f y ∂η x = ∫ s, f (m s x) ∂σ := fun x => by
    rw [hη, integral_map (hmx x).aemeasurable hf.aestronglyMeasurable]
  rw [← hμ] at hi
  refine ⟨?_, ?_, ?_⟩
  · have h := hi.ae_of_comp
    rw [ProbabilityTheory.Kernel.const_apply] at h
    filter_upwards [h] with x hx
    rw [hη] at hx
    exact (integrable_map_measure hf.aestronglyMeasurable (hmx x).aemeasurable).1 hx
  · have h := hi.integral_comp
    rw [ProbabilityTheory.Kernel.const_apply] at h
    simpa only [hI] using h
  · have h := ProbabilityTheory.Kernel.integral_comp hi
    rw [ProbabilityTheory.Kernel.const_apply, hμ] at h
    simpa only [hI] using h

theorem weil_formula_integrable : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  intro k r μG μS νq _ f hq hf hi
  have hc : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of q.1 * Matrix.of q.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := continuous_fst
    have h2 : Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of q.2 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) := continuous_snd
    exact h1.matrix_mul h2
  exact unfold_integral_of_lintegral μG μS νq
    (fun s x => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r))
    hc.measurable hq f hf.stronglyMeasurable hi

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilFormulaIntegrableComplexStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_integrable_complex : ∀ (k r : ℕ) (μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)) [SFinite μS] (f : Formalism.QuantumDeterminants.Mt k r → ℂ), PI.BesselPeriodGGP.IsQuotMeas μG μS νq → Measurable f → Integrable f μG → (∀ᵐ x ∂νq, Integrable (fun s => f (fun i j => (Matrix.of s * Matrix.of x) i j)) μS) ∧ Integrable (fun x => ∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) νq ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂νq := by
  first | exact @GlobalTheory.weil_formula_integrable | exact GlobalTheory.weil_formula_integrable | (intros; apply GlobalTheory.weil_formula_integrable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.HaarInversion

def mulM {m : ℕ} (x y : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x * Matrix.of y) i j

noncomputable def invM {m : ℕ} (x : PI.MtM m) : PI.MtM m := fun i j => (Matrix.of x)⁻¹ i j

lemma of_mulM {m : ℕ} (x y : PI.MtM m) : Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := rfl

lemma of_invM {m : ℕ} (x : PI.MtM m) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := rfl

lemma measurable_mulM {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → PI.MtM m}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hu)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hv)

lemma measurable_invM {m : ℕ} : Measurable (invM : PI.MtM m → PI.MtM m) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have hof : Continuous fun x : PI.MtM m => (Matrix.of x : Matrix (Fin m) (Fin m) ℂ) := continuous_id
  have h1 : Measurable fun x : PI.MtM m => (Matrix.of x).det := hof.matrix_det.measurable
  have h2 : Measurable fun x : PI.MtM m => (Matrix.of x).adjugate i j :=
    (hof.matrix_adjugate.matrix_elem i j).measurable
  simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact h1.inv.mul h2

theorem lintegral_inv_eq : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  intro m S μ hS hμ hR f hf
  obtain ⟨hσ, hne, hc, hL⟩ := hμ
  obtain ⟨-, -, -, hinv⟩ := hS
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := hc
  have left : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM a y) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM (measurable_const (a := a)) measurable_id)
    have e : (fun y : PI.MtM m => mulM a (id y)) = PI.lmulQ (Matrix.of a) := rfl
    rw [e, hL _ ha] at h
    exact h.symm
  have right : ∀ a : PI.MtM m, Matrix.of a ∈ S → ∀ g : PI.MtM m → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM y a) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have h := lintegral_map (μ := μ) hg (measurable_mulM measurable_id (measurable_const (a := a)))
    have e : (fun y : PI.MtM m => mulM (id y) a) = PI.rmulQ (Matrix.of a) := rfl
    rw [e, hR _ ha] at h
    exact h.symm
  obtain ⟨t, ht, -, ht0, ht1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0)
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hne)
  set g : PI.MtM m → ℝ≥0∞ := t.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator ht
  have hgi : ∫⁻ y, g y ∂μ = μ t := lintegral_indicator_one ht
  have hfi : Measurable fun x => f (invM x) := hf.comp measurable_invM
  have key : (∫⁻ x, f (invM x) ∂μ) * μ t = (∫⁻ x, f x ∂μ) * μ t := by
    calc (∫⁻ x, f (invM x) ∂μ) * μ t
        = ∫⁻ x, ∫⁻ y, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          rw [← lintegral_mul_const _ hfi]
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => g (mulM x y) :=
            hg.comp (measurable_mulM measurable_const measurable_id')
          rw [lintegral_const_mul _ hm, left x hx g hg, hgi]
      _ = ∫⁻ y, ∫⁻ x, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hfi.comp measurable_fst).mul (hg.comp (measurable_mulM measurable_fst measurable_snd))
      _ = ∫⁻ y, ∫⁻ x, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          simp only
          rw [← right y hy (fun x => f (mulM y (invM x)) * g x)
            ((hf.comp (measurable_mulM measurable_const measurable_invM)).mul hg)]
          refine lintegral_congr fun x => ?_
          congr 2
          apply Matrix.of.injective
          rw [of_mulM, of_invM, of_invM, of_mulM, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
            (hinv _ hy).2, Matrix.one_mul]
      _ = ∫⁻ x, ∫⁻ y, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hf.comp (measurable_mulM measurable_fst (measurable_invM.comp measurable_snd))).mul
            (hg.comp measurable_snd)
      _ = ∫⁻ x, (∫⁻ y, f y ∂μ) * g x ∂μ := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => f (mulM y (invM x)) :=
            hf.comp (measurable_mulM measurable_id' measurable_const)
          rw [lintegral_mul_const _ hm, right (invM x) (hinv _ hx).1 f hf]
      _ = (∫⁻ x, f x ∂μ) * μ t := by rw [lintegral_const_mul _ hg, hgi]
  exact (ENNReal.mul_left_inj ht0.ne' ht1.ne).mp key

end GlobalTheory.HaarInversion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroupStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  first | exact @GlobalTheory.HaarInversion.lintegral_inv_eq | exact GlobalTheory.HaarInversion.lintegral_inv_eq | (intros; apply GlobalTheory.HaarInversion.lintegral_inv_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.LengthCont

variable {n ι : Type} [Fintype n] [DecidableEq n]

def dst (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (A : Matrix n n ℂ) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℂ n)
    (Submodule.span ℂ ((fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s) : Set _)

def opn (M : Matrix n n ℂ) : ℝ := ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M‖

lemma opn_cont : Continuous (opn (n := n)) := by

  let L : Matrix n n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun M => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
      map_add' := fun M N => map_add _ M N
      map_smul' := fun c M => map_smul _ c M }
  exact continuous_norm.comp (LinearMap.continuous_of_finiteDimensional L)

lemma opn_one [Nonempty n] : opn (1 : Matrix n n ℂ) = 1 := by
  unfold opn
  rw [map_one]
  exact norm_one

private lemma infDist_image_le_opNorm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (y : E) (K : Set E) (hK : K.Nonempty) :
    Metric.infDist (T y) (T '' K) ≤ ‖T‖ * Metric.infDist y K := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hδ : 0 < ε / (‖T‖ + 1) := by positivity
  obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hK).1 (lt_add_of_pos_right (Metric.infDist y K) hδ)
  have hTε : ‖T‖ * (ε / (‖T‖ + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg T]
  calc Metric.infDist (T y) (T '' K) ≤ dist (T y) (T p) :=
        Metric.infDist_le_dist_of_mem (Set.mem_image_of_mem T hp)
    _ ≤ ‖T‖ * dist y p := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]; exact T.le_opNorm _
    _ ≤ ‖T‖ * (Metric.infDist y K + ε / (‖T‖ + 1)) := by gcongr
    _ ≤ ‖T‖ * Metric.infDist y K + ε := by rw [mul_add]; linarith

lemma dst_mul_le (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) (M A : Matrix n n ℂ) :
    dst x f s (M * A) ≤ opn M * dst x f s A := by
  unfold dst
  set T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) M
  have key : ∀ v : n → ℂ, (WithLp.toLp 2 ((M * A) *ᵥ v) : EuclideanSpace ℂ n) =
      T (WithLp.toLp 2 (A *ᵥ v)) := fun v => by
    rw [← Matrix.mulVec_mulVec]; rfl
  simp only [key]
  set S : Set (EuclideanSpace ℂ n) := (fun b => (WithLp.toLp 2 (A *ᵥ f b) : EuclideanSpace ℂ n)) '' s
  have himg : (fun b => T (WithLp.toLp 2 (A *ᵥ f b))) '' s = T '' S := (Set.image_image _ _ _).symm
  rw [himg]

  have hsub : T '' (Submodule.span ℂ S : Set _) ⊆ (Submodule.span ℂ (T '' S) : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.apply_mem_span_image_of_mem_span (T : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) hp
  calc Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (Submodule.span ℂ (T '' S) : Set _)
      ≤ Metric.infDist (T (WithLp.toLp 2 (A *ᵥ x))) (T '' (Submodule.span ℂ S : Set _)) :=
        Metric.infDist_le_infDist_of_subset hsub ⟨T 0, 0, Submodule.zero_mem _, rfl⟩
    _ ≤ ‖T‖ * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) :=
        infDist_image_le_opNorm_mul T _ _ ⟨0, Submodule.zero_mem _⟩
    _ = opn M * Metric.infDist (WithLp.toLp 2 (A *ᵥ x)) (Submodule.span ℂ S : Set _) := rfl

lemma dst_inv_continuousOn [Nonempty n] (x : n → ℂ) (f : ι → n → ℂ) (s : Set ι) :
    ContinuousOn (fun g : Matrix n n ℂ => dst x f s g⁻¹) {g | IsUnit g.det} := by
  set U : Set (Matrix n n ℂ) := {g | IsUnit g.det}

  have hinv : ContinuousOn (fun g : Matrix n n ℂ => g⁻¹) U := by
    have h : (fun g : Matrix n n ℂ => g⁻¹) = fun g => (g.det)⁻¹ • g.adjugate := by
      funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h]
    exact (continuous_id.matrix_det.continuousOn.inv₀ fun (g : Matrix n n ℂ) (hg : g ∈ U) => (show IsUnit g.det from hg).ne_zero).smul
      continuous_id.matrix_adjugate.continuousOn
  intro g0 hg0
  have hg0' : IsUnit g0.det := hg0
  set a0 := dst x f s g0⁻¹

  have hu : Filter.Tendsto (fun g => opn (g⁻¹ * g0)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : ContinuousWithinAt (fun g => opn (g⁻¹ * g0)) U g0 :=
      opn_cont.continuousAt.comp_continuousWithinAt ((hinv g0 hg0).mul continuousWithinAt_const)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.tendsto
    rwa [h1] at this
  have hv : Filter.Tendsto (fun g => opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds 1) := by
    have hc : Continuous fun g => opn (g0⁻¹ * g) := opn_cont.comp (continuous_const.mul continuous_id)
    have h1 : opn (g0⁻¹ * g0) = 1 := by rw [Matrix.nonsing_inv_mul _ hg0', opn_one]
    have := hc.continuousWithinAt (s := U) (x := g0) |>.tendsto
    rwa [h1] at this
  have hup : ∀ g ∈ U, dst x f s g⁻¹ ≤ opn (g⁻¹ * g0) * a0 := by
    intro g _
    have h := dst_mul_le x f s (g⁻¹ * g0) g0⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ hg0', mul_one] at h
  have hlow : ∀ g ∈ U, a0 ≤ opn (g0⁻¹ * g) * dst x f s g⁻¹ := by
    intro g hg
    have h := dst_mul_le x f s (g0⁻¹ * g) g⁻¹
    rwa [mul_assoc, Matrix.mul_nonsing_inv _ (show IsUnit g.det from hg), mul_one] at h
  have hpos : ∀ᶠ g in nhdsWithin g0 U, 0 < opn (g0⁻¹ * g) := hv.eventually (lt_mem_nhds one_pos)
  have hL : Filter.Tendsto (fun g => a0 / opn (g0⁻¹ * g)) (nhdsWithin g0 U) (nhds a0) := by
    have := (tendsto_const_nhds (x := a0)).div hv one_ne_zero
    rwa [div_one] at this
  have hR : Filter.Tendsto (fun g => opn (g⁻¹ * g0) * a0) (nhdsWithin g0 U) (nhds a0) := by
    have := hu.mul_const a0
    rwa [one_mul] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hR ?_ (eventually_nhdsWithin_of_forall hup)
  filter_upwards [hpos, eventually_nhdsWithin_of_forall hlow] with g hg1 hg2
  rw [div_le_iff₀ hg1, mul_comm]
  exact hg2

theorem lenA_continuousOn : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    0 < Formalism.QuantumDeterminants.Tz k r z → ∀ a, ContinuousOn (fun g => lenA k r z g a) (GG k r) := by
  intro k r z _ _ a

  have hsub : GG k r ⊆ {g : Mx k r | IsUnit g.det} := by
    intro g hg
    have h1 : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
    have hdet : (Formalism.QuantumDeterminants.Hpk k r).det * (Formalism.QuantumDeterminants.Hpk k r).det = 1 := by
      rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    show IsUnit g.det
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at h2
    rw [← h2, mul_zero] at hdet
    exact zero_ne_one hdet
  exact (dst_inv_continuousOn (Formalism.QuantumDeterminants.fvec k r z a) (Formalism.QuantumDeterminants.fvec k r z) {b | b < a}).mono hsub

end GlobalTheory.LengthCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HermCmpWedgeEqDet
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopMinorWedge

theorem det_mul_sub {n l : ℕ} (A : Matrix (Fin l) (Fin n) ℂ) (B : Matrix (Fin n) (Fin l) ℂ) :
    (A * B).det = ∑ I : BranchingSupport.Sub n l, (A.submatrix id (I.1.orderEmbOfFin I.2)).det *
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det := by
  rw [GlobalTheory.det_mul_eq_sum_minors]
  exact Fintype.sum_equiv
    (⟨fun S => ⟨S.1, S.2⟩, fun S => ⟨S.1, S.2⟩, fun _ => rfl, fun _ => rfl⟩ :
      Set.powersetCard (Fin n) l ≃ BranchingSupport.Sub n l) _ _ (fun _ => rfl)

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := det_mul_sub (g.submatrix (I.1.orderEmbOfFin I.2) id) (Matrix.of fun c b => f b c)
  have h2 : BranchingSupport.wedge (fun b => g *ᵥ f b) I =
      (g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun c b => f b c)).det := rfl
  rw [h2, h]
  rfl

theorem star_wedge_dot {n l : ℕ} (f f' : Fin l → Fin n → ℂ) :
    star (BranchingSupport.wedge f) ⬝ᵥ BranchingSupport.wedge f' = (Matrix.of fun a b => star (f a) ⬝ᵥ f' b).det := by
  have h := det_mul_sub (Matrix.of fun a c => star (f a c)) (Matrix.of fun c b => f' b c)
  have h2 : (Matrix.of fun a b => star (f a) ⬝ᵥ f' b) =
      (Matrix.of fun a c => star (f a c)) * (Matrix.of fun c b => f' b c) := rfl
  rw [h2, h]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [Pi.star_apply, BranchingSupport.wedge, ← Matrix.det_conjTranspose]
  rfl

theorem herm_cmp_wedge_eq_det : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (cmp (r + 1) g *ᵥ wedge (Formalism.QuantumDeterminants.fvec k r z'))
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (Formalism.QuantumDeterminants.Zhat k r z z' g).det := by
  intro k r z z' g
  rw [Formalism.QuantumDeterminants.herm, cmp_mulVec_wedge, cmp_mulVec_wedge, star_wedge_dot]
  rfl

end GlobalTheory.TopMinorWedge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DominantRootSums
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DominantRootSums

private lemma sum_index_mul_root_eq_sub' {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, ((i : ℕ) : ℝ) * _root_.PI.UpqRep.root a b i = ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ) := by
  simp [_root_.PI.UpqRep.root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

theorem _root_.GlobalTheory.DominantRootSums.not_cDom_add_root : ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (a b : Fin n), a < b →
    ¬ _root_.PI.UpqRep.CDom ε (Λ + _root_.PI.UpqRep.root a b) Λ := by
  intro n ε Λ a b hab hdom
  unfold _root_.PI.UpqRep.CDom at hdom
  obtain ⟨c, hc, hsum⟩ := hdom
  rw [show Λ - (Λ + _root_.PI.UpqRep.root a b) = -_root_.PI.UpqRep.root a b by abel] at hsum
  have h1 := congrArg (fun v : Fin n → ℝ => ∑ i : Fin n, ((i : ℕ) : ℝ) * v i) hsum
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, sum_index_mul_root_eq_sub'] at h1
  have hR : ∑ i : Fin n, ((i : ℕ) : ℝ) * (∑ a', ∑ b', (c a' b' : ℝ) • _root_.PI.UpqRep.root a' b') i
      = ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [← sum_index_mul_root_eq_sub', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hR] at h1
  have hle : ∑ a', ∑ b', (c a' b' : ℝ) * (((a' : ℕ) : ℝ) - ((b' : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun a' _ => Finset.sum_nonpos fun b' _ => ?_
    by_cases h0 : c a' b' = 0
    · simp [h0]
    · have hlt : ((a' : ℕ) : ℝ) < ((b' : ℕ) : ℝ) := by exact_mod_cast (hc a' b' h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

end GlobalTheory.DominantRootSums
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLe
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem norm_sq_integral_inner_smul_le (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ)
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hp : AEStronglyMeasurable ph ν) :
    ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤
      (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  set F : Ω → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ‖f x‖ₑ with hF
  set G : Ω → ℝ≥0∞ := fun x => ‖g x‖ₑ with hG
  have hFm : AEMeasurable F ν := hp.enorm.mul hf.enorm
  have hGm : AEMeasurable G ν := hg.enorm
  have h1 : ‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ₑ ≤ ∫⁻ x, (F * G) x ∂ν := by
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    have h : ‖⟪f x, ph x • g x⟫_ℂ‖ ≤ ‖ph x‖ * ‖f x‖ * ‖g x‖ := by
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [norm_smul]; ring
    have := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ofReal_norm_eq_enorm,
      ofReal_norm_eq_enorm] at this
    exact this
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hFm hGm
  have e1 : (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) = ∫⁻ x, F x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm_eq_enorm, ofReal_norm_eq_enorm, ENNReal.rpow_two]
  have e2 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν) = ∫⁻ x, G x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm, ENNReal.rpow_two]
  rw [e1, e2, ENNReal.ofReal_pow (by positivity), ofReal_norm_eq_enorm]
  refine (pow_le_pow_left' (h1.trans h2) 2).trans (le_of_eq ?_)
  have k : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, k, k]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSqIntegralInnerWeightLeStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sq_integral_inner_weight_le : ∀ (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ), AEStronglyMeasurable f ν → AEStronglyMeasurable g ν → AEStronglyMeasurable ph ν → ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤ (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  first | exact @GlobalTheory.norm_sq_integral_inner_smul_le | exact GlobalTheory.norm_sq_integral_inner_smul_le | (intros; apply GlobalTheory.norm_sq_integral_inner_smul_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem factorisation_of_two_partial_integrations : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  intro T Wp Wq _ _ _ _ _ _ l l' J A Bb hA hB hJA hJB
  by_cases h1 : ∀ x, l x = 0
  · refine ⟨0, fun x y X => ?_⟩
    ext c
    have h0 := hA y 0 c 0
    rw [hJA, h1 x, map_zero]
    simpa using h0
  by_cases h2 : ∀ y, l' y = 0
  · refine ⟨0, fun x y X => ?_⟩
    ext c
    have h0 := hB x 0 c 0
    rw [hJB, h2 y, map_zero]
    simpa using h0
  push Not at h1 h2
  obtain ⟨x₀, hx⟩ := h1
  obtain ⟨y₀, hy⟩ := h2
  have hadj : ∀ (a : Wq) (b v : Wp),
      ContinuousLinearMap.adjoint ((innerSL ℂ a).smulRight b) v = ⟪b, v⟫_ℂ • a := by
    intro a b v
    refine ext_inner_right ℂ fun w => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
      inner_conj_symm]
    ring
  have hp : ⟪l x₀, l x₀⟫_ℂ ≠ 0 := fun h => hx (inner_self_eq_zero.mp h)
  have hq : ⟪l' y₀, l' y₀⟫_ℂ ≠ 0 := fun h => hy (inner_self_eq_zero.mp h)
  have key : ∀ y a c, A y a c = (⟪a, l' y⟫_ℂ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) • Bb x₀ (l x₀) c := by
    intro y a c
    have e1 := hJA x₀ y ((innerSL ℂ a).smulRight (l x₀)) c
    have e2 := hJB x₀ y ((innerSL ℂ a).smulRight (l x₀)) c
    rw [hadj, hA] at e1
    rw [ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, e1] at e2
    have hs : star ⟪l x₀, l x₀⟫_ℂ = ⟪l x₀, l x₀⟫_ℂ := inner_conj_symm (𝕜 := ℂ) _ _
    rw [hs] at e2
    rw [mul_comm, mul_smul, ← e2, smul_smul, inv_mul_cancel₀ hp, one_smul]
  refine ⟨((⟪l' y₀, l' y₀⟫_ℂ)⁻¹ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) •
    J x₀ y₀ ((innerSL ℂ (l' y₀)).smulRight (l x₀)), fun x y X => ?_⟩
  ext c
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hJB x₀,
    ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, hJA, key,
    ContinuousLinearMap.adjoint_inner_left, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneousStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorisation_of_conjHomogeneous_and_homogeneous : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  first | exact @GlobalTheory.factorisation_of_two_partial_integrations | exact GlobalTheory.factorisation_of_two_partial_integrations | (intros; apply GlobalTheory.factorisation_of_two_partial_integrations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummand
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem dualTens_casimir_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (x : Fin n → M) (i : Fin n) :
    ∑ a, ∑ b, dualTens E a b (dualTens E b a x) i
      = Formalism.REAL.Cas E (x i) + (2 : ℂ) • splitCas E x i + (n : ℂ) • x i := by
  have h : ∀ a b, dualTens E a b (dualTens E b a x) i
      = E a b (E b a (x i)) - (if i = a then E a b (x b) else 0) - (if i = b then E b a (x a) else 0)
        + (if i = b then x b else 0) := by
    intro a b
    simp only [dualTens, map_sub, if_true]
    split_ifs <;> (try simp only [map_zero]) <;> abel
  have h1 : ∑ a, ∑ b, (if i = a then E a b (x b) else 0) = ∑ c, E i c (x c) := by
    rw [Finset.sum_comm]; simp
  have h2 : ∑ a, ∑ b, (if i = b then E b a (x a) else 0) = ∑ c, E i c (x c) := by
    simp
  have h3 : ∑ _a : Fin n, ∑ b, (if i = b then x b else 0) = (n : ℂ) • x i := by
    simp [Nat.cast_smul_eq_nsmul]
  have h4 : ∑ a, ∑ b, E a b (E b a (x i)) = Formalism.REAL.Cas E (x i) := by
    simp [Formalism.REAL.Cas, LinearMap.sum_apply]
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3, h4, splitCas, two_smul]
  abel

theorem casG_sub_single {n : ℕ} (mu : Fin n → ℝ) (s : Fin n) :
    casG (mu - Pi.single s 1) = casG mu - 2 * mu s + 1 := by
  have h : ∀ a, (mu - Pi.single s (1 : ℝ) : Fin n → ℝ) a ^ 2
      = mu a ^ 2 + (if a = s then - 2 * mu s + 1 else 0) := by
    intro a
    by_cases ha : a = s
    · subst ha; simp; ring
    · simp [ha]
  simp only [casG, h, Finset.sum_add_distrib]
  simp
  ring

theorem splitCas_on_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (Ns : Type) [AddCommGroup Ns] [Module ℂ Ns] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (F : Fin n → Fin n → Module.End ℂ Ns) (io : Ns →ₗ[ℂ] (Fin n → M)) (mu : Fin n → ℝ) (s : Fin n), (∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w) → (∀ y, Formalism.REAL.Cas F y = (casG (mu - Pi.single s 1) : ℂ) • y) → (∀ a b y, io (F a b y) = dualTens E a b (io y)) → ∀ y, splitCas E (io y) = ((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y := by
  intro M _ _ Ns _ _ n E F io mu s hE hF hio y
  funext i
  have h1 : io (Formalism.REAL.Cas F y) i = ∑ a, ∑ b, dualTens E a b (dualTens E b a (io y)) i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.REAL.Cas, LinearMap.sum_apply, map_sum, Finset.sum_apply, hio]
  rw [dualTens_casimir_apply, hE, hF, map_smul, casG_sub_single, Pi.smul_apply] at h1
  have h2 : (2 : ℂ) • splitCas E (io y) i
      = (2 : ℂ) • (((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y i) := by
    have h3 : (2 : ℂ) • splitCas E (io y) i
        = ((casG mu - 2 * mu s + 1 : ℝ) : ℂ) • io y i - (casG mu : ℂ) • io y i - (n : ℂ) • io y i := by
      rw [h1]; abel
    rw [h3, ← sub_smul, ← sub_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [Pi.smul_apply]
  exact smul_right_injective M (two_ne_zero) h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummandStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCasimir_eigenvalue_on_dualTensor_summand : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (Ns : Type) [AddCommGroup Ns] [Module ℂ Ns] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (F : Fin n → Fin n → Module.End ℂ Ns) (io : Ns →ₗ[ℂ] (Fin n → M)) (mu : Fin n → ℝ) (s : Fin n), (∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w) → (∀ y, Formalism.REAL.Cas F y = (casG (mu - Pi.single s 1) : ℂ) • y) → (∀ a b y, io (F a b y) = dualTens E a b (io y)) → ∀ y, splitCas E (io y) = ((-mu s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • io y := by
  first | exact @GlobalTheory.splitCas_on_summand | exact GlobalTheory.splitCas_on_summand | (intros; apply GlobalTheory.splitCas_on_summand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem cdom_add_lowering_word {n : ℕ} (ε : Fin n → Bool) (Λ : Fin n → ℝ)
    (w : List (Fin n × Fin n)) (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) :
    PI.UpqRep.CDom ε (Λ + Formalism.REAL.wordWeightShift w) Λ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [Formalism.REAL.wordWeightShift]⟩
  | cons p w ih =>
    obtain ⟨c, hc, he⟩ := ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    have hp := hw p List.mem_cons_self
    refine ⟨fun a b => c a b + (if a = p.2 then if b = p.1 then 1 else 0 else 0), ?_, ?_⟩
    · intro a b hab
      by_cases h0 : c a b = 0
      · by_cases h1 : a = p.2
        · by_cases h2 : b = p.1
          · subst h1; subst h2; exact ⟨hp.2, hp.1.symm⟩
          · simp [h0, h2] at hab
        · simp [h0, h1] at hab
      · exact hc a b h0
    · have h1 : ∑ a, ∑ b, (((if a = p.2 then if b = p.1 then 1 else 0 else 0 : ℕ) : ℝ)) •
          PI.UpqRep.root a b = PI.UpqRep.root p.2 p.1 := by
        rw [Finset.sum_eq_single p.2]
        · rw [Finset.sum_eq_single p.1]
          · simp
          · intro b _ hb; simp [hb]
          · simp
        · intro a _ ha; simp [ha]
        · simp
      simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
      rw [h1, ← he]
      simp only [Formalism.REAL.wordWeightShift, PI.UpqRep.root]
      abel

theorem weight_cdom_of_mem_kSpan :
    ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  intro k W _ _ E Λ μ x v hg hu hΛ hv hv0 hμ
  by_contra hne
  have hk := Formalism.REAL.isUnitary_kUnit _ E hu
  have hr := Formalism.REAL.glRel_kRel (PI.UpqRep.allPos k) E hg
  rw [Formalism.REAL.compact_span_eq_lowering hr hΛ] at hv
  have key : ∀ z ∈ Formalism.REAL.lowSpan (PI.UpqRep.allPos k) E x, ⟪z, v⟫_ℂ = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := hy
      refine Formalism.REAL.compact_weight_orthogonal W k _ E _ μ _ v hk
        (Formalism.REAL.word_action_weight hr hΛ.1 w (fun q hq => (hw q hq).1)) hμ ?_
      intro heq
      exact hne (heq ▸ cdom_add_lowering_word _ Λ w hw)
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul c y _ hy => rw [inner_smul_left, hy, mul_zero]
  exact hv0 (inner_self_eq_zero.mp (key v hv))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpanStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  first | exact @GlobalTheory.weight_cdom_of_mem_kSpan | exact GlobalTheory.weight_cdom_of_mem_kSpan | (intros; apply GlobalTheory.weight_cdom_of_mem_kSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransport
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyTransport

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smoothOn_comp {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H J A B : Matrix (Fin n) (Fin n) ℂ} (hAB : ∀ g, gᴴ * J * g = J → (A * g * B)ᴴ * H * (A * g * B) = H)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : PI.UpqRep.SmoothOnH H f) :
    PI.PhMeasCore.SmoothOnH J (fun g => f (A * g * B)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, he⟩ := hf (A * g₀ * B) (hAB g₀ hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => A * g * B
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let L' := LinearMap.toContinuousLinearMap L
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, ?_, ?_⟩
  · exact hF.comp L'.contDiff.contDiffOn (fun x hx => hx)
  · intro g hg hgJ
    exact he (A * g * B) hg (hAB g hgJ)

end Smooth

theorem dsig_conj {k r : ℕ} (R : Rep k r) {Q : Mx k r} (hQ : IsUnit Q) (X : Mx k r) (v : R.H) :
    PI.PhMeasCore.dsig (fun g => R.σ (Q⁻¹ * g * Q)) X v =
      PI.UpqRep.dsig (k := k) (r := r) R.σ (Q⁻¹ * X * Q) v := by
  unfold PI.PhMeasCore.dsig PI.UpqRep.dsig
  congr 1
  funext t
  have : (t : ℂ) • (Q⁻¹ * X * Q) = Q⁻¹ * ((t : ℂ) • X) * Q := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [this, Matrix.exp_conj' Q _ hQ]

theorem smooth_and_dsigC_transport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  intro k r ε R Q ⟨⟨hunit, hcay⟩, hU⟩
  have h1 : Q * Qᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  have h2 : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h2
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * Formalism.REAL.Jm ε * Q := hcay.symm
  have hc : ∀ Z : Mx k r, Q * (Qᴴ * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  constructor
  · intro v hv
    refine smoothOn_comp (H := PI.UpqRep.Hpk k r) (f := fun g => R.σ g v) ?_ hv
    intro g hg
    rw [← hcay, hinv]
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc]
    simp only [Matrix.mul_assoc] at hg'
    rw [← Matrix.mul_assoc (PI.UpqRep.Jm ε) g Q, ← Matrix.mul_assoc gᴴ _ Q, hg']
  · intro Y v
    have ht : Q⁻¹ * PI.DSInfCharCap.thetaJ ε Y * Q =
        -(Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * Y * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r) := by
      rw [hH, hinv, PI.DSInfCharCap.thetaJ]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc,
        Matrix.mul_neg, Matrix.neg_mul]
    unfold PI.DSInfCharCap.dsigC Rep.dC
    rw [dsig_conj R hunit, dsig_conj R hunit, ← ht]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

end GlobalTheory.CayleyTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsComplexDerivedActionCayleyTransportStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothVectors_complexDerivedAction_cayleyTransport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  first | exact @GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | exact GlobalTheory.CayleyTransport.smooth_and_dsigC_transport | (intros; apply GlobalTheory.CayleyTransport.smooth_and_dsigC_transport <;> assumption)
end
end
