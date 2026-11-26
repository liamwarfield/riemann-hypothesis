module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompact
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefExtendsHolomorphically
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.KHolExt

variable {n : ℕ} {ε : Fin n → Bool}

def Hol (ε : Fin n → Bool) (a : KG ε → ℂ) : Prop :=
  ∃ F : (Fin n → Fin n → ℂ) → ℂ, DifferentiableOn ℂ F {y | Matrix.of y ∈ KC ε} ∧
    ∀ k : KG ε, F (fun i j => toMK k i j) = a k

lemma Hol.const (c : ℂ) : Hol ε (fun _ => c) :=
  ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩

lemma Hol.add {a b : KG ε → ℂ} (ha : Hol ε a) (hb : Hol ε b) : Hol ε (fun k => a k + b k) := by
  obtain ⟨F, hF, hFa⟩ := ha
  obtain ⟨G, hG, hGb⟩ := hb
  refine ⟨fun y => F y + G y, hF.add hG, fun k => ?_⟩
  simp only [hFa, hGb]

lemma Hol.mul {a b : KG ε → ℂ} (ha : Hol ε a) (hb : Hol ε b) : Hol ε (fun k => a k * b k) := by
  obtain ⟨F, hF, hFa⟩ := ha
  obtain ⟨G, hG, hGb⟩ := hb
  refine ⟨fun y => F y * G y, hF.mul hG, fun k => ?_⟩
  simp only [hFa, hGb]

lemma Hol.entry (i j : Fin n) : Hol ε (fun k => toMK k i j) := by
  refine ⟨fun y => y i j, ?_, fun k => rfl⟩
  have hd : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => y i j) := by fun_prop
  exact hd.differentiableOn

lemma differentiable_det (f : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, Differentiable ℂ (fun y => f y i j)) : Differentiable ℂ (fun y => (f y).det) := by
  simp only [Matrix.det_apply']
  have hp : ∀ σ : Equiv.Perm (Fin n), Differentiable ℂ (fun y => ∏ i, f y (σ i) i) := fun σ => by
    have h : Differentiable ℂ (∏ i, (fun y : Fin n → Fin n → ℂ => f y (σ i) i)) :=
      Finset.prod_induction (fun i => (fun y : Fin n → Fin n → ℂ => f y (σ i) i))
        (fun g => Differentiable ℂ g) (fun a b ha hb => ha.mul hb) (differentiable_const 1)
        (fun i _ => hf (σ i) i)
    have e : (fun y => ∏ i, f y (σ i) i) = ∏ i, (fun y => f y (σ i) i) := by
      funext y
      rw [Finset.prod_apply]
    rw [e]
    exact h
  have hs := Differentiable.sum (𝕜 := ℂ) (u := Finset.univ)
    (A := fun (σ : Equiv.Perm (Fin n)) (y : Fin n → Fin n → ℂ) => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i)
    (fun σ _ => (differentiable_const (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul (hp σ))
  have e : (fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i) =
      ∑ σ : Equiv.Perm (Fin n), (fun y => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i) := by
    funext y
    rw [Finset.sum_apply]
  rw [e]
  exact hs

lemma toMK_inv (k : KG ε) : toMK k⁻¹ = star (toMK k) := by
  have hu : toMK k * star (toMK k) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 ((mem_KG ε (k : UJ ε)).1 k.2).1
  have hl : toMK k⁻¹ * toMK k = 1 := Units.inv_mul ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [hu, mul_one]
    _ = star (toMK k) := by rw [← mul_assoc, hl, one_mul]

lemma toMK_mul (g k : KG ε) : toMK (g * k) = toMK g * toMK k := rfl

lemma Hol.conjEntry (i j : Fin n) : Hol ε (fun k => star (toMK k i j)) := by
  refine ⟨fun y => ((Matrix.of y).det)⁻¹ * (Matrix.of y).adjugate j i, ?_, fun k => ?_⟩
  · have hdet : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) :=
      differentiable_det (fun y => Matrix.of y) (fun a b => by simp only [Matrix.of_apply]; fun_prop)
    have hadj : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate j i) := by
      simp only [Matrix.adjugate_apply]
      exact differentiable_det _ (fun a b => by
        simp only [Matrix.updateRow_apply, Matrix.of_apply]
        split_ifs <;> fun_prop)
    intro y hy
    have hy1 : IsUnit (Matrix.of y) := by
      simp only [Set.mem_setOf_eq, KC] at hy
      exact hy.1
    have hne : (Matrix.of y).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hy1).ne_zero
    exact ((hdet y).inv hne).differentiableWithinAt.mul (hadj y).differentiableWithinAt
  · have hu : toMK k * star (toMK k) = 1 :=
      Matrix.mem_unitaryGroup_iff.1 ((mem_KG ε (k : UJ ε)).1 k.2).1
    have hinv : (toMK k)⁻¹ = star (toMK k) := Matrix.inv_eq_right_inv hu
    have key : (toMK k)⁻¹ j i = ((toMK k).det)⁻¹ * (toMK k).adjugate j i := by
      rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
    change ((toMK k).det)⁻¹ * (toMK k).adjugate j i = star (toMK k i j)
    rw [← key, hinv, Matrix.star_apply]

def Sep (ε : Fin n → Bool) (p : KG ε → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → KG ε → ℂ) (b : ι → C(KG ε, ℂ)), (∀ i, Hol ε (a i)) ∧
    ∀ g k, p (g⁻¹ * k) = ∑ i, a i g * b i k

lemma Sep.const (c : ℂ) : Sep ε (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ => ContinuousMap.const _ 1, fun _ => Hol.const c,
    fun g k => by simp⟩

lemma Sep.add {p q : KG ε → ℂ} (hp : Sep ε p) (hq : Sep ε q) : Sep ε (fun k => p k + q k) := by
  obtain ⟨ι, _, a, b, ha, hab⟩ := hp
  obtain ⟨κ, _, c, d, hc, hcd⟩ := hq
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun g k => ?_⟩
  · rintro (i | i)
    · exact ha i
    · exact hc i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hab, hcd]

lemma Sep.mul {p q : KG ε → ℂ} (hp : Sep ε p) (hq : Sep ε q) : Sep ε (fun k => p k * q k) := by
  obtain ⟨ι, _, a, b, ha, hab⟩ := hp
  obtain ⟨κ, _, c, d, hc, hcd⟩ := hq
  refine ⟨ι × κ, inferInstance, fun x g => a x.1 g * c x.2 g, fun x => b x.1 * d x.2,
    fun x => (ha x.1).mul (hc x.2), fun g k => ?_⟩
  show p (g⁻¹ * k) * q (g⁻¹ * k) = _
  rw [hab, hcd, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousMap.mul_apply]
  ring

lemma isEmb (ε : Fin n → Bool) : Topology.IsEmbedding (fun k : KG ε => toMK k) := by
  have hc : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hi : Function.Injective (fun k : KG ε => toMK k) := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  exact (hc.isClosedEmbedding hi).isEmbedding

def ent (ε : Fin n → Bool) (i j : Fin n) : C(KG ε, ℂ) :=
  ⟨fun k => toMK k i j, (continuous_apply_apply i j).comp (isEmb ε).continuous⟩

lemma Sep.entry (i j : Fin n) : Sep ε (ent ε i j) := by
  refine ⟨Fin n, inferInstance, fun l g => star (toMK g l i), fun l => ent ε l j,
    fun l => Hol.conjEntry l i, fun g k => ?_⟩
  show toMK (g⁻¹ * k) i j = ∑ l, star (toMK g l i) * toMK k l j
  rw [toMK_mul, toMK_inv, Matrix.mul_apply]
  simp only [Matrix.star_apply]

lemma Sep.conjEntry (i j : Fin n) : Sep ε (star (ent ε i j) : C(KG ε, ℂ)) := by
  refine ⟨Fin n, inferInstance, fun l g => toMK g l i, fun l => star (ent ε l j),
    fun l => Hol.entry l i, fun g k => ?_⟩
  show star (toMK (g⁻¹ * k) i j) = ∑ l, toMK g l i * star (toMK k l j)
  rw [toMK_mul, toMK_inv, Matrix.mul_apply, star_sum]
  simp only [Matrix.star_apply, star_mul', star_star]

def sepAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | Sep ε p ∧ Sep ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨hp.1.mul hq.1, by
    rw [star_mul']; exact hp.2.mul hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨hp.1.add hq.1, by
    rw [star_add]; exact hp.2.add hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact Sep.const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact Sep.const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma sepAlg_dense (ε : Fin n → Bool) : (sepAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy ((isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hcon
    push_neg at hcon
    exact hne (Matrix.ext hcon)
  have hmem : ent ε i j ∈ sepAlg ε := ⟨Sep.entry i j, Sep.conjEntry i j⟩
  exact ⟨_, ⟨ent ε i j, hmem, rfl⟩, hij⟩

private theorem integrable_of_continuous_isFiniteMeasure {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

lemma eq_zero_of_orth (φ : C(KG ε, ℂ))
    (h : ∀ p : C(KG ε, ℂ), Sep ε p → ∫ k, p k * φ k ∂(muK ε) = 0) : φ = 0 := by
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ k, p k * φ k ∂(muK ε)
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_of_continuous_isFiniteMeasure (p.continuous.mul φ.continuous))
          (integrable_of_continuous_isFiniteMeasure (q.continuous.mul φ.continuous))
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hL : Continuous L := by
    refine AddMonoidHomClass.continuous_of_bound L (∫ k, ‖φ k‖ ∂(muK ε)) fun p => ?_
    calc ‖L p‖ = ‖∫ k, p k * φ k ∂(muK ε)‖ := rfl
      _ ≤ ∫ k, ‖p‖ * ‖φ k‖ ∂(muK ε) := by
          refine norm_integral_le_of_norm_le ((integrable_of_continuous_isFiniteMeasure φ.continuous).norm.const_mul _) ?_
          refine Filter.Eventually.of_forall fun k => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (p.norm_coe_le_norm k) (norm_nonneg _)
      _ = (∫ k, ‖φ k‖ ∂(muK ε)) * ‖p‖ := by rw [integral_const_mul, mul_comm]
  have hcl : IsClosed {p : C(KG ε, ℂ) | L p = 0} := isClosed_eq hL continuous_const
  have hsub : ((sepAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {p | L p = 0} := by
    intro p hp
    exact h p hp.1
  have hall : ∀ p : C(KG ε, ℂ), L p = 0 := by
    intro p
    have hp : p ∈ closure ((sepAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by
      rw [← StarSubalgebra.topologicalClosure_coe, SetLike.mem_coe, sepAlg_dense]
      exact StarSubalgebra.mem_top
    exact closure_minimal hsub hcl hp
  have h1 : ∫ k, (star φ) k * φ k ∂(muK ε) = 0 := hall (star φ)
  have e : ∀ k, (star φ) k * φ k = ((‖φ k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [ContinuousMap.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp only [e, integral_ofReal] at h1
  have hreal : ∫ k, ‖φ k‖ ^ 2 ∂(muK ε) = 0 := by exact_mod_cast h1
  have hae : (fun k => ‖φ k‖ ^ 2) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖φ k‖)
      (integrable_of_continuous_isFiniteMeasure (φ.continuous.norm.pow 2))).1 hreal
  have heq : (fun k => ‖φ k‖ ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) (φ.continuous.norm.pow 2) continuous_const).1 hae
  ext k
  have hk := congrFun heq k
  simpa using hk

end GlobalTheory.KHolExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorant
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec.PhMajProof

theorem local_integrable (n : ℕ) (ε : Fin n → Bool) (h s : ℝ) (hs : 0 ≤ s)
    (hyp : rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) :
    Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  rcases hyp with h0 | hlt
  · have key : (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) =
        fun g : UJ ε => decE (rkR ε) 0 (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      funext g
      rw [GlobalTheory.Count.Majorant.dOp_eq_zero ε h0 g]
      simp [decE]
    rw [key]
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε 0 s le_rfl (Or.inl h0)
  · have hh : 0 ≤ h := by
      have : 0 ≤ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) :=
        mul_nonneg (by positivity) (add_nonneg hs (by positivity))
      linarith
    exact GlobalTheory.Count.Majorant.majorant_integrable n ε h s hh (Or.inr hlt)

theorem phMaj : PhMaj := by
  intro B d h hds hloc
  have hd : ∀ v, 0 < d v := fun v => (hds v).2.2.2.1
  have hdp : 0 ≤ ∏ v, d v := Finset.prod_nonneg fun v _ => (hd v).le
  have hcont : ∀ v, Continuous fun g : B.I.Ginf => B.σ v (uMat (g v)) (B.w v) := by
    intro v
    have hon := (hds v).2.1.2.2.1.2.2 (B.w v)
    refine hon.comp_continuous ?_ ?_
    · unfold uMat
      exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
    · intro g
      exact (g v).2
  refine ⟨?_, ?_, ?_⟩
  · unfold ph
    exact continuous_const.mul (continuous_star.comp
      (continuous_finsetProd _ fun v _ => continuous_const.inner (hcont v)))
  · intro g
    unfold ph majPh
    rw [norm_mul, norm_star, norm_prod, Complex.norm_real, Real.norm_of_nonneg hdp]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hloc v (g v)) hdp
  · intro s hs hyp
    have key : (fun g => majPh B d h g * Real.exp (s * dSum B.I g)) = fun g : B.I.Ginf =>
        (∏ v, d v) * ∏ v, (decE (rkR (B.I.ε v)) h (dOp (uMat (g v))) * Real.exp (s * dOp (uMat (g v)))) := by
      funext g
      unfold majPh dSum
      rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]
      ring
    rw [key]
    unfold muInf
    have hprod : Integrable (fun x : (∀ v, UJ (B.I.ε v)) => ∏ v,
        (decE (rkR (B.I.ε v)) h (dOp (uMat (x v))) * Real.exp (s * dOp (uMat (x v)))))
        (Measure.pi fun v => muG (B.I.ε v)) :=
      Integrable.fintype_prod_dep fun v => local_integrable B.I.n (B.I.ε v) h s hs (hyp v)
    exact hprod.const_mul _

end GlobalTheory.Dec.PhMajProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesCoefficientIntegrableMajorantStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_coefficient_integrable_majorant : PhMaj := by
  first | exact @GlobalTheory.Dec.PhMajProof.phMaj | exact GlobalTheory.Dec.PhMajProof.phMaj | (intros; apply GlobalTheory.Dec.PhMajProof.phMaj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWN
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWN
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem IsClosedSub.isMatGroup_of_unitary {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S := by
  obtain ⟨hG, hcl, h1, hmul, hinv⟩ := hS
  refine ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ?_⟩⟩

  have e : aᴴ * Hpk k r * a = Hpk k r := hG ha
  have hH := Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r
  have hd := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hdet : IsUnit a.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hd
    exact hH.ne_zero hd.symm
  exact Matrix.mul_nonsing_inv a hdet

theorem map_invM_eq {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hR : ∀ s ∈ S, μ.map (rmulM s) = μ) : μ.map invM = μ := by
  have hL : PI.IsHaarOnM S μ := hμ
  have hR' : PI.IsRightInvM S μ := hR
  ext B hB
  rw [Measure.map_apply measurable_invM hB]

  have h := GlobalTheory.HaarInversion.lintegral_inv_eq _ S μ hS hL hR' (B.indicator 1)
    (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB] at h
  rw [← h, ← lintegral_indicator_one (measurable_invM hB)]
  rfl

theorem rightInv_of_multiple {S : Set (Mat k r)} (hS : PI.IsMatGroup S) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn S μ) (hν : PI.IsHaarOnM S ν) (hR : PI.IsRightInvM S ν) :
    ∀ s ∈ S, μ.map (rmulM s) = μ := by
  intro s hs
  have hL : PI.IsHaarOnM S μ := hμ

  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S ν hS hν).1 μ hL
  have hνs : ν.map (rmulM s) = ν := hR s hs
  rw [hc, Measure.map_smul, hνs]
  exact (continuous_rmulM s).measurable.aemeasurable

private theorem exists_isHaarOnM_of_isMatGroup {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : PI.IsMatGroup G) :
    ∃ μ : Measure (PI.MtM m), PI.IsHaarOnM G μ := by
  have he := GlobalTheory.MatHaar.inc_memb (G := G) (hG := hG)
  refine ⟨(GlobalTheory.MatHaar.haar0 hG).map GlobalTheory.MatHaar.inc, he.sigmaFinite_map, ?_, ?_, ?_⟩
  · intro h0
    rw [Measure.map_eq_zero_iff he.measurable.aemeasurable] at h0
    exact (NeZero.ne (GlobalTheory.MatHaar.haar0 hG)) h0
  · rw [he.map_apply]
    have : (GlobalTheory.MatHaar.inc (G := G) (hG := hG)) ⁻¹' {x | Matrix.of x ∉ G} = ∅ := by
      ext g
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact GlobalTheory.MatHaar.inc_mem g
    rw [this, measure_empty]
  · intro a ha
    let g0 : GlobalTheory.MatHaar.Grp G hG := ⟨a, ha⟩
    have hcomp : PI.lmulQ a ∘ GlobalTheory.MatHaar.inc (G := G) (hG := hG) =
        GlobalTheory.MatHaar.inc ∘ (fun g => g0 * g) := by
      funext g
      exact (GlobalTheory.MatHaar.inc_mul g0 g).symm
    rw [Measure.map_map (GlobalTheory.MatHaar.lmulQ_cont a).measurable he.measurable, hcomp,
      ← Measure.map_map he.measurable (measurable_const_mul g0), map_mul_left_eq_self]

theorem unimodular_S_N_UW : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ μ : Measure (Mt k r), (IsHaarOn (Sset k r z) μ → IsUnimod (Sset k r z) μ) ∧ (IsHaarOn (Nset k r) μ → IsUnimod (Nset k r) μ ∧ ∀ h ∈ UWset k r z, μ.map (conjM h) = μ) ∧ (IsHaarOn (UWset k r z) μ → IsUnimod (UWset k r z) μ ∧ μ Set.univ < ⊤) := by
  intro k r z hz hT μ
  obtain ⟨-, hNc, hWc, -, -⟩ := closedSub_groups k r z hz hT
  have hN := hNc.isMatGroup_of_unitary
  have hW := hWc.isMatGroup_of_unitary
  obtain ⟨μN0, hμN0⟩ := exists_isHaarOnM_of_isMatGroup hN
  obtain ⟨μW0, hμW0⟩ := exists_isHaarOnM_of_isMatGroup hW
  refine ⟨fun hμ => ?_, fun hμ => ?_, fun hμ => ?_⟩
  ·
    obtain ⟨hSg, -, hSH, hSR⟩ := GlobalTheory.muSof_isHaar k r z μW0 μN0 hz hT hμW0 hμN0
    have hR := rightInv_of_multiple hSg hμ hSH hSR
    exact ⟨hR, map_invM_eq hSg hμ hR⟩
  · obtain ⟨-, -, hNR, -, hconj⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μW0 μ hz hT hμW0 hμ
    have hR : ∀ s ∈ Nset k r, μ.map (rmulM s) = μ := hNR
    exact ⟨⟨hR, map_invM_eq hN hμ hR⟩, fun h hh => hconj h hh⟩
  · obtain ⟨hWR, hfin, -, -, -⟩ :=
      GlobalTheory.UnipotentRadicalHaar.unimodular_normal k r z μ μN0 hz hT hμ hμN0
    have hR : ∀ s ∈ UWset k r z, μ.map (rmulM s) = μ := hWR
    exact ⟨⟨hR, map_invM_eq hW hμ hR⟩, measure_lt_top μ _⟩

end GlobalTheory.SgInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_besselSubgroups_UW_N : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → ∀ μ : Measure (Mt k r), (IsHaarOn (Sset k r z) μ → IsUnimod (Sset k r z) μ) ∧ (IsHaarOn (Nset k r) μ → IsUnimod (Nset k r) μ ∧ ∀ h ∈ UWset k r z, μ.map (conjM h) = μ) ∧ (IsHaarOn (UWset k r z) μ → IsUnimod (UWset k r z) μ ∧ μ Set.univ < ⊤) := by
  first | exact @GlobalTheory.SgInf.unimodular_S_N_UW | exact GlobalTheory.SgInf.unimodular_S_N_UW | (intros; apply GlobalTheory.SgInf.unimodular_S_N_UW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizeProperties
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.CountSteps

section Abstract

variable {R V E : Type} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ρ : V →+ E} {L : Submodule R V}

theorem strict_eq (hL : IsLat ρ L) (θ : ℝ) :
    ∃ θ₀, θ < θ₀ ∧ ∀ θ', θ < θ' → θ' ≤ θ₀ →
      sSup {N : Submodule R V | N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} = hnStep ρ L θ' := by

  obtain ⟨t, ht, hsup⟩ :=
    finSup R V E ρ L {N | N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} hL (fun N hN => hN.1)
  obtain ⟨θ₀, hθ₀, hle⟩ : ∃ θ₀, θ < θ₀ ∧ ∀ N ∈ t, θ₀ ≤ muMin ρ N := by
    rcases t.eq_empty_or_nonempty with h | h
    · exact ⟨θ + 1, by linarith, by simp [h]⟩
    · obtain ⟨N₀, hN₀, hmin⟩ := t.exists_min_image (fun N => muMin ρ N) h
      exact ⟨muMin ρ N₀, (ht hN₀).2.2, hmin⟩
  refine ⟨θ₀, hθ₀, fun θ' h1 h2 => le_antisymm ?_ ?_⟩
  · rw [hsup]
    unfold hnStep
    refine Finset.sup_le fun N hN => ?_
    exact le_sSup ⟨(ht hN).1, (ht hN).2.1, h2.trans (hle N hN)⟩
  · unfold hnStep
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, lt_of_lt_of_le h1 hN.2.2⟩

private lemma zl_mono' {A B : Submodule R V} (h : A ≤ B) : zl ρ A ≤ zl ρ B := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := hy
  exact ⟨a, h ha, rfl⟩

theorem isSat_of_le {S N : Submodule R V} (hS : IsSat ρ L S) (h1 : S ≤ N) (h2 : N ≤ L) :
    IsSat ρ N S := by
  unfold IsSat Formalism.F.IsSaturated at *
  exact ⟨h1, zl_mono' h1, fun y hy hspan => hS.2.2 y (zl_mono' h2 hy) hspan⟩

theorem quot_slope_lt (hL : IsLat ρ L) (θ : ℝ) {N : Submodule R V} (h1 : hnStep ρ L θ < N) (h2 : N ≤ L) :
    Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ))) < θ := by
  obtain ⟨hsat, -, -, hmax⟩ := hnStep_spec R V E ρ L hL θ
  obtain ⟨hsub, -, hsatEq, -, -, -, -, -⟩ := satBasic R V E ρ L hL
  obtain ⟨-, -, -, -, -, -, -, hq⟩ := satBasic R V E ρ N (hsub N h2)
  obtain ⟨hrk, hrkle, hdeg⟩ := hq _ (isSat_of_le hsat h1.le h2)

  have hne : rk ρ (hnStep ρ L θ) ≠ rk ρ N := fun h => h1.ne (hsatEq _ _ hsat h1.le h2 h.symm).symm
  have hlt : (rk ρ (hnStep ρ L θ) : ℝ) < rk ρ N := by exact_mod_cast lt_of_le_of_ne hrkle hne
  have key := hmax N h1 h2
  unfold Formalism.F.slope
  rw [hrk, hdeg, Nat.cast_sub hrkle, div_lt_iff₀ (by linarith)]
  exact key

theorem step_eq_bot (hL : IsLat ρ L) (h0 : L ≠ ⊥) (θ : ℝ) : hnStep ρ L θ = ⊥ ↔ muMax ρ L < θ := by
  obtain ⟨hsat, hmin, hcont, -⟩ := hnStep_spec R V E ρ L hL θ
  obtain ⟨hsub, -, -, hrk0, -, -, -, -⟩ := satBasic R V E ρ L hL
  obtain ⟨hmaxL, -, ⟨N, hNsat, hN0, hNslope⟩, -, -⟩ := muChar R V E ρ L hL h0
  have hdegL : ∀ S : Submodule R V, S ≤ L → deg ρ S ≤ muMax ρ L * rk ρ S := (hmaxL _).1 le_rfl
  constructor
  · intro hbot
    by_contra hcon
    push Not at hcon

    have hNL : N ≤ L := hNsat.1
    obtain ⟨-, hminN, -, -, -⟩ := muChar R V E ρ N (hsub N hNL) hN0
    have hrkpos : (0 : ℝ) < rk ρ N := by
      have : rk ρ N ≠ 0 := fun h => hN0 ((hrk0 N hNL).1 h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hdegN : deg ρ N = muMax ρ L * rk ρ N := by
      have e : slope ρ N = deg ρ N / rk ρ N := rfl
      rw [e, div_eq_iff hrkpos.ne'] at hNslope
      exact hNslope
    have hmm : muMax ρ L ≤ muMin ρ N := (hminN _).2 fun S hS => by
      have := hdegL S (hS.trans hNL)
      rw [mul_sub, ← hdegN]
      linarith
    have hle := hcont N hNL hN0 (hcon.trans hmm)
    rw [hbot] at hle
    exact hN0 (le_bot_iff.mp hle)
  · intro hlt
    by_contra hne
    have hH := hmin hne
    have hHL : hnStep ρ L θ ≤ L := hsat.1
    obtain ⟨hmaxH, -, -, hm1, hm2⟩ := muChar R V E ρ _ (hsub _ hHL) hne
    have : muMax ρ (hnStep ρ L θ) ≤ muMax ρ L :=
      (hmaxH _).2 fun S hS => hdegL S (hS.trans hHL)
    linarith

end Abstract

theorem exp_le_iff {c m t : ℝ} (ht : 0 < t) : Real.exp (c - m) ≤ t ↔ c - Real.log t ≤ m := by
  rw [← Real.le_log_iff_exp_le ht]
  constructor <;> intro h <;> linarith

theorem exp_lt_iff {c m t : ℝ} (ht : 0 < t) : Real.exp (c - m) < t ↔ c - Real.log t < m := by
  rw [← Real.lt_log_iff_exp_lt ht]
  constructor <;> intro h <;> linarith

theorem steps : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  intro I x t ht
  obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
  obtain ⟨hTC, -, -, -, hw⟩ := GlobalTheory.T.autPointMajorantFrames_give_majorants I x
  have := hTC
  have hdet : ∀ w, IsUnit (frm I x w).det := fun w => (hw w).1
  set ρ := Formalism.HermitianLatticesTheory.realize (bas I) (frm I x) with hρ
  set L := lamX I x with hLdef
  have hLlat : IsLat ρ L := (plLat _ _ _ (bas I) (frm I x) hdet L hfg).1
  have : IsNoetherian (𝓞 I.E) L := isNoetherian_of_fg_of_noetherian L hfg
  have hNfg : ∀ N, N ≤ L → N.FG := fun N hN => Submodule.FG.of_le_of_isNoetherian hN
  set c : ℝ := Real.log 2 / 2 - logDisc I.E / (2 * (Module.finrank ℚ I.E : ℝ)) with hc

  have hlarge : ∀ N, N ≤ L → N ≠ ⊥ →
      largestSize (bas I) (frm I x) N = Real.exp (c - muMin ρ N) := fun N hN h0 =>
    (sizeMu _ _ _ (bas I) (frm I x) hdet N (hNfg N hN) h0).2.2.2.2.1
  have hsq : ∀ N S, N ≤ L → N ≠ ⊥ → IsSat ρ N S → S ≠ N →
      sizeQ (bas I) (frm I x) N S = Real.exp (c - Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ S))) :=
    fun N S hN h0 hS hne => (sizeMu _ _ _ (bas I) (frm I x) hdet N (hNfg N hN) h0).2.2.1 S hS hne
  set θ := c - Real.log t with hθ

  have hLe : stepLe I x t = hnStep ρ L θ := by
    unfold stepLe hnStep
    refine congrArg sSup (Set.ext fun N => ?_)
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hN, h0, hs⟩
      rw [hlarge N hN h0] at hs
      exact ⟨hN, h0, (exp_le_iff ht).1 hs⟩
    · rintro ⟨hN, h0, hs⟩
      refine ⟨hN, h0, ?_⟩
      rw [hlarge N hN h0]
      exact (exp_le_iff ht).2 hs
  have hLt : stepLt I x t = sSup {N : Submodule (𝓞 I.E) (Fin I.n → I.E) |
      N ≤ L ∧ N ≠ ⊥ ∧ θ < muMin ρ N} := by
    unfold stepLt
    refine congrArg sSup (Set.ext fun N => ?_)
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hN, h0, hs⟩
      rw [hlarge N hN h0] at hs
      exact ⟨hN, h0, (exp_lt_iff ht).1 hs⟩
    · rintro ⟨hN, h0, hs⟩
      refine ⟨hN, h0, ?_⟩
      rw [hlarge N hN h0]
      exact (exp_lt_iff ht).2 hs
  obtain ⟨θ₀, hθ₀, hstrict⟩ := strict_eq hLlat θ
  have hLt' : stepLt I x t = hnStep ρ L θ₀ := hLt.trans (hstrict θ₀ hθ₀ le_rfl)
  have hsame : ∀ θ', θ < θ' → θ' ≤ θ₀ → hnStep ρ L θ' = hnStep ρ L θ₀ := fun θ' h1 h2 =>
    (hstrict θ' h1 h2).symm.trans (hstrict θ₀ hθ₀ le_rfl)
  have hspec := hnStep_spec _ _ _ ρ L hLlat θ
  have hspec₀ := hnStep_spec _ _ _ ρ L hLlat θ₀
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hLe]; exact hspec.1
  · rw [hLt']; exact hspec₀.1
  · unfold stepLt stepLe
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.le⟩
  · intro t' htt'
    unfold stepLe stepLt
    exact sSup_le_sSup fun N hN => ⟨hN.1, hN.2.1, hN.2.2.trans_lt htt'⟩
  · intro h0
    rw [hLe] at h0 ⊢
    rw [hlarge _ hspec.1.1 h0]
    exact (exp_le_iff ht).2 (hspec.2.1 h0)
  · intro h0
    rw [hLt'] at h0 ⊢
    rw [hlarge _ hspec₀.1.1 h0]
    exact (exp_lt_iff ht).2 (lt_of_lt_of_le hθ₀ (hspec₀.2.1 h0))
  · intro N h1 h2
    rw [hLe] at h1 ⊢
    rw [hsq N _ h2 (ne_bot_of_gt h1) (isSat_of_le hspec.1 h1.le h2) h1.ne]
    have hs := quot_slope_lt hLlat θ h1 h2
    exact (Real.log_lt_iff_lt_exp ht).1 (by linarith)
  · intro N h1 h2
    rw [hLt'] at h1 ⊢
    rw [hsq N _ h2 (ne_bot_of_gt h1) (isSat_of_le hspec₀.1 h1.le h2) h1.ne]

    have key : ∀ θ', θ < θ' → θ' ≤ θ₀ →
        Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ₀))) < θ' := fun θ' h1' h2' => by
      have e := hsame θ' h1' h2'
      have := quot_slope_lt hLlat θ' (by rw [e]; exact h1) h2
      rwa [e] at this
    generalize Formalism.F.slope (Formalism.F.quot (zl ρ N) (zl ρ (hnStep ρ L θ₀))) = s at key ⊢
    have hs : s ≤ θ := by
      by_contra hcon
      push Not at hcon
      have := key (min s θ₀) (lt_min hcon hθ₀) (min_le_right _ _)
      exact lt_irrefl _ (this.trans_le (min_le_left _ _))
    exact (Real.log_le_iff_le_exp ht).1 (by linarith)
  · intro hn
    have hL0 : L ≠ ⊥ := by
      intro h
      have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      have htop : (⊤ : Submodule I.E (Fin I.n → I.E)) = ⊥ := by
        rw [← hspan, h]
        simp
      exact top_ne_bot htop
    have hleast : least I x = Real.exp (c - muMax ρ L) := by
      unfold least
      exact (sizeMu _ _ _ (bas I) (frm I x) hdet L hfg hL0).2.2.2.1
    refine ⟨by rw [hleast]; exact Real.exp_pos _, ?_, ?_⟩
    · rw [hLe, step_eq_bot hLlat hL0, hleast, ← Real.log_lt_iff_lt_exp ht]
      constructor <;> intro h <;> linarith
    · rw [hLt', hleast, ← Real.log_le_iff_le_exp ht]
      constructor
      · intro hb
        by_contra hcon
        push Not at hcon
        have h1 : θ < muMax ρ L := by linarith
        have hm : muMax ρ L < θ₀ := (step_eq_bot hLlat hL0 θ₀).1 hb
        have := (step_eq_bot hLlat hL0 _).1 ((hsame _ h1 hm.le).trans hb)
        exact lt_irrefl _ this
      · intro h
        exact (step_eq_bot hLlat hL0 θ₀).2 (by linarith)

end GlobalTheory.CountSteps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalLatticeFiltration_size_properties : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  first | exact @GlobalTheory.CountSteps.steps | exact GlobalTheory.CountSteps.steps | (intros; apply GlobalTheory.CountSteps.steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.PermGroup
variable {n : ℕ}

lemma memLp_equiv {ε ε' : Fin n → Bool} (e : UJ ε' ≃ₜ* UJ ε) (F : UJ ε → ℂ) (p : ENNReal) :
    MemLp F p (muG ε) ↔ MemLp (fun g => F (e g)) p (muG ε') := by
  have hE : (Measure.map e (muG ε')).IsHaarMeasure := e.isHaarMeasure_map (muG ε')
  have hc : Measure.map e (muG ε') =
      Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) • muG ε := Measure.isMulLeftInvariant_eq_smul _ _
  set c : ENNReal := ((Measure.haarScalarFactor (Measure.map e (muG ε')) (muG ε) : NNReal) : ENNReal)
    with hcdef
  have hc' : Measure.map e (muG ε') = c • muG ε := by rw [hcdef, ← ENNReal.smul_def]; exact hc
  have hT : c ≠ ⊤ := ENNReal.coe_ne_top
  have h0 : c ≠ 0 := by
    intro hz
    have hz' : Measure.map e (muG ε') = 0 := by rw [hc', hz, zero_smul]
    rw [Measure.map_eq_zero_iff
      (show AEMeasurable (⇑e) (muG ε') from (map_continuous e).measurable.aemeasurable)] at hz'
    exact NeZero.ne _ hz'
  have hm := (e.toHomeomorph.toMeasurableEquiv).memLp_map_measure_iff (g := F) (p := p) (μ := muG ε')
  change MemLp F p (Measure.map e (muG ε')) ↔ MemLp (F ∘ e) p (muG ε') at hm
  change MemLp F p (muG ε) ↔ MemLp (F ∘ e) p (muG ε')
  rw [← hm, hc']
  constructor
  · intro h
    exact h.smul_measure hT
  · intro h
    have h' := h.smul_measure (ENNReal.inv_ne_top.2 h0)
    rwa [smul_smul, ENNReal.inv_mul_cancel h0 hT, one_smul] at h'

def homUJ {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) : UJ ε' →* UJ ε :=
  ((Units.map φ).comp (UJ ε').subtype).codRestrict (UJ ε) fun g => h _ g.2

lemma homUJ_cont {ε ε' : Fin n → Bool} (φ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (hc : Continuous φ) : Continuous (homUJ φ h) := by
  refine continuous_induced_rng.2 ?_
  rw [Units.continuous_iff]
  exact ⟨hc.comp (Units.continuous_val.comp continuous_subtype_val),
    hc.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

lemma memLp_hom {ε ε' : Fin n → Bool} (φ ψ : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ g ∈ UJset ε', φ g ∈ UJset ε) (h' : ∀ g ∈ UJset ε, ψ g ∈ UJset ε')
    (hc : Continuous φ) (hc' : Continuous ψ) (h1 : ∀ g, ψ (φ g) = g) (h2 : ∀ g, φ (ψ g) = g)
    (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal) :
    MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔
      MemLp (fun g : UJ ε' => f (φ (umat g))) p (muG ε') := by
  let e : UJ ε' ≃ₜ* UJ ε :=
    { toFun := homUJ φ h
      invFun := homUJ ψ h'
      left_inv := fun g => Subtype.ext (Units.ext (h1 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      right_inv := fun g => Subtype.ext (Units.ext (h2 ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
      map_mul' := fun a b => map_mul (homUJ φ h) a b
      continuous_toFun := homUJ_cont φ h hc
      continuous_invFun := homUJ_cont ψ h' hc' }
  exact memLp_equiv e (fun g => f (umat g)) p

def perm (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ ≃+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ s).toRingEquiv

lemma perm_apply (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    perm s g = g.submatrix s.symm s.symm := rfl

lemma perm_cont (s : Equiv.Perm (Fin n)) : Continuous (perm s) := by
  have h : ⇑(perm s) = fun g => g.submatrix s.symm s.symm := funext (perm_apply s)
  rw [h]
  exact continuous_id.matrix_submatrix _ _

lemma perm_ct (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) : (perm s g)ᴴ = perm s gᴴ := rfl

lemma perm_Jm (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) : Jm ε = perm s (Jm (ε ∘ s)) := by
  rw [perm_apply]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Jm]
  · have hij' : s.symm i ≠ s.symm j := fun h => hij (s.symm.injective h)
    simp [Jm, hij, hij']

lemma perm_UJ (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ UJset (ε ∘ s) ↔ perm s g ∈ UJset ε := by
  simp only [UJset, Set.mem_ofPred_eq, inUJ]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul]
  exact (perm s).injective.eq_iff.symm

lemma perm_K (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ Kset (ε ∘ s) ↔ perm s g ∈ Kset ε := by
  simp only [Kset, Set.mem_ofPred_eq, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, EmbeddingLike.map_eq_one_iff, (perm s).injective.eq_iff]

lemma perm_P (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    inP (ε ∘ s) g ↔ inP ε (perm s g) := by
  simp only [inP, inG]
  rw [perm_ct, perm_Jm ε s]
  simp only [← map_mul, ← map_add (f := _), ← map_neg, EmbeddingLike.map_eq_zero_iff,
    (perm s).injective.eq_iff]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
lemma perm_exp (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (perm s g) = perm s (NormedSpace.exp g) := (NormedSpace.map_exp (perm s) (perm_cont s) g).symm

def permM (s : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.submatrix s.symm s.symm
  map_one' := map_one (perm s)
  map_mul' := map_mul (perm s)

lemma permM_symm (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s.symm (permM s g) = g := by
  show (g.submatrix s.symm s.symm).submatrix s.symm.symm s.symm.symm = g
  ext i j
  simp

lemma permM_symm' (s : Equiv.Perm (Fin n)) (g : Matrix (Fin n) (Fin n) ℂ) :
    permM s (permM s.symm g) = g := by
  show (g.submatrix s.symm.symm s.symm.symm).submatrix s.symm s.symm = g
  ext i j
  simp

def conj : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := g.map star
  map_one' := FormF.map_star_one
  map_mul' := FormF.map_star_mul

lemma conj_cont : Continuous (conj (n := n)) := by
  show Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.map star
  exact continuous_id.matrix_map continuous_star

theorem permGroup : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  intro n ε s
  have hpm : ∀ (t : Equiv.Perm (Fin n)) (x : Matrix (Fin n) (Fin n) ℂ), permM t x = perm t x :=
    fun t x => (perm_apply t x).symm
  have hcont : ∀ t : Equiv.Perm (Fin n), Continuous (permM t) := fun t => by
    have h : ⇑(permM t) = ⇑(perm t) := funext (hpm t)
    rw [h]
    exact perm_cont t
  refine ⟨fun g => ⟨?_, ?_, ?_, ?_⟩, fun f p => ⟨?_, ?_⟩⟩
  · rw [← perm_apply]; exact perm_UJ ε s g
  · rw [← perm_apply]; exact perm_K ε s g
  · rw [← perm_apply]; exact perm_P ε s g
  · rw [← perm_apply, ← perm_apply]; exact perm_exp s g
  · refine memLp_hom (permM s) (permM s.symm) (fun g hg => ?_) (fun g hg => ?_) (hcont s)
      (hcont s.symm) (permM_symm s) (permM_symm' s) f p
    · rw [hpm]; exact (perm_UJ ε s g).1 hg
    · apply (perm_UJ ε s _).2
      rw [← hpm, permM_symm']
      exact hg
  · exact memLp_hom GlobalTheory.Dec.PermGroup.conj GlobalTheory.Dec.PermGroup.conj (fun g hg => FormF.UJ_star hg)
      (fun g hg => FormF.UJ_star hg) conj_cont conj_cont (fun g => FormF.map_star_star g)
      (fun g => FormF.map_star_star g) f p

end GlobalTheory.Dec.PermGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariantStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_structures_perm_conj_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (s : Equiv.Perm (Fin n)), (∀ g : Matrix (Fin n) (Fin n) ℂ, (g ∈ UJset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ UJset ε) ∧ (g ∈ Kset (ε ∘ s) ↔ g.submatrix s.symm s.symm ∈ Kset ε) ∧ (inP (ε ∘ s) g ↔ inP ε (g.submatrix s.symm s.symm)) ∧ NormedSpace.exp (g.submatrix s.symm s.symm) = (NormedSpace.exp g).submatrix s.symm s.symm) ∧ ∀ (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (p : ENNReal), (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ (ε ∘ s) => f ((umat g).submatrix s.symm s.symm)) p (muG (ε ∘ s))) ∧ (MemLp (fun g : UJ ε => f (umat g)) p (muG ε) ↔ MemLp (fun g : UJ ε => f ((umat g).map star)) p (muG ε)) := by
  first | exact @GlobalTheory.Dec.PermGroup.permGroup | exact GlobalTheory.Dec.PermGroup.permGroup | (intros; apply GlobalTheory.Dec.PermGroup.permGroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroup
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem isUnimod_GG : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  intro k r μ hμ
  obtain ⟨hG, h⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hM, hR⟩ := h μ hμ
  refine ⟨fun s hs => hR s hs, ?_⟩
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf measurable_invM]
  exact GlobalTheory.HaarInversion.lintegral_inv_eq _ (GG k r) μ hG hM hR f hf

end GlobalTheory.SgInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroupStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnimodular_besselModelUnitaryGroup : ∀ (k r : ℕ) (μ : Measure (Mt k r)), IsHaarOn (GG k r) μ → IsUnimod (GG k r) μ := by
  first | exact @GlobalTheory.SgInf.isUnimod_GG | exact GlobalTheory.SgInf.isUnimod_GG | (intros; apply GlobalTheory.SgInf.isUnimod_GG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDecOfDecGapGapGe
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem locDec_of_decGap_gapGe : DecGap → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → GapGe B h →
    (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h := by
  intro hD B d h hds hgap hh v g
  obtain ⟨h1, h2, h3, -⟩ := hds v
  have hw : B.w v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v) := h3.2
  have hn : ‖B.w v‖ = 1 := h3.1
  have := (hD _ _ _ _ _ h1 h2 h (hgap v) (hh v) (uMat g) g.2 _ hw _ hw).2
  simpa [hn] using this

end GlobalTheory.Dec
end
