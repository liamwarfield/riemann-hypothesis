module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp Filter Topology
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LenCont

theorem eucl_eq {n : ℕ} (v : Fin n → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [eucl, Complex.normSq_eq_norm_sq]

theorem eucl_mulVec_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    eucl (A *ᵥ v) ≤ opn A * eucl v := by
  rw [eucl_eq, eucl_eq, opn, ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem opn_continuous {n : ℕ} : Continuous (opn (n := n)) := by
  unfold opn
  refine continuous_norm.comp ?_
  exact LinearMap.continuous_of_finiteDimensional
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).toAlgEquiv.toLinearMap)

theorem opn_one {n : ℕ} : opn (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = 1 := by
  rw [opn, map_one, norm_one]

def len {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sInf {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))}

theorem len_le {n : ℕ} (Y : Submodule ℂ (Fin n → ℂ)) (f : Fin n → ℂ) (g h : Matrix (Fin n) (Fin n) ℂ)
    (hh : IsUnit h.det) : len Y f g ≤ opn (g⁻¹ * h) * len Y f h := by
  have hb : BddBelow {t | ∃ y ∈ Y, t = eucl (g⁻¹ *ᵥ (f - y))} :=
    ⟨0, by rintro t ⟨y, -, rfl⟩; exact Real.sqrt_nonneg _⟩
  have hne : {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}.Nonempty := ⟨_, 0, Y.zero_mem, rfl⟩
  have key : ∀ t ∈ {t | ∃ y ∈ Y, t = eucl (h⁻¹ *ᵥ (f - y))}, len Y f g ≤ opn (g⁻¹ * h) * t := by
    rintro t ⟨y, hy, rfl⟩
    refine (csInf_le hb ⟨y, hy, rfl⟩).trans ?_
    have := eucl_mulVec_le (g⁻¹ * h) (h⁻¹ *ᵥ (f - y))
    rwa [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one] at this
  have h0 : 0 ≤ opn (g⁻¹ * h) := norm_nonneg _
  rcases h0.eq_or_lt with h0 | h0
  · obtain ⟨t, ht⟩ := hne
    have := key t ht
    rw [← h0] at this ⊢
    simpa using this
  · rw [mul_comm, ← div_le_iff₀ h0]
    refine le_csInf hne fun t ht => ?_
    rw [div_le_iff₀ h0, mul_comm]
    exact key t ht

theorem len_continuousOn {n : ℕ} (Y : Submodule ℂ (Fin (n + 1) → ℂ)) (f : Fin (n + 1) → ℂ) :
    ContinuousOn (len Y f) {g | IsUnit g.det} := by
  intro x₀ hx₀
  have hx₀' : IsUnit x₀.det := hx₀
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → _) x₀ := by
    refine continuousAt_matrix_inv x₀ ?_
    obtain ⟨u, hu⟩ := hx₀'
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have h1 : Tendsto (fun x => opn (x⁻¹ * x₀)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x⁻¹ * x₀)) x₀ :=
      opn_continuous.continuousAt.comp (hinv.mul continuousAt_const)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have h2 : Tendsto (fun x => opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 1) := by
    have : ContinuousAt (fun x : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => opn (x₀⁻¹ * x)) x₀ :=
      opn_continuous.continuousAt.comp (continuousAt_const.mul continuousAt_id)
    simpa [ContinuousAt, Matrix.nonsing_inv_mul _ hx₀', opn_one] using this
  have hU : Tendsto (fun x => opn (x⁻¹ * x₀) * len Y f x₀) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    simpa using h1.mul_const (len Y f x₀)
  have hL : Tendsto (fun x => len Y f x₀ / opn (x₀⁻¹ * x)) (𝓝 x₀) (𝓝 (len Y f x₀)) := by
    have := (tendsto_const_nhds (x := len Y f x₀)).div h2 one_ne_zero
    rw [div_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hL.mono_left nhdsWithin_le_nhds)
    (hU.mono_left nhdsWithin_le_nhds) ?_ (Eventually.of_forall fun x => len_le Y f x x₀ hx₀')
  filter_upwards [self_mem_nhdsWithin, (h2.eventually (lt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds]
    with x hx hpos
  rw [div_le_iff₀ hpos, mul_comm]
  exact len_le Y f x₀ x hx

theorem fold_continuousOn {X ι : Type*} [TopologicalSpace X] [DecidableEq ι] (S : Set X) (F : ι → X → ℝ)
    (hF : ∀ a, ContinuousOn (F a) S) (s : Finset ι) :
    ContinuousOn (fun x => s.fold max 1 fun a => F a x) S := by
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s ha ih =>
    simp only [Finset.fold_insert ha]
    exact continuous_max.comp_continuousOn ((hF a).prodMk ih)

theorem lA_Sg_continuousOn : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)),
    (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  intro k r z
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1
  have h : ∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r) := fun a =>
    (len_continuousOn _ (fvec k r z a)).mono fun g hg => ((uHGroup _ _ hH).2.2 g hg).1
  exact ⟨h, fold_continuousOn (GG k r) (fun a x => lA k r z x a) h Finset.univ⟩

end GlobalTheory.Amp.LenCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengthsStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_majorantFlagLengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), (∀ a, ContinuousOn (fun x => lA k r z x a) (GG k r)) ∧ ContinuousOn (Sg k r z) (GG k r) := by
  first | exact @GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | exact GlobalTheory.Amp.LenCont.lA_Sg_continuousOn | (intros; apply GlobalTheory.Amp.LenCont.lA_Sg_continuousOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.FockTen

theorem fockF_eq_fockL {σ : Type} (f g : MvPolynomial σ ℂ) : Formalism.REAL.fockF f g = Formalism.L2.DIV.fockL g f := by
  classical
  rw [Formalism.L2.DIV.fockL_apply,
    Formalism.L2.DIV.fockS_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right]
  unfold Formalism.REAL.fockF
  rw [Finset.sum_subset (Finset.subset_union_left : f.support ⊆ f.support ∪ g.support)]
  · refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Formalism.L2.DIV.mfact]
    ring
  · intro m _ hm
    have hf : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    rw [hf, zero_mul, zero_mul]

theorem fockF_ten {ι : Type} [Fintype ι] {n : ℕ} (f g : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.REAL.fockF (ten f) (ten g) = ∏ τ, Formalism.REAL.fockF (f τ) (g τ) := by
  rw [fockF_eq_fockL]
  show Formalism.L2.DIV.fockL (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (g τ)) (∏ τ, Formalism.GradedWeylDivisibility.blockEmb ℂ τ (f τ)) = _
  rw [Formalism.L2.DIV.fk_fock_prod]
  exact Finset.prod_congr rfl fun τ _ => (fockF_eq_fockL _ _).symm

theorem fockF_extremal_ne {n : ℕ} (l : DomWeight n) : Formalism.REAL.fockF (extremal ℂ n l) (extremal ℂ n l) ≠ 0 := by
  intro h0
  have h1 : normFock l (extremal ℂ n l) (extremal ℂ n l) = 1 := bridge_normFock_extremal_holds n l
  rw [normFock, h0, div_zero] at h1
  exact zero_ne_one h1

theorem nfAll_ten : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  intro ι _ n lam
  have hden : ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => fockF_extremal_ne (lam τ)
  refine ⟨fun f g => ?_, fun p hp => ?_, fun G M s f y => ?_⟩
  · rw [nfAll, fockF_ten]
    simp only [normFock]
    rw [Finset.prod_div_distrib]
  · rw [nfAll, div_eq_zero_iff] at hp
    rcases hp with hp | hp
    · by_contra hne
      exact (@LT.lt.ne' ℂ Complex.partialOrder.toPreorder _ _ (Formalism.L2.DIV.ps_fockF_pos p hne)) hp
    · exact absurd hp hden
  · show (∏ τ, (M τ * y.1 τ).det ^ s τ) *
        MvPolynomial.eval _ (∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)) = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [MvPolynomial.eval_rename]
    rfl

end GlobalTheory.FockTen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorPropertiesStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedFockForm_pureTensor_properties : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  first | exact @GlobalTheory.FockTen.nfAll_ten | exact GlobalTheory.FockTen.nfAll_ten | (intros; apply GlobalTheory.FockTen.nfAll_ten <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfValTwoEqCvalR
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CasimirEigen

variable {n : ℕ}

theorem gelfVal_two_eq (χ : Fin n → ℂ) :
    gelfVal χ 2 = ∑ a, χ a * χ a - ∑ a, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) := by
  rw [gelfVal_succ χ 1, pow_one]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_mul]
  have e : ∀ a : Fin n, (if a = b then χ a + ((n : ℂ) - 1) / 2 else if a < b then -1 else 0) =
      (if a = b then χ a + ((n : ℂ) - 1) / 2 else 0) - (if a ∈ Finset.Iio b then 1 else 0) := by
    intro a
    by_cases h1 : a = b
    · subst h1; simp
    · by_cases h2 : a < b <;> simp [h1, h2]
  simp only [Amat, Matrix.of_apply, e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, Fin.card_Iio, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  ring

theorem gelfVal_two_eq_cvalR (ε : Fin n → Bool) (lam : Fin n → ℝ) :
    gelfVal (fun a => (lam a : ℂ)) 2 = ((cvalR ε lam : ℝ) : ℂ) := by
  rw [gelfVal_two_eq]
  simp only [cvalR, nsq, dot, Pi.add_apply, half_sum_roots_standard n ε, Formalism.QuantumDeterminants.rhoStd]
  push_cast
  rfl

theorem gelf_one_eq (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    gelf ε 1 f g = ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g := by
  unfold gelf
  rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rfl

theorem inner_eabV {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {f : Matrix (Fin n) (Fin n) ℂ → H} (hf : SmoothOnGV ε f) (y : H) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Eab ε a b (fun x => ⟪y, f x⟫_ℂ) g = ⟪y, EabV ε a b f g⟫_ℂ := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have k1 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h1 hg).2
  have k2 := (rdVPair_of vector_right_derivative_extends n ε H ℂ (innerSL ℂ y) f _ g hf h2 hg).2
  simp only [innerSL_apply_apply, rdV_eq] at k1 k2
  simp only [Eab, Ec, EabV, EcV, inner_add_right, inner_smul_right, k1, k2]

theorem cas_eq_of_isZEigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ Vs) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → ((∀ u, u ∈ Vs ↔ SmoothOnGV ε (fun g => σ g u)) ∧ GlRel E ∧ IsUnitary ε E ∧ (∀ X, inG ε X → ∀ u : Vs, HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0) ∧ ∀ a b (u : Vs), ∀ g ∈ UJset ε, σ g (E a b u) = EabV ε a b (fun g => σ g u) g) → ∀ u : Vs, (∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g u⟫_ℂ)) → Cas E u = ((cvalR ε lam : ℝ) : ℂ) • u := by
  intro n ε H _ _ _ σ Vs E lam hσ ⟨hV, _, _, _, hE⟩ u hu
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := GlobalTheory.SmoothVecMod.inUJ_one
  have key : ∀ (y : H) (a b : Fin n) (v : Vs) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Eab ε a b (fun x => ⟪y, σ x v⟫_ℂ) g = ⟪y, σ g (E a b v)⟫_ℂ := by
    intro y a b v g hg
    rw [hE a b v g hg]
    exact inner_eabV ((hV v).1 v.2) y a b hg
  apply Subtype.ext
  refine ext_inner_left ℂ fun y => ?_
  have h := (hu y).2 1 1 h1
  rw [gelf_one_eq, gelfVal_two_eq_cvalR ε lam] at h
  have e : ∀ a b : Fin n, Eab ε a b (Eab ε b a (fun x => ⟪y, σ x u⟫_ℂ)) 1 =
      ⟪y, ((E a b (E b a u) : Vs) : H)⟫_ℂ := by
    intro a b
    have := GlobalTheory.SmoothVecMod.eabV_congr (E := ℂ) (key y b a u) a b h1
    rw [eabV_eq, eabV_eq] at this
    rw [this, key y a b _ 1 h1, hone]
  simp only [e, hone] at h
  simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, inner_sum, Submodule.coe_smul,
    inner_smul_right]
  exact h

end GlobalTheory.CasimirEigen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegral
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.CutQuot

section Abstract

variable {X : Type*} [MeasurableSpace X] {T : X → X → X} {G R : Set X} {μG μR ν : Measure X}

theorem null_of_stable (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    {B : Set X} (hB : MeasurableSet B) (hst : ∀ s ∈ R, ∀ x ∈ B, T s x ∈ B) (hn : μG B = 0) : ν B = 0 := by
  have h1 := hW (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hn] at h1
  have h2 : ∫⁻ x, B.indicator (fun _ => μR Set.univ) x ∂ν ≤
      ∫⁻ x, (∫⁻ s, B.indicator (1 : X → ℝ≥0∞) (T s x) ∂μR) ∂ν := by
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, ← lintegral_one]
      refine le_of_eq (lintegral_congr_ae ?_)
      filter_upwards [hR] with s hs
      rw [Set.indicator_of_mem (hst s hs x hx)]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  rw [← h1, lintegral_indicator_const hB, nonpos_iff_eq_zero, mul_eq_zero] at h2
  exact h2.resolve_left (by simpa using h0)

theorem exists_cut [SigmaFinite μG] [SFinite μR] (hT : Measurable (Function.uncurry T))
    (hR : ∀ᵐ s ∂μR, s ∈ R) (h0 : μR ≠ 0)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν)
    (hG : ∀ᵐ x ∂ν, x ∈ G)
    (hinv : ∀ ρ ∈ R, ∀ x, ∀ f : X → ℝ≥0∞, Measurable f →
      ∫⁻ s, f (T s (T ρ x)) ∂μR = ∫⁻ s, f (T s x) ∂μR) :
    ∃ φ : X → ℝ≥0∞, Measurable φ ∧ (∀ x, ∫⁻ ρ, φ (T ρ x) ∂μR ≤ 1) ∧
      ∀ F : X → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x ∈ G, F (T ρ x) = F x) →
        ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  obtain ⟨g, hg0, hgm, hgi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  set ψ : X → ℝ≥0∞ := fun x => (g x : ℝ≥0∞) with hψ
  have hψm : Measurable ψ := hgm.coe_nnreal_ennreal
  have hTx : ∀ x, Measurable fun s => T s x := fun x => hT.comp (measurable_id.prodMk measurable_const)
  set I : X → ℝ≥0∞ := fun x => ∫⁻ s, ψ (T s x) ∂μR with hI
  have hIm : Measurable I := Measurable.lintegral_prod_left (f := fun s x => ψ (T s x)) (hψm.comp hT)
  have hI0 : ∀ x, I x ≠ 0 := by
    intro x hx
    have h := (lintegral_eq_zero_iff (hψm.comp (hTx x))).1 hx
    apply h0
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with s hs
    have := hg0 (T s x)
    simp [hψ] at hs
    exact this.ne' hs
  have hIfin : ∀ᵐ x ∂ν, I x < ∞ := by
    refine ae_lt_top hIm ?_
    rw [← hW ψ hψm]
    exact (hgi.trans ENNReal.one_lt_top).ne
  have key : ∀ x, ∫⁻ ρ, ψ (T ρ x) * (I (T ρ x))⁻¹ ∂μR = I x * (I x)⁻¹ := by
    intro x
    rw [show I x * (I x)⁻¹ = ∫⁻ ρ, ψ (T ρ x) * (I x)⁻¹ ∂μR from
      (lintegral_mul_const (I x)⁻¹ (f := fun s => ψ (T s x)) (hψm.comp (hTx x))).symm]
    refine lintegral_congr_ae ?_
    filter_upwards [hR] with s hs
    have : I (T s x) = I x := hinv s hs x ψ hψm
    rw [this]
  have hφm : Measurable fun x => ψ x * (I x)⁻¹ := hψm.mul hIm.inv
  refine ⟨fun x => ψ x * (I x)⁻¹, hφm, fun x => ?_, fun F hF hFi => ?_⟩
  · rw [key]; exact ENNReal.mul_inv_le_one _
  · show _ = ∫⁻ x, ψ x * (I x)⁻¹ * F x ∂μG
    rw [hW (fun x => ψ x * (I x)⁻¹ * F x) (hφm.mul hF)]
    refine lintegral_congr_ae ?_
    filter_upwards [hG, hIfin] with x hx hx'
    have h1 : ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F (T s x) ∂μR =
        ∫⁻ s, ψ (T s x) * (I (T s x))⁻¹ * F x ∂μR := by
      refine lintegral_congr_ae ?_
      filter_upwards [hR] with s hs
      rw [hFi s hs x hx]
    rw [h1, lintegral_mul_const (F x) (f := fun s => ψ (T s x) * (I (T s x))⁻¹) (hφm.comp (hTx x)), key,
      ENNReal.mul_inv_cancel (hI0 x) hx'.ne, one_mul]

end Abstract

theorem mul_mem_iff {k r : ℕ} {s : Mat k r} (hs : s ∈ GG k r) (x : Mat k r) :
    s * x ∈ GG k r ↔ x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * Hpk k r * x := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← hs']
    simp only [Matrix.mul_assoc]
  show (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r ↔ xᴴ * Hpk k r * x = Hpk k r
  rw [this]

theorem measurable_G (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  refine IsClosed.measurableSet ?_
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact isClosed_eq (f := fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x)
    ((h.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h) continuous_const

theorem continuous_act (k r : ℕ) :
    Continuous (Function.uncurry fun s x : Mt k r => lmulM (Matrix.of s) x) := by
  have h : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  exact (h.comp continuous_fst).matrix_mul (h.comp continuous_snd)

theorem cut_quotient : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  intro k r R μG μR ν hR hG hμ hU hW
  haveI := hG.1
  haveI := hμ.1
  set T : Mt k r → Mt k r → Mt k r := fun s x => lmulM (Matrix.of s) x with hT
  have hTm : Measurable (Function.uncurry T) := (continuous_act k r).measurable
  have hae : ∀ᵐ s ∂μR, s ∈ {x : Mt k r | Matrix.of x ∈ R} := hμ.2.2.1
  have hW' : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (T s x) ∂μR) ∂ν := hW
  have hmem : ∀ s : Mt k r, Matrix.of s ∈ R → ∀ x : Mt k r,
      (Matrix.of (T s x) ∈ GG k r ↔ Matrix.of x ∈ GG k r) := fun s hs x =>
    mul_mem_iff (hR.1 hs) (Matrix.of x)
  have h1 : ν {x | Matrix.of x ∉ GG k r} = 0 :=
    null_of_stable hae hμ.2.1 hW' (measurable_G k r).compl
      (fun s hs x hx h => hx ((hmem s hs x).1 h)) hG.2.2.1
  have h1' : ∀ᵐ x ∂ν, x ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := h1
  refine ⟨h1, fun A hA hst hn => ?_, ?_⟩
  · have h2 : ν (A ∩ {x : Mt k r | Matrix.of x ∈ GG k r}) = 0 :=
      null_of_stable hae hμ.2.1 hW' (hA.inter (measurable_G k r))
        (fun s hs x hx => ⟨(hst _ hs x hx.2).2 hx.1, (hmem s hs x).2 hx.2⟩)
        (measure_mono_null Set.inter_subset_left hn)
    refine measure_mono_null (fun x hx => ?_) (measure_union_null h2 h1)
    by_cases h : Matrix.of x ∈ GG k r
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · obtain ⟨φ, hφ, hle, hF⟩ := exists_cut hTm hae hμ.2.1 hW' h1' (by
      intro ρ hρ x f hf
      have hTx : Measurable fun s => T s x := hTm.comp (measurable_id.prodMk measurable_const)
      have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
      have hr : Measurable (rmulM (k := k) (r := r) (Matrix.of ρ)) :=
        by
        have hc' : Continuous (rmulM (k := k) (r := r) (Matrix.of ρ)) := hc.matrix_mul continuous_const
        exact hc'.measurable
      conv_rhs => rw [← hU.1 (Matrix.of ρ) hρ]
      rw [lintegral_map (f := fun s => f (T s x)) (hf.comp hTx) hr]
      refine lintegral_congr fun s => congrArg f ?_
      exact (Matrix.mul_assoc (Matrix.of s) (Matrix.of ρ) (Matrix.of x)).symm)
    exact ⟨φ, ⟨hφ, fun x _ => hle x⟩, fun F hFm hFi => hF F hFm fun ρ hρ x hx => hFi _ hρ x hx⟩

end GlobalTheory.Amp.CutQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutoffComputesBesselQuotientIntegralStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_computes_besselQuotientIntegral : ∀ (k r : ℕ) (R : Set (Mat k r)) (μG μR ν : Measure (Mt k r)), IsClosedSub k r R → IsHaarOn (GG k r) μG → IsHaarOn R μR → IsUnimod R μR → IsQuotMeas μG μR ν → ν {x | Matrix.of x ∉ GG k r} = 0 ∧ (∀ A : Set (Mt k r), MeasurableSet A → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → (lmulM ρ x ∈ A ↔ x ∈ A)) → μG A = 0 → ν A = 0) ∧ ∃ φ, SubCut (GG k r) μR φ ∧ ∀ F : Mt k r → ℝ≥0∞, Measurable F → (∀ ρ ∈ R, ∀ x, Matrix.of x ∈ GG k r → F (lmulM ρ x) = F x) → ∫⁻ x, F x ∂ν = ∫⁻ x, φ x * F x ∂μG := by
  first | exact @GlobalTheory.Amp.CutQuot.cut_quotient | exact GlobalTheory.Amp.CutQuot.cut_quotient | (intros; apply GlobalTheory.Amp.CutQuot.cut_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitary
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.FlagMeas.measurable_detOn_comp {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ}
    (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) (V : Submodule ℂ (Fin n → ℂ)) :
    Measurable fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  let P := Submodule.linearProjOfIsCompl V W hW
  let b := Module.finBasis ℂ V
  let g : X → ℂ := fun x =>
    (Matrix.of fun i k => b.repr (P (f x *ᵥ (b k : Fin n → ℂ))) i).det
  have hg : Continuous g := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i k => ?_
    have hL : Continuous fun v : Fin n → ℂ => b.repr (P v) i :=
      (((Finsupp.lapply i).comp b.repr.toLinearMap).comp P).continuous_of_finiteDimensional
    exact hL.comp (hf.matrix_mulVec continuous_const)
  have hS : IsClosed {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := by
    simp only [Set.setOf_forall]
    refine isClosed_biInter fun y _ => ?_
    exact V.closed_of_finiteDimensional.preimage (hf.matrix_mulVec continuous_const)
  have heq : (fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V) =
      fun x => if x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} then ‖g x‖ else 0 := by
    funext x
    unfold _root_.GlobalTheory.FlagMeas.detOn
    by_cases h : ∀ y ∈ V, (toLin' (f x)) y ∈ V
    · have h' : x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun y hy => by
        simpa [Matrix.toLin'_apply] using h y hy
      rw [dite_eq_left h, if_pos h', ← LinearMap.det_toMatrix b]
      congr 2
      ext i k
      rw [LinearMap.toMatrix_apply, Matrix.of_apply]
      congr 2
      have hm : f x *ᵥ (b k : Fin n → ℂ) = ((toLin' (f x)).restrict h (b k) : Fin n → ℂ) := by
        simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
      rw [hm]
      exact (Submodule.projectionOnto_apply_left hW _).symm
    · have h' : x ∉ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun hx => h fun y hy => by
        simpa [Matrix.toLin'_apply] using hx y hy
      rw [dite_eq_right h, if_neg h']
  rw [heq]
  exact Measurable.ite hS.measurableSet hg.norm.measurable measurable_const

theorem _root_.GlobalTheory.FlagMeas.measurable_locSize_uMat (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a) :
    Measurable fun g : _root_.Formalism.REAL.UJ ε => _root_.GlobalTheory.FlagMeas.locSize j W (_root_.Formalism.MainNotions.S.uMat g) i := by
  have hc : Continuous fun g : _root_.Formalism.REAL.UJ ε => _root_.Formalism.MainNotions.S.uMat g := by
    unfold _root_.Formalism.MainNotions.S.uMat
    exact Units.continuous_val.comp continuous_subtype_val
  unfold _root_.GlobalTheory.FlagMeas.locSize
  exact ((_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _).div
    (_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _)).pow_const _

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitaryStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_flagLocalSizes_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a), Measurable fun g : Formalism.REAL.UJ ε => locSize j W (uMat g) i := by
  first | exact @GlobalTheory.FlagMeas.measurable_locSize_uMat | exact GlobalTheory.FlagMeas.measurable_locSize_uMat | (intros; apply GlobalTheory.FlagMeas.measurable_locSize_uMat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdPartialZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFinEqSumCastLEOfVanish
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.LeadMinorTri

theorem sum_fin_eq_sum_castLE_of_vanish {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ)
    (hf : ∀ k : Fin n, l ≤ k.val → f k = 0) :
    ∑ k, f k = ∑ k : Fin l, f (Fin.castLE hl k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE hl) ((Fin.castLE_injective hl).injOn) (by simp) ?_ (by simp)
  intro k _ hk
  apply hf
  by_contra h
  exact hk ⟨⟨k.val, by omega⟩, by simp, rfl⟩

theorem leadBlock_lower_mul {n l : ℕ} (hl : l ≤ n) (c z : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, i < j → c i j = 0) :
    (c * z).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      c.submatrix (Fin.castLE hl) (Fin.castLE hl) * z.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => c (Fin.castLE hl i) k * z k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc _ k (by rw [Fin.lt_def]; have := i.isLt; simp only [Fin.val_castLE]; omega), zero_mul]

theorem leadBlock_mul_upper {n l : ℕ} (hl : l ≤ n) (z c : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∀ i j, j < i → c i j = 0) :
    (z * c).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      z.submatrix (Fin.castLE hl) (Fin.castLE hl) * c.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_fin_eq_sum_castLE_of_vanish hl (fun k => z (Fin.castLE hl i) k * c k (Fin.castLE hl j)) ?_
  intro k hk
  rw [hc k _ (by rw [Fin.lt_def]; have := j.isLt; simp only [Fin.val_castLE]; omega), mul_zero]

theorem leadMinor_lower_mul_mul_upper :
    ∀ (n : ℕ) (c z c' : Matrix (Fin n) (Fin n) ℂ), (∀ i j, i < j → c i j = 0) → (∀ i j, j < i → c' i j = 0) → ∀ (l : ℕ) (hl : l ≤ n), leadMinor (c * z * c') l hl = (∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) * c' (Fin.castLE hl i) (Fin.castLE hl i)) * leadMinor z l hl := by
  intro n c z c' hc hc' l hl
  have h1 : (c.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_lowerTriangular
    intro i j hij
    exact hc _ _ (show i < j from hij)
  have h2 : (c'.submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      ∏ i : Fin l, c' (Fin.castLE hl i) (Fin.castLE hl i) := by
    apply Matrix.det_of_upperTriangular
    intro i j hij
    exact hc' _ _ (show j < i from hij)
  change ((c * z * c').submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
    _ * (z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
  rw [leadBlock_mul_upper hl _ _ hc', leadBlock_lower_mul hl _ _ hc, Matrix.det_mul, Matrix.det_mul,
    h1, h2, Finset.prod_mul_distrib]
  ring

end GlobalTheory.LeadMinorTri
end

open Matrix Finset Formalism.MainNotions.S GlobalTheory.Dec

namespace GlobalTheory.PhiTriangular

theorem sum_sInt_from {n : ℕ} (lam : Fin n → ℝ) (l : Fin n) :
    ∑ i : Fin n, (if l ≤ i then sInt lam i else 0) = muInt lam l := by
  let m : ℕ → ℤ := fun k => if h : k < n then muInt lam ⟨k, h⟩ else 0
  have h1 : ∀ i : Fin n, (if l ≤ i then sInt lam i else 0) =
      m (max i.val l.val) - m (max (i.val + 1) l.val) := by
    intro i
    by_cases h : l ≤ i
    · have h' : l.val ≤ i.val := h
      rw [if_pos h, max_eq_left h', max_eq_left (by omega : l.val ≤ i.val + 1)]
      simp only [m, sInt, dif_pos i.isLt]
    · have h' : i.val < l.val := by simpa using h
      rw [if_neg h, max_eq_right h'.le, max_eq_right (by omega : i.val + 1 ≤ l.val), sub_self]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => m (max k l.val) - m (max (k + 1) l.val)) n,
    Finset.sum_range_sub' (fun k => m (max k l.val)) n, max_eq_right (Nat.zero_le _),
    max_eq_left l.isLt.le]
  simp [m]

theorem prod_castLE_succ {n : ℕ} (d : Fin n → ℂ) (i : Fin n) :
    ∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j) = ∏ l : Fin n, if l ≤ i then d l else 1 := by
  refine Finset.prod_of_injOn (Fin.castLE i.isLt) ((Fin.castLE_injective _).injOn) (by simp) ?_ ?_
  · intro k _ hk
    rw [if_neg]
    intro h
    exact hk ⟨⟨k.val, Nat.lt_succ_of_le h⟩, by simp, rfl⟩
  · intro j _
    rw [if_pos]
    exact Nat.le_of_lt_succ j.isLt

theorem zpow_finset_sum {ι : Type} (s : Finset ι) (f : ι → ℤ) {a : ℂ} (ha : a ≠ 0) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem prod_partial_zpow {n : ℕ} (lam : Fin n → ℝ) (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) :
    ∏ i : Fin n, (∏ j : Fin (i.val + 1), d (Fin.castLE i.isLt j)) ^ (-(sInt lam i)) =
      ∏ l, d l ^ (-(muInt lam l)) := by
  simp only [prod_castLE_succ, ← Finset.prod_zpow]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← sum_sInt_from, ← Finset.sum_neg_distrib, zpow_finset_sum _ _ (hd l)]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : l ≤ i <;> simp [h]

theorem phiTri : PhiTri := by
  intro n lam c z c' hc hc' hd hz
  have hd' : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hd l).1 (hd l).2
  refine ⟨fun i => ?_, ?_⟩
  · rw [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc']
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd' _) (hz i)
  · unfold Phi
    simp only [GlobalTheory.LeadMinorTri.leadMinor_lower_mul_mul_upper n c z c' hc hc', mul_zpow _ (leadMinor z _ _)]
    rw [Finset.prod_mul_distrib, prod_partial_zpow lam (fun l => c l l * c' l l) hd']

end GlobalTheory.PhiTriangular
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramSchmidtLengths
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramFlag

open InnerProductSpace in
theorem sub_gs_mem {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r) :
    f a - gramSchmidt ℂ f a ∈ Submodule.span ℂ (f '' Set.Iio a) := by
  have h := gramSchmidt_def'' (𝕜 := ℂ) f a
  have hs : f a - gramSchmidt ℂ f a = ∑ i ∈ Finset.Iio a,
      (⟪gramSchmidt ℂ f i, f a⟫_ℂ / (‖gramSchmidt ℂ f i‖ : ℂ) ^ 2) • gramSchmidt ℂ f i := by
    rw [sub_eq_iff_eq_add']
    exact h
  rw [hs, ← span_gramSchmidt_Iio (𝕜 := ℂ) f a]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.1 hi, rfl⟩)

open InnerProductSpace in
theorem norm_gs_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) (a : Fin r)
    {w : E} (hw : w ∈ Submodule.span ℂ (f '' Set.Iio a)) : ‖gramSchmidt ℂ f a‖ ≤ ‖f a - w‖ := by
  have horth : ∀ v ∈ Submodule.span ℂ (f '' Set.Iio a), ⟪gramSchmidt ℂ f a, v⟫_ℂ = 0 := by
    intro v hv
    rw [← span_gramSchmidt_Iio (𝕜 := ℂ) f a] at hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact gramSchmidt_orthogonal (𝕜 := ℂ) f (ne_of_gt (Set.mem_Iio.1 hi))
    | zero => exact inner_zero_right _
    | add y y' _ _ hy hy' => rw [inner_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [inner_smul_right, hy, mul_zero]
  have hy : (f a - gramSchmidt ℂ f a) - w ∈ Submodule.span ℂ (f '' Set.Iio a) :=
    Submodule.sub_mem _ (sub_gs_mem f a) hw
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (gramSchmidt ℂ f a) _ (horth _ hy)
  have heq : gramSchmidt ℂ f a + ((f a - gramSchmidt ℂ f a) - w) = f a - w := by abel
  rw [heq] at hpy
  nlinarith [norm_nonneg (gramSchmidt ℂ f a), norm_nonneg (f a - w),
    mul_self_nonneg ‖(f a - gramSchmidt ℂ f a) - w‖]

open InnerProductSpace in
theorem exists_upper {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ} (f : Fin r → E) :
    ∃ u : UT r → ℂ, ∀ a, ∑ b, upper u b a • f b = gramSchmidt ℂ f a := by
  classical
  choose l hl hlx using fun a => (Finsupp.mem_span_image_iff_linearCombination ℂ).1 (sub_gs_mem f a)
  refine ⟨fun p => -(l p.1.2 p.1.1), fun a => ?_⟩
  have hz : ∀ b, a ≤ b → l a b = 0 := by
    intro b hab
    by_contra hne
    have hb := (Finsupp.mem_supported ℂ (l a)).1 (hl a) (Finset.mem_coe.2 (Finsupp.mem_support_iff.2 hne))
    exact absurd (Set.mem_Iio.1 hb) (not_lt.2 hab)
  have hc : ∀ b, upper (fun p : UT r => -(l p.1.2 p.1.1)) b a = (if b = a then 1 else 0) - l a b := by
    intro b
    rcases lt_trichotomy b a with hba | hba | hba
    · simp [upper, hba, hba.ne]
    · subst hba
      simp [upper, hz b le_rfl]
    · simp [upper, not_lt.2 hba.le, hba.ne', hz b hba.le]
  have hsum := hlx a
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (f i))] at hsum
  simp_rw [hc, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hsum, sub_sub_cancel]

theorem eucl_eq {N : ℕ} (v : Fin N → ℂ) : eucl v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin N))‖ := by
  rw [EuclideanSpace.norm_eq, eucl]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_eq_norm_sq]

theorem gramSchmidt_lengths : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), ∀ x ∈ GG k r, ∃ u : UT r → ℂ, (∀ a : Fin r, eucl (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = lA k r z x a.castSucc ∧ 0 < lA k r z x a.castSucc) ∧ ∀ a a' : Fin r, a ≠ a' → star (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) ⬝ᵥ (∑ b, upper u b a' • (x⁻¹ *ᵥ bvec (eI k r b))) = 0 := by
  intro k r z x hx
  classical
  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    obtain ⟨-, hsq, -⟩ := Formalism.QuantumDeterminants.hpkFacts k r
    have h := congrArg Matrix.det hsq
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.2 ⟨_, h⟩
  have hxu : IsUnit x.det := ((Formalism.QuantumDeterminants.uHGroup _ _ hH).2.2 x hx).1
  let L : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin x⁻¹
  have hLapp : ∀ v, L v = WithLp.toLp 2 (x⁻¹ *ᵥ v) := fun v => rfl
  let e : Fin r → Fin (2 * r + k + 1) → ℂ := fun b => bvec (eI k r b)
  let F : Fin r → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => L (e b)
  have hLinj : Function.Injective L := by
    intro v w hvw
    rw [hLapp, hLapp] at hvw
    have h1 : x⁻¹ *ᵥ v = x⁻¹ *ᵥ w := congrArg WithLp.ofLp hvw
    have h2 := congrArg (fun t => x *ᵥ t) h1
    simpa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hxu] using h2
  have heinj : Function.Injective (eI k r) := fun a b h => Fin.ext (by have h' := congrArg Fin.val h; exact h')
  have hlie : LinearIndependent ℂ e := by
    have h0 := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp _ heinj
    convert h0 using 1
    funext b
    simp [e, bvec]
  have hli : LinearIndependent ℂ F := hlie.map' L (LinearMap.ker_eq_bot.2 hLinj)
  obtain ⟨u, hu⟩ := exists_upper F
  have hG : ∀ a, WithLp.toLp 2 (∑ b, upper u b a • (x⁻¹ *ᵥ bvec (eI k r b))) = InnerProductSpace.gramSchmidt ℂ F a := by
    intro a
    have htl : ∀ v : Fin (2 * r + k + 1) → ℂ,
        WithLp.toLp 2 v = (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm v := fun v => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu a, htl, map_sum]
    simp only [map_smul]
    rfl
  have hset : ∀ a : Fin r, (Set.range fun b : {b : Fin r // b.val < (a.castSucc : Fin (r + 1)).val} =>
      bvec (eI k r b.1)) = e '' Set.Iio a := by
    intro a
    ext v
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, b.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  have hlA : ∀ a : Fin r, lA k r z x a.castSucc = ‖InnerProductSpace.gramSchmidt ℂ F a‖ := by
    intro a
    have hf : Formalism.QuantumDeterminants.fvec k r z a.castSucc = e a := by
      rw [Formalism.QuantumDeterminants.fvec, dite_eq_left (show (a.castSucc : Fin (r + 1)).val < r from a.isLt)]
      rfl
    have hspan : Submodule.span ℂ (F '' Set.Iio a) = (Submodule.span ℂ (e '' Set.Iio a)).map L := by
      rw [Submodule.map_span, Set.image_image]
    unfold lA
    rw [hf, hset a]
    apply IsLeast.csInf_eq
    constructor
    · have hm := sub_gs_mem F a
      rw [hspan] at hm
      obtain ⟨y, hy, hyL⟩ := Submodule.mem_map.1 hm
      refine ⟨y, hy, ?_⟩
      rw [eucl_eq, ← hLapp, map_sub, hyL]
      show _ = ‖F a - (F a - InnerProductSpace.gramSchmidt ℂ F a)‖
      rw [sub_sub_cancel]
    · rintro t ⟨y, hy, rfl⟩
      rw [eucl_eq, ← hLapp, map_sub]
      exact norm_gs_le F a (w := L y) (by rw [hspan]; exact Submodule.mem_map_of_mem hy)
  refine ⟨u, fun a => ⟨by rw [eucl_eq, hG a, hlA a], ?_⟩, fun a a' haa' => ?_⟩
  · rw [hlA a]
    exact norm_pos_iff.2 (InnerProductSpace.gramSchmidt_ne_zero (𝕜 := ℂ) a hli)
  · rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, hG a, hG a']
    exact InnerProductSpace.gramSchmidt_orthogonal (𝕜 := ℂ) F haa'

end GlobalTheory.Amp.GramFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqMeasureInterFundamentalDom
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

open scoped Pointwise in
theorem covol_eq_measure_inter_fund : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) (μ : Measure G) (fund A : Set G), (Γ : Set G).Countable → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → MeasurableSet A → (∀ γ ∈ Γ, ∀ x ∈ A, γ * x ∈ A) → covol (Γ : Set G) μ A = μ (A ∩ fund) := by
  intro G _ _ _ Γ μ fund A hc hμ hf hcov hdis hA hinv
  have : Countable Γ := hc.to_subtype
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s hs => by
    have h := hμ γ γ.2
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_const_mul (γ : G)) hs]
    rfl⟩
  have hF : IsFundamentalDomain Γ fund μ := by
    refine IsFundamentalDomain.mk'' hf.nullMeasurableSet ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun y => ?_
      obtain ⟨γ, hγ, h⟩ := hcov y
      exact ⟨⟨γ, hγ⟩, h⟩
    · intro γ hγ
      exact hdis γ γ.2 (fun h => hγ (Subtype.ext h))
    · intro γ
      exact (measurePreserving_smul γ μ).quasiMeasurePreserving
  apply le_antisymm
  · unfold covol
    refine iInf_le_of_le (A ∩ fund) (iInf_le_of_le (hA.inter hf) (iInf_le_of_le ?_ le_rfl))
    intro x hx
    obtain ⟨γ, hγ, h⟩ := hcov x
    exact ⟨γ, hγ, hinv γ hγ x hx, h⟩
  · unfold covol
    refine le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_
    rw [hF.measure_eq_tsum D]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro x ⟨hx, hxf⟩
    obtain ⟨γ, hγ, h⟩ := hD x hx
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hxf⟩
    rw [Set.mem_inv_smul_set_iff]
    exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducible
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem hcType_rep : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) := by
  intro k r z u Wp _ _ _ π _ hT hπ
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, hmul, hunit, hcont⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  refine ⟨hρ.1, ⟨h1, hmul⟩, continuousOn_clm_apply.mpr hcont, hunit, fun S hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  exact GlobalTheory.BesselFrame.conj_mem_UW hg'
    (PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1))

end GlobalTheory.ThA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWContinuousUnitaryIrreducibleStatement
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hcTypeW_continuous_unitary_irreducible : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Formalism.MainNotions.S.IsHCTypeW k r z u π → Nontrivial Wp ∧ IsCRepOn (UWset k r z) π ∧ ContinuousOn π (UWset k r z) ∧ (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) ∧ (∀ S : Submodule ℂ Wp, (∀ h ∈ UWset k r z, ∀ v ∈ S, π h v ∈ S) → S = ⊥ ∨ S = ⊤) := by
  first | exact @GlobalTheory.ThA.hcType_rep | exact GlobalTheory.ThA.hcType_rep | (intros; apply GlobalTheory.ThA.hcType_rep <;> assumption)
end
end
