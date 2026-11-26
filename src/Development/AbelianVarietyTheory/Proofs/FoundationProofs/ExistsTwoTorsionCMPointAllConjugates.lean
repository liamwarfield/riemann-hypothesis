module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoTorsionPt

theorem not_integral_half {N : ℕ} (hN : Odd N) {x : ℂ} (hx : IsIntegral ℤ x)
    (h : x + (starRingEnd ℂ) x = (N : ℂ) / 2) : False := by
  have h1 : IsIntegral ℤ ((starRingEnd ℂ) x) := hx.map (starRingEnd ℂ).toIntAlgHom
  have h2 : IsIntegral ℤ (algebraMap ℚ ℂ ((N : ℚ) / 2)) := by
    have : algebraMap ℚ ℂ ((N : ℚ) / 2) = (N : ℂ) / 2 := by simp
    rw [this, ← h]; exact hx.add h1
  have h3 : IsIntegral ℤ ((N : ℚ) / 2) :=
    (isIntegral_algebraMap_iff ).1 h2
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (N : ℚ) = 2 * (m : ℚ) := by
    have : (m : ℚ) = (N : ℚ) / 2 := by simpa using hm
    rw [this]; ring
  have h5 : (N : ℤ) = 2 * m := by exact_mod_cast h4
  obtain ⟨k, hk⟩ := hN
  omega

theorem isTwoTorsionCMPoint_of_odd_multiple (D : D7) (Λ : AddSubgroup ℂ) {δ : ℂ} (hδ : δ ≠ 0) {N : ℕ} (hN : Odd N)
    (hmem : δ * N ∈ Λ) (hint : ∀ w ∈ Λ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x) :
    GL3Theta.IsTwoTorsionPointUnkilled D Λ (δ * N / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * (δ * N / 2) = δ * N := by ring
    rw [this]; exact hmem
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_add (f := _), map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring

theorem lamOf_integral (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ w ∈ lamOf D cc δ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x := by
  intro w hw
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, -, rfl⟩ := hw
    refine ⟨_, ?_, rfl⟩
    have h0 : IsIntegral ℤ (c : D.host.K) := c.2
    exact h0.map (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  | zero => exact ⟨0, isIntegral_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, hx.add hy, by ring⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, hx.neg, by ring⟩

theorem norm_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    δ * (Ideal.absNorm cc : ℕ) ∈ lamOf D cc δ := by
  refine AddSubgroup.subset_closure ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩
  simp

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    Odd (Ideal.absNorm cc) :=
  Nat.coprime_two_right.1 (Nat.Coprime.coprime_mul_right_right h.1.2)

theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ h).2.1

theorem exists_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 :=
  ⟨_, isTwoTorsionCMPoint_of_odd_multiple D _ (delta_ne h) (odd_norm h) (norm_mem_lamOf D cc δ) (lamOf_integral D cc δ)⟩

theorem exists_bar {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) (Λ : AddSubgroup ℂ)
    (hΛ : Λ.map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D Λ t0 := by
  have hδ : (starRingEnd ℂ) δ ≠ 0 := by simpa using delta_ne h
  refine ⟨_, isTwoTorsionCMPoint_of_odd_multiple D Λ hδ (odd_norm h) ?_ ?_⟩
  · have h1 := norm_mem_lamOf D cc δ
    rw [← hΛ] at h1
    obtain ⟨w, hw, e⟩ := h1
    have e1 : (starRingEnd ℂ) w = δ * (Ideal.absNorm cc : ℕ) := e
    have e2 : w = (starRingEnd ℂ) δ * (Ideal.absNorm cc : ℕ) := by
      rw [← Complex.conj_conj w, e1, map_mul, map_natCast]
    rw [← e2]; exact hw
  · intro w hw
    have h1 : (starRingEnd ℂ) w ∈ lamOf D cc δ := by
      rw [← hΛ]; exact ⟨w, hw, rfl⟩
    obtain ⟨x, hx, e⟩ := lamOf_integral D cc δ _ h1
    refine ⟨(starRingEnd ℂ) x, hx.map (starRingEnd ℂ).toIntAlgHom, ?_⟩
    rw [← Complex.conj_conj w, e, map_mul]

theorem exists_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ M') ∧
      ∀ x ∈ M, x ∈ M' ∧ ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := algebraicClosure M ℂ) ρ
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, ?_, ?_⟩
  · intro x hx
    exact mem_algebraicClosure_iff.2 (hx.extendScalars (algebraMap ℚ M).injective)
  · intro x hx
    have hx' : x ∈ (algebraicClosure M ℂ).restrictScalars ℚ :=
      (algebraicClosure M ℂ).algebraMap_mem (⟨x, hx⟩ : M)
    refine ⟨hx', ?_⟩
    unfold TaylorLogMetric.liftM
    rw [dite_eq_left hx', dite_eq_left hx, ← hφ]
    rfl

theorem exists_point : ∀ D : D7, t0Ex D := by
  intro D cc δ hc
  refine ⟨exists_lamOf hc, ?_⟩
  intro M ρ h2 h3
  obtain ⟨M', ρ', halg, hext⟩ := exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    rw [e]
    exact exists_lamOf hc'
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    refine exists_bar hc' _ ?_
    rw [← e]
    exact (congrArg Tor.abelian₂ hbar).symm

end GlobalTheory.TwoTorsionPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates : ∀ D : D7, t0Ex D := by
  first | exact @GlobalTheory.TwoTorsionPt.exists_point | exact GlobalTheory.TwoTorsionPt.exists_point | (intros; apply GlobalTheory.TwoTorsionPt.exists_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory Matrix
open scoped NNReal

noncomputable section

namespace GlobalTheory.DetSqrtCover

variable {p q : ℕ}

theorem exp_add_smul (X : Mat p q) (s t : ℝ) :
    NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)

theorem det_exp (X : Mat p q) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact GlobalTheory.RealPar.Cover.hasDerivAt_det_exp X
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← exp_add_smul, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2

theorem exp_mul_exp_neg (X : Mat p q) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Mat p q) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

def expGL (X : Mat p q) : GL (Ix p q) ℂ :=
  ⟨NormedSpace.exp X, NormedSpace.exp (-X), exp_mul_exp_neg X, exp_neg_mul_exp X⟩

theorem continuous_mexp : Continuous fun X : Mat p q => NormedSpace.exp X := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem continuous_expGL : Continuous (expGL : Mat p q → GL (Ix p q) ℂ) :=
  Units.continuous_iff.2 ⟨continuous_mexp, continuous_mexp.comp continuous_neg⟩

theorem expGL_mem {X : Mat p q} (hX : X ∈ upq p q) : expGL X ∈ Formalism.UG.Upq p q := by
  have hJ : Jm p q * Jm p q = 1 := GlobalTheory.RealPar.KStabLie.Jm_sq p q
  let U : (Mat p q)ˣ := ⟨Jm p q, Jm p q, hJ, hJ⟩
  have h1 : Xᴴ = U.val * (-X) * U⁻¹.val := by
    change Xᴴ = Jm p q * (-X) * Jm p q
    have h : Xᴴ * Jm p q = Jm p q * (-X) := by
      rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← h, Matrix.mul_assoc, hJ, Matrix.mul_one]
  have h2 : (NormedSpace.exp X)ᴴ = Jm p q * NormedSpace.exp (-X) * Jm p q := by
    rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_units_conj]
    rfl
  rw [GlobalTheory.RealPar.mem_Upq]
  change (NormedSpace.exp X)ᴴ * Jm p q * NormedSpace.exp X = Jm p q
  rw [h2, Matrix.mul_assoc _ (Jm p q) (Jm p q), hJ, Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

def expHalf (X : Mat p q) : ℂˣ := Units.mk0 (Complex.exp (X.trace / 2)) (Complex.exp_ne_zero _)

theorem continuous_expHalf : Continuous (expHalf : Mat p q → ℂˣ) :=
  Units.isEmbedding_val₀.continuous_iff.2
    (Complex.continuous_exp.comp (continuous_id.matrix_trace.div_const 2))

theorem expHalf_sq (X : Mat p q) : ((expHalf X : ℂˣ) : ℂ) ^ 2 = (NormedSpace.exp X).det := by
  rw [det_exp, expHalf, Units.val_mk0, sq, ← Complex.exp_add, add_halves]

def cover (p q : ℕ) : Subgroup (GL (Ix p q) ℂ × ℂˣ) where
  carrier := {z | z.1 ∈ Formalism.UG.Upq p q ∧ (z.2 : ℂ) ^ 2 = (z.1 : Mat p q).det}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    simp only [Prod.snd_mul, Prod.fst_mul, Units.val_mul, Matrix.det_mul, mul_pow, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
    simp only [Prod.snd_inv, Prod.fst_inv, Units.val_inv_eq_inv_val, inv_pow, ha.2, Matrix.coe_units_inv,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv']⟩

theorem isClosed_cover : IsClosed (cover p q : Set (GL (Ix p q) ℂ × ℂˣ)) := by
  have c1 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.1 : Mat p q) := Units.continuous_val.comp continuous_fst
  have c2 : Continuous fun z : GL (Ix p q) ℂ × ℂˣ => (z.2 : ℂ) := Units.continuous_val.comp continuous_snd
  exact (isClosed_eq ((c1.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul c1)
    (continuous_const (y := Jm p q))).inter (isClosed_eq (c2.pow 2) c1.matrix_det)

instance locallyCompact_cover : LocallyCompactSpace (cover p q) := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  haveI : LocallyCompactSpace (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Ix p q) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace ℂᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace ℂˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact isClosed_cover.locallyCompactSpace

instance measurable_cover : MeasurableSpace (cover p q) := borel _

instance borel_cover : BorelSpace (cover p q) := ⟨rfl⟩


open Classical in
def expLift (X : Mat p q) : cover p q :=
  if h : X ∈ upq p q then ⟨(expGL X, expHalf X), expGL_mem h, expHalf_sq X⟩ else 1

theorem expLift_val {X : Mat p q} (h : X ∈ upq p q) : (expLift X).1 = (expGL X, expHalf X) := by
  rw [expLift, dite_eq_left h]

def grpOf (p q : ℕ) (ν : Measure (cover p q)) [ν.IsHaarMeasure] : GrpData p q where
  G := cover p q
  haar := ν
  cov := (MonoidHom.fst _ _).comp (cover p q).subtype
  sq := (MonoidHom.snd _ _).comp (cover p q).subtype
  cov_mem x := x.2.1
  sq_sq x := x.2.2
  bij g hg w hw := ⟨⟨(g, w), hg, hw⟩, ⟨rfl, rfl⟩, fun _ hy => Subtype.ext (Prod.ext hy.1 hy.2)⟩
  emb := Topology.IsEmbedding.subtypeVal
  expt := expLift
  expt_cov X hX := by
    change ((expLift X).1.1 : Mat p q) = _
    rw [expLift_val hX]; rfl
  expt_cont := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (continuous_expGL.prodMk continuous_expHalf).continuousOn.congr fun X hX => expLift_val hX
  expt_zero := by
    apply Subtype.ext
    rw [expLift_val (by simp [upq])]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact NormedSpace.exp_zero
    · simp [expHalf]
  expt_add X hX s t := by
    apply Subtype.ext
    have h := GlobalTheory.RealPar.KStabLie.smul_mem_upq hX
    rw [Subgroup.coe_mul, expLift_val (h _), expLift_val (h _), expLift_val (h _)]
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact exp_add_smul X s t
    · simp [expHalf, add_smul, add_div, Complex.exp_add]

def covHom (T : GrpData p q) : T.G →* UpqT p q :=
  (T.cov.codRestrict (Formalism.UG.Upq p q) T.cov_mem : T.G →* Formalism.UG.Upq p q)

theorem continuous_covU (T : GrpData p q) : Continuous T.covU :=
  Continuous.subtype_mk (continuous_fst.comp T.emb.continuous) _

theorem surjective_covU (T : GrpData p q) : Function.Surjective T.covU := by
  rintro ⟨g, hg⟩
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((g : Mat p q).det) two_pos
  have h0 : w ≠ 0 := by
    rintro rfl
    exact g.det_ne_zero (by rw [← hw]; simp)
  obtain ⟨x, hx, -⟩ := T.bij g hg (Units.mk0 w h0) hw
  exact ⟨x, Subtype.ext hx.1⟩

theorem isProperMap_covU (T : GrpData p q) : IsProperMap T.covU := by
  haveI : T2Space (UpqT p q) := inferInstanceAs (T2Space (Formalism.UG.Upq p q))
  haveI : LocallyCompactSpace (UpqT p q) :=
    (UpqUnimodular.modelEquiv p q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  refine isProperMap_iff_isCompact_preimage.2 ⟨continuous_covU T, fun K hK => ?_⟩
  have hS : IsCompact ((Units.val : ℂˣ → ℂ) ⁻¹' Metric.sphere 0 1) := by
    refine (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff ?_).2 (isCompact_sphere 0 1)
    intro z hz
    have : z ≠ 0 := by rintro rfl; simp at hz
    exact ⟨Units.mk0 z this, rfl⟩
  have hK' : IsCompact ((fun g : Formalism.UG.Upq p q => g.1) '' K) := hK.image continuous_subtype_val
  refine ((GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).isCompact_preimage (hK'.prod hS)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_covU T)) fun x hx => ⟨⟨T.covU x, hx, rfl⟩, ?_⟩
  simpa using GlobalTheory.RealPar.Cover.norm_sq x

theorem isHaarMeasure_map_covU (T : GrpData p q) : (T.haar.map T.covU).IsHaarMeasure := by
  haveI : IsTopologicalGroup (UpqT p q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  haveI : T2Space (UpqT p q) := inferInstanceAs (T2Space (Formalism.UG.Upq p q))
  haveI : LocallyCompactSpace (UpqT p q) :=
    (UpqUnimodular.modelEquiv p q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  exact Measure.isHaarMeasure_map T.haar (covHom T) (continuous_covU T) (surjective_covU T)
    (isProperMap_iff_tendsto_cocompact.1 (isProperMap_covU T)).2

theorem exists_grpData_map_haar : ∀ (p q : ℕ) (μ : Measure (UpqT p q)), μ.IsHaarMeasure →
    ∃ T : GrpData p q, Measure.map T.covU T.haar = μ := by
  intro p q μ hμ
  haveI := isHaarMeasure_map_covU (grpOf p q Measure.haar)
  obtain ⟨t, ht⟩ := GlobalTheory.CompactDualUnique.exists_eq_smul μ
    ((grpOf p q Measure.haar).haar.map (grpOf p q Measure.haar).covU)
  have h0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact isOpen_univ.measure_ne_zero μ Set.univ_nonempty (by rw [ht]; rfl)
  haveI : (t • (Measure.haar : Measure (cover p q))).IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ h0
  refine ⟨grpOf p q (t • Measure.haar), ?_⟩
  rw [ht]
  haveI : BorelSpace (UpqT p q) := ⟨rfl⟩
  exact Measure.map_smul _ (continuous_covU _).aemeasurable

end GlobalTheory.DetSqrtCover

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaSpan

open GlobalTheory.TripleIntertwiner

section
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]

theorem sum_translate {M : Type} [AddCommMonoid M] {A₀ A : AddSubgroup V} [Fintype (A ⧸ A₀.addSubgroupOf A)]
    (g : V → M) (hg : ∀ x ∈ A, ∀ l ∈ A, l ∈ A₀ → g (x + l) = g x) {a : V} (ha : a ∈ A) :
    ∑ q : A ⧸ A₀.addSubgroupOf A, g (a + rep q) = ∑ q : A ⧸ A₀.addSubgroupOf A, g (rep q) := by
  let q₀ : A ⧸ A₀.addSubgroupOf A := QuotientAddGroup.mk ⟨a, ha⟩
  rw [← Equiv.sum_comp (Equiv.addLeft q₀) (fun q => g (rep q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨l, hl0, hl, h3⟩ := rep_add q₀ q
  obtain ⟨l', hl0', hl', h4⟩ := rep_mk (B := A₀) (⟨a, ha⟩ : A)
  show _ = g (rep (q₀ + q))
  rw [h3, hg _ (add_mem (rep_mem _) (rep_mem _)) _ hl0 hl, h4, add_right_comm,
    hg _ (add_mem ha (rep_mem _)) _ hl0' hl']

variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}

theorem mem_span_translates (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0) (W0 : ∀ f, W 0 f = f)
    {A : AddSubgroup V} (m : ℕ) (s : V →+ V) (hs : ∀ v, m • s v = v) (hs' : ∀ v, s (m • v) = v)
    [Fintype (A ⧸ (subLa m A).addSubgroupOf A)] (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (P : Submodule ℂ F) (hP : ∀ x, ∀ f ∈ P, W x f ∈ P) (e : F)
    (line : ∀ g ∈ P, (∀ x ∈ A, W x g = g) → ∃ t : ℂ, g = t • e)
    (f : F) (hfP : f ∈ P) (hf : ∀ x ∈ A, W (m • x) f = f) :
    f ∈ Submodule.span ℂ {g | ∃ a ∈ A, g = W (s a) e} := by
  obtain ⟨H1, H2, H3, H4⟩ := H
  have c0 : ∀ y, c 0 y = 1 := fun y => by
    have := H2 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (H4 0 y)).1 this.symm
  have c0' : ∀ y, c y 0 = 1 := fun y => by
    have := H3 y 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (H4 y 0)).1 this.symm
  have cm : ∀ (k : ℕ) x y, c (k • x) y = c x (k • y) := by
    intro k x y
    induction k with
    | zero => rw [zero_smul, zero_smul, c0, c0']
    | succ k ih => rw [succ_nsmul, succ_nsmul, H2, H3, ih]
  have cs : ∀ x y, c (s x) y = c x (s y) := fun x y => by
    conv_lhs => rw [← hs y, ← cm, hs]
  have comm : ∀ x y g, W x (W y g) = (c x y / c y x) • W y (W x g) := by
    intro x y g
    rw [H1, H1, smul_smul, div_mul_cancel₀ _ (H4 _ _), add_comm]
  have hA0 : ∀ l ∈ subLa m A, ∃ x ∈ A, l = m • x := by
    rintro l ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  let G : V → F := fun a => ∑ q : A ⧸ (subLa m A).addSubgroupOf A, W (rep q) (W (s (-a)) f)
  have hG : ∀ a ∈ A, ∃ t : ℂ, G a = t • e := by
    intro a ha
    refine line _ (P.sum_mem fun q _ => hP _ _ (hP _ _ hfP)) fun x hx => ?_
    have := sum_translate (A₀ := subLa m A) (fun y => W y (W (s (-a)) f)) (fun y hy l hl hl' => by
      obtain ⟨b, hb, rfl⟩ := hA0 l hl'
      have h1 : W (m • b) (W (s (-a)) f) = W (s (-a)) f := by
        rw [comm, hf b hb, cm, ← cm m (s _), hs, cA _ hb _ (neg_mem ha), cA _ (neg_mem ha) _ hb]; simp
      have h2 := H1 y (m • b) (W (s (-a)) f)
      rw [h1, cA _ hy _ hl, one_smul] at h2
      exact h2.symm) hx
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [H1, cA _ hx _ (rep_mem q), one_smul]
  have hWG : ∀ a, (c (s a) (s (-a)))⁻¹ • W (s a) (G a) =
      ∑ q : A ⧸ (subLa m A).addSubgroupOf A, (c a (s (rep q)) / c (s (rep q)) a) • W (rep q) f := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [comm, H1 (s a), ← map_add (f := _), add_neg_cancel, map_zero, W0, map_smul, smul_smul, smul_smul, cs a (rep q),
      ← cs (rep q) a]
    congr 1
    have := H4 (s a) (s (-a))
    field_simp
  have hχ : ∀ q : A ⧸ (subLa m A).addSubgroupOf A,
      (∑ u : A ⧸ (subLa m A).addSubgroupOf A, c (rep u) (s (rep q)) / c (s (rep q)) (rep u)) • W (rep q) f =
        if q = 0 then (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) • f else 0 := by
    intro q
    split_ifs with h
    · obtain ⟨l, -, hl, h3⟩ := rep_mk (B := subLa m A) (0 : A)
      obtain ⟨b, hb, rfl⟩ := hA0 l hl
      have h4 : rep q = m • b := by rw [h]; simpa using h3
      have h5 : s (rep q) = b := by rw [h4, hs']
      rw [h5, h4, hf b hb, Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun u _ => by
        rw [cA _ hb _ (rep_mem u), cA _ (rep_mem u) _ hb, div_one]]
      simp
    · have hv : s (rep q) ∉ A := by
        intro hv
        apply h
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
        exact ⟨_, hv, hs _⟩
      obtain ⟨x₀, hx₀, hne⟩ : ∃ x ∈ A, c x (s (rep q)) ≠ c (s (rep q)) x := by
        by_contra hh
        push_neg at hh
        exact hv (hsd _ hh)
      have := sum_translate (A₀ := subLa m A) (fun y => c y (s (rep q)) / c (s (rep q)) y) (fun y hy l hl hl' => by
        obtain ⟨b, hb, rfl⟩ := hA0 l hl'
        simp only [H2, H3]
        rw [cm, ← cm m (s _), hs, cA _ hb _ (rep_mem q), cA _ (rep_mem q) _ hb, mul_one, mul_one]) hx₀
      simp only [H2, H3, mul_div_mul_comm, ← Finset.mul_sum] at this
      have h1 : c x₀ (s (rep q)) / c (s (rep q)) x₀ ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq (H4 _ _)]; exact hne
      have h2 : ∑ u : A ⧸ (subLa m A).addSubgroupOf A, c (rep u) (s (rep q)) / c (s (rep q)) (rep u) = 0 := by
        by_contra h0
        exact h1 ((mul_eq_right₀ h0).1 this)
      rw [h2, zero_smul]
  have hsum : ∑ u : A ⧸ (subLa m A).addSubgroupOf A, (c (s (rep u)) (s (-rep u)))⁻¹ • W (s (rep u)) (G (rep u)) =
      (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) • f := by
    simp only [hWG]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hχ]
    simp
  have hc : (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Submodule.smul_mem_iff _ hc, ← hsum]
  refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_
  obtain ⟨t, ht⟩ := hG _ (rep_mem u)
  rw [ht, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rep_mem u, rfl⟩)

end

theorem wd_differentiable (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

theorem theta_span : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 := by
  intro D cc δ hc N N' e0 he he0 F hF
  obtain ⟨hFd, m, hm, hF⟩ := hF
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨l1, l2, -, l4, l5, -, -⟩ := GlobalTheory.ThetaLine.theta_line D hg cc δ hc N N' _ k
  have hrat := fun x hx => GlobalTheory.ThetaInter.klat_rat hg.1 k (x := x) hx
  change e0 ∈ ThSp D _ (La0 D (tor0 D cc δ) N N') at he
  set A := La0 D (tor0 D cc δ) N N'
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) :=
    GlobalTheory.ThetaInter.finite_quot l5 fun x hx => ⟨m, hm, x, hx, rfl⟩
  letI : Fintype (A ⧸ (subLa m A).addSubgroupOf A) := Fintype.ofFinite _
  have H := wLin_heis D (tor0 D cc δ) (N := N) (N' := N')
  have fix : ∀ x ∈ A, wLin D (tor0 D cc δ) x e0 = e0 := fun x hx => by
    show Wd D _ x e0 = e0
    rw [l2 x hx]
    exact funext (he.2 x hx)
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  let P : Submodule ℂ (VC D N N' → ℂ) :=
    { carrier := {G | Differentiable ℂ G}
      add_mem' := fun ha hb => Differentiable.add ha hb
      zero_mem' := differentiable_const _
      smul_mem' := fun a _ h => Differentiable.const_smul h a }
  have key := mem_span_translates (c := fun x y => Complex.exp (cocExp D (tor0 D cc δ) x y)) H
    (fun f => wd_zero D _ f) (A := A) m (DistribSMul.toAddMonoidHom _ (m : ℂ)⁻¹)
    (fun v => by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hm'])
    (fun v => by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hm'])
    (fun x hx y hy => by
      have := H.1 x y e0
      rw [fix y hy, fix x hx, fix _ (A.add_mem hx hy)] at this
      exact smul_left_injective ℂ he0 (this.symm.trans (one_smul ℂ e0).symm))
    (fun v hv => l4 v fun y hy => im_int_of_comm D _ y v (hv y hy))
    P (fun x f hf => wd_differentiable D _ x hf) e0
    (fun g hg hfix => l1 g ⟨hg, fun x hx z => by
      have := hfix x hx
      change Wd D _ x g = g at this
      rw [l2 x hx] at this
      exact congrFun this z⟩ e0 he he0)
    F hFd hF
  obtain ⟨n, r, g, hsum⟩ := Submodule.mem_span_set'.1 key
  have : ∀ i, ∃ z, (g i : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 := by
    intro i
    obtain ⟨a, ha, h⟩ := (g i).2
    obtain ⟨B, rfl⟩ := hrat a ha
    refine ⟨((m : D.host.K)⁻¹) • B, h.trans ?_⟩
    unfold pt
    rw [GlobalTheory.ThetaInter.embV_smul hg.1, smul_comm δ]
    simp [wLin]
  choose z hz using this
  exact ⟨n, r, z, by rw [← hsum]; simp only [hz]⟩

end GlobalTheory.ThetaSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuumStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_span_rational_translates_vacuum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 := by
  first | exact @GlobalTheory.ThetaSpan.theta_span | exact GlobalTheory.ThetaSpan.theta_span | (intros; apply GlobalTheory.ThetaSpan.theta_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriples
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTriple

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem theta_cocycle_eq_exp_hermitian (T : Tor D) (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T (w0 D • x) y).im : ℂ)) := by
  have h : Hf D T (w0 D • x) y = w0 D * Hf D T x y := by
    rw [GlobalTheory.ThetaLine.Hf_eq, GlobalTheory.ThetaLine.sq_smul_left, GlobalTheory.ThetaLine.Hf_eq, mul_div_assoc]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  rw [bc, h, Complex.mul_im, h1, h2]
  congr 1
  push_cast
  ring

theorem nice_of_klat (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    Nice D (tor0 D cc δ) A := by
  obtain ⟨-, h0, h1, h2, -, -, -⟩ :=
    GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h0, fun x hx y hy => ?_, fun x hx => h2 x fun y hy => ?_⟩
  · obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have hw := GlobalTheory.ThetaInter.klat_smul_mem hA a hx
    rw [ha] at hw
    obtain ⟨m, hm⟩ := h1 _ hw y hy
    rw [theta_cocycle_eq_exp_hermitian, hm, Complex.exp_eq_one_iff]
    exact ⟨-m, by push_cast; ring⟩
  · have h := hx y hy
    rw [bc_comm, mul_eq_right₀ (bc_ne_zero _ _ _ _), Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨-n, ?_⟩
    have h3 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D (tor0 D cc δ) x y).im : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast
      linear_combination -hn
    exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h3

theorem index_ne_zero (hc : Crv D cc δ) {A₁ A₂ : AddSubgroup (VC D N N')} (h₁ : KLat D (tor0 D cc δ) A₁)
    (h₂ : KLat D (tor0 D cc δ) A₂) : (A₁.addSubgroupOf A₂).index ≠ 0 := by
  haveI := GlobalTheory.ThetaInter.klat_finite (GlobalTheory.InducedType.induced_type D).1.1 hc.1.1 h₁ h₂
    (GlobalTheory.ThetaInter.klat_facts hc h₂).1
  exact AddSubgroup.index_ne_zero_of_finite

theorem iop_self {T : Tor D} {A : AddSubgroup (VC D N N')} (hA : Nice D T A) {e : VC D N N' → ℂ}
    (he : e ∈ ThSp D T A) : Iop D T A A e = e := by
  rw [hA.Iop_eq]
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by simp
  have hc : Nat.card (A ⧸ A.addSubgroupOf A) = 1 := hi
  obtain ⟨hs, ⟨q₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hc
  rw [finsum_eq_single _ q₀ (fun q hq => absurd (Subsingleton.elim q q₀) hq), hi,
    ((hA.mem_ThSp e).1 he).2 _ (Quotient.out q₀ : A).2]
  simp

theorem klat_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  intro D cc δ hc N N'
  refine ⟨fun A hA => nice_of_klat hc hA, fun A₁ A₂ h₁ h₂ _ _ _ => index_ne_zero hc h₁ h₂,
    fun A hA e he => iop_self (nice_of_klat hc hA) he, fun A₁ A₂ A₃ h₁ h₂ h₃ e he h0 => ?_⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.TripleIntertwiner.triple_constant D cc δ hc N N' A₁ A₂ A₃ h₁ h₂ h₃ e he
  exact ⟨μ, nice_of_klat hc h₁, nice_of_klat hc h₂, nice_of_klat hc h₃, index_ne_zero hc h₁ h₂,
    index_ne_zero hc h₂ h₃, index_ne_zero hc h₁ h₃, he, h0, hμ, h⟩

end GlobalTheory.ThetaTriple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLatticesFormSelfDualTriplesStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattices_form_selfDual_triples : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → Nice D (tor0 D cc δ) A) ∧ (∀ A₁ A₂ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → (A₁.addSubgroupOf A₂).index ≠ 0) ∧ (∀ A : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A → ∀ e ∈ ThSp D (tor0 D cc δ) A, Iop D (tor0 D cc δ) A A e = e) ∧ ∀ A₁ A₂ A₃ : AddSubgroup (VC D N N'), KLat D (tor0 D cc δ) A₁ → KLat D (tor0 D cc δ) A₂ → KLat D (tor0 D cc δ) A₃ → ∀ e ∈ ThSp D (tor0 D cc δ) A₁, e ≠ 0 → ∃ μ, Trip D (tor0 D cc δ) A₁ A₂ A₃ e μ := by
  first | exact @GlobalTheory.ThetaTriple.klat_triples | exact GlobalTheory.ThetaTriple.klat_triples | (intros; apply GlobalTheory.ThetaTriple.klat_triples <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolDS

variable {p q : ℕ}

instance t2Space_cuspAdeles (T : GrpData p q) : T2Space T.G := T.emb.t2Space

instance instSecondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_val₀.secondCountableTopology
  exact T.emb.secondCountableTopology

instance instLocallyCompact (T : GrpData p q) : LocallyCompactSpace T.G := by
  haveI : LocallyCompactSpace (Mat p q) := inferInstanceAs (LocallyCompactSpace (Ix p q → Ix p q → ℂ))
  exact (GlobalTheory.RealPar.SqInt.isClosedEmbedding_emb T).locallyCompactSpace

end GlobalTheory.HolDS

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpan
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Vacuum

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  exact h2 ▸ (h1 1).2

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ)
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, map_nsmul]
  exact smul_comm _ _ _

theorem map_nsmul_inc (D : D7) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    (m • z).map (inc D) = m • z.map (inc D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]

theorem nsmul_inv_smul {X : Type*} [AddCommGroup X] [Module ℚ X] {m : ℕ} (hm : 0 < m) (a : X) :
    m • ((m : ℚ)⁻¹ • a) = a := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hm.ne'), one_smul]

theorem level_fixed {D : D7} (hg : admG1 D) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {N N' : ℕ}
    {w : 𝓞 D.host.E} {γ : XA D N N' → XA D N N' → ℂ}
    {WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N'}
    (hM : GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA) (v : TTs D (tor0 D cc δ) N N') (m : ℕ)
    (hv : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) (m • x) v = v) :
    ∀ b ∈ latA D cc N N', WA (m • b) v = v := by
  intro b hb
  obtain ⟨-, -, -, hW, hC⟩ := hM
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  obtain ⟨m', hm', h⟩ := hC (m • b) v
  obtain ⟨z, a, ha, hz⟩ := h3 b m' hm'
  have hz' : pt D (tor0 D cc δ) δ z ∈ La0 D (tor0 D cc δ) N N' := by
    rw [← h1, hz]
    exact add_mem hb (nsmul_mem ha _)
  have e : (m • z).map (inc D) = m • b + m' • (m • a) := by
    rw [map_nsmul_inc, hz, smul_add, smul_comm m m' a]
  rw [← h _ (nsmul_mem ha m), ← e]
  apply Subtype.ext
  rw [hW, pt_nsmul]
  exact hv _ hz'

theorem vacuum_fixed_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  intro D hg cc δ hc N N' w γ WA hM e0 he0 hne
  obtain ⟨hL, hWd, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hg cc δ hc N N' (La0 D (tor0 D cc δ) N N')
    (Or.inr ⟨_, _, sd_std D _, sd_std D _, rfl⟩)
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.completedStandardAdelicLattice_properties D hg cc δ hc N N'
  have h0 : ∀ x ∈ La0 D (tor0 D cc δ) N N', Wd D (tor0 D cc δ) ((1 : ℕ) • x) e0 = e0 := fun x hx => by
    rw [one_smul, hWd x hx]
    funext z
    exact he0.2 x hx z
  have hT : e0 ∈ TTs D (tor0 D cc δ) N N' := ⟨he0.1, 1, one_pos, h0⟩
  refine ⟨hT, fun a ha => ?_, ?_⟩
  · have := level_fixed hg hc hM ⟨e0, hT⟩ 1 h0 a ha
    rwa [one_smul] at this
  refine GlobalTheory.T.span_heisenberg_translates_vacuum_eq_top hM.1 _ hM.2.1 _ (fun v hv => ?_) (fun v => ?_)
  · have hv' : (v : VC D N N' → ℂ) ∈ ThSp D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := by
      refine ⟨v.2.1, fun x hx y => ?_⟩
      have e := hWd x hx v
      obtain ⟨z, rfl⟩ := h2 x hx
      rw [← hM.2.2.2.1, hv _ ((h1 z).2 hx)] at e
      exact (congrFun e y).symm
    obtain ⟨c, hc'⟩ := hL _ hv' e0 he0 hne
    exact ⟨c, Subtype.ext hc'⟩
  · obtain ⟨-, m, hm, hv⟩ := v.2
    refine ⟨(latA D cc N N').comap (m • LinearMap.id), GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hg cc δ hc N N' m hm _ (fun ζ hζ => hζ),
      fun a _ hT' => ?_⟩
    have hb : (m : ℚ)⁻¹ • a ∈ latA D cc N N' := by
      refine (hM.2.1 _).2 fun a' ha' => ?_
      have ht : (m : ℚ)⁻¹ • a' ∈ (latA D cc N N').comap (m • LinearMap.id) := by
        change m • ((m : ℚ)⁻¹ • a') ∈ latA D cc N N'
        rwa [nsmul_inv_smul hm]
      rw [← nsmul_inv_smul hm a', hM.1.nsmul_right, ← hM.1.nsmul_left, nsmul_inv_smul hm]
      exact hT' _ ht
    have := level_fixed hg hc hM v m hv _ hb
    rwa [nsmul_inv_smul hm] at this

end GlobalTheory.FinWeil.Vacuum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdelicWeilVacuumFixedAndTranslatesSpanStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∃ h : e0 ∈ TTs D (tor0 D cc δ) N N', Fixes WA (latA D cc N N') ⟨e0, h⟩ ∧ Submodule.span ℂ (Set.range fun ζ => WA ζ ⟨e0, h⟩) = ⊤ := by
  first | exact @GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | exact GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span | (intros; apply GlobalTheory.FinWeil.Vacuum.vacuum_fixed_span <;> assumption)
end
end
