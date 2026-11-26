module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionReal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedValues D := by
  first | exact @GlobalTheory.MixValues.mixed_values | exact GlobalTheory.MixValues.mixed_values | (intros; apply GlobalTheory.MixValues.mixed_values <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KmapEq
noncomputable section

namespace GlobalTheory.KerDia

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre}

def ent (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {b : (I.stp u a i).β} {b' : (I.stp u a (i + 1)).β}
    (p : (I.stp u a i).D b) (p' : (I.stp u a (i + 1)).D b') :
    (Fr B.fields.emb B.embLL (B.R.N i) → ℂ) →ₗ[ℂ] (Fr B.fields.emb B.embLL (B.R.N (i + 1)) → ℂ) :=
  (I.rho u a i b p * I.rho' u a i b' p') • (((I.chain l u a).divDe i).comp
    ((fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ∘ₗ jetMap (jetC I.J.cD (I.th u a i b b' p p')) 0 ∘ₗ
      Formalism.L2.Col.polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))).comp ((I.chain l u a).sharp i)))

theorem Kmap_eq (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) :
    (I.chain l u a).Kmap i c c' = ent I l u a i ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') := rfl

end GlobalTheory.KerDia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.SupThetaGrowth

theorem om_sup_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (height S g * height T h) ^ A := by
  intro D ψ S T χS χT om hom f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨N, hN⟩ := GlobalTheory.WeilWordGrowth.om_pointwise D ψ S T χS χT om hom θ hθ
  obtain ⟨c, -, hc⟩ := hN f hf
  exact ⟨c, N, hc⟩

end GlobalTheory.SupThetaGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_thetaFun_sup_moderate_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (height S g * height T h) ^ A := by
  first | exact @GlobalTheory.SupThetaGrowth.om_sup_growth | exact GlobalTheory.SupThetaGrowth.om_sup_growth | (intros; apply GlobalTheory.SupThetaGrowth.om_sup_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardChar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilConjAdjoint

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7} {S T : HSp D}

theorem conjTarget_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjTarget om (g, negGA T h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjTarget] using this

theorem conjSource_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjSource om (negGA S g, h) (cj id f) = cj id (om (g, h) f) := by
  have := cjEnd_cj (Equiv.refl (WO S T)) (om (g, h)) f
  simpa [conjSource] using this

theorem conjAdjoint_cj (om : Rep S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    conjAdjoint om (h, g) (cj (dagger T S) f) = cj (dagger T S) (om (g, h) f) :=
  cjEnd_cj (daggerEquiv S T) (om (g, h)) f

theorem conjAdjoint_holds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ S T : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.ConjAdjoint ψ S T := by
  intro D ψ hψ S T
  obtain ⟨hθ, hH⟩ := GlobalTheory.T.thetaHeisenberg_conjugation_negHermitianSpace D ψ hψ S T
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T
  refine ⟨hθ, hH, fun χS χT om H => ?_, fun χS χT om H => ?_, d1, d2, d3, d4, fun χS χT om H => ?_⟩
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).1
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjTarget_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ S (negSp T) _ _ om' _ H' H1 _ _ ((hθ f).1.2 hf)
  · have H1 := (GlobalTheory.T.isWeilDatum_conj_negHermitianSpaces D ψ S T χS χT om H).2
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjSource_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ (negSp S) T _ _ om' _ H' H1 _ _ ((hθ f).2.2 hf)
  · have H1 := GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S T χS χT om H
    refine ⟨H1, fun om' H' g h f hf => ?_⟩
    rw [← conjAdjoint_cj]
    exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hψ T S _ _ om' _ H' H1 _ _ ((d3 f).2 hf)

end GlobalTheory.WeilConjAdjoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardCharStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilConjugationAdjointRule_standard_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.ConjAdjoint ψ S T := by
  first | exact @GlobalTheory.WeilConjAdjoint.conjAdjoint_holds | exact GlobalTheory.WeilConjAdjoint.conjAdjoint_holds | (intros; apply GlobalTheory.WeilConjAdjoint.conjAdjoint_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlices
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlices
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposS

variable {D : D7}

theorem symplOH_zero_right {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0

theorem symplOH_zero_left {S T : HSp D} (x : WO S T) : symplOH S T 0 x = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 x

theorem psi_neg_mul (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

variable {S A B T : HSp D} (o : OrthDec S A B)

theorem symm_add (r u : WO A T) (y : WO B T) :
    (o.resS T).symm (u + r, y) = (o.resS T).symm (u, y) + (o.resS T).symm (r, 0) := by
  rw [← map_add (f := _)]; simp

theorem sympl_ext_right (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (u, y)) ((o.resS T).symm (r, 0)) = symplOH A T u r := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_right]

theorem sympl_ext_left (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (r, 0)) ((o.resS T).symm (u, y)) = symplOH A T r u := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_left]

def ext0 (T : HSp D) : WO A T →+ WO S T := (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem matrixExtendByZero_apply (r : WO A T) : ext0 o T r = (o.resS T).symm (r, 0) := rfl

theorem continuous_wittExtendByZero : Continuous (ext0 o T) :=
  (o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)

theorem matrixExtendByZero_map {R : Type} [Semiring R] (f : AE D →+* R) (r : WO A T) (h : r.map f = 0) : (ext0 o T r).map f = 0 := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.map_mul, h, Matrix.zero_mul]

theorem homExtensionByZeroOrthDecomp_rational (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) : ext0 o T (ratW T A γ) = ratW T S (γ * o.qA) := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, ratW, ratW, rat, Matrix.map_mul]

end GlobalTheory.SuperposS

namespace GlobalTheory.SuperposS

theorem superpos_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  intro D ψ hψ S A B T o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hFm : ∀ u : WO A T, Measurable fun w => F ((o.resS T).symm (u, k w)) := fun u =>
    (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id))).measurable.comp hk
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    beta_reduce
    have e : ∀ w, a w * F ((o.resS T).symm (ratW T A γ + u, k w)) =
        ψ (-symplOH A T (ratW T A γ) u) * (a w * F ((o.resS T).symm (u, k w))) := by
      intro w
      rw [add_comm, symm_add, add_comm, ← matrixExtendByZero_apply, homExtensionByZeroOrthDecomp_rational, hF.quasi, ← homExtensionByZeroOrthDecomp_rational, matrixExtendByZero_apply, sympl_ext_left]
      ring
    simp_rw [e]
    exact integral_const_mul _ _
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap (ext0 o T), hU.preimage (continuous_wittExtendByZero o), fun u hu h0 => ?_⟩
    have hj := hl _ hu (matrixExtendByZero_map o _ u h0)
    funext v
    simp only [heisO]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    have e := congrFun hj ((o.resS T).symm (v, k w))
    simp only [heisO] at e
    rw [symm_add, ← matrixExtendByZero_apply]
    conv_rhs => rw [← e]
    rw [matrixExtendByZero_apply, sympl_ext_right]
    ring
  ·
    obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
    haveI : FirstCountableTopology (WO A T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
    refine continuous_of_dominated (bound := fun w => ‖a w‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · exact ha.aestronglyMeasurable.mul (hFm u).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun w => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun w => ?_
      exact continuous_const.mul (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := (ext0 o T).comp L
    have hL'c : Continuous L' := (continuous_wittExtendByZero o).comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => matrixExtendByZero_map o _ (L t) (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T A :=
      ((GlobalTheory.FockCompare.piW θ T A).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T A).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ T A (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO A T (GlobalTheory.FockCompare.piW θ T A w))
    have key : ∀ t, (∫ x, a x * F ((o.resS T).symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH A T w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH A T w (L t) = symplOH A T w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := A) (T := T) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, symm_add, ← matrixExtendByZero_apply]
      show _ = _ * (a x * (ψ (symplOH S T ((o.resS T).symm (w, k x)) ((o.resS T).symm (L t, 0))) * _))
      rw [sympl_ext_right]
      change a x * F (_ + ext0 o T (L t)) = ψ (-symplOH A T w (L t)) * (a x * (ψ (symplOH A T w (L t)) * F (_ + ext0 o T (L t))))
      have := psi_neg_mul ψ (symplOH A T w (L t))
      linear_combination (-(a x * F ((o.resS T).symm (w, k x) + (ext0 o T) (L t)))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F ((o.resS T).symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposS

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionSuperpositionOrthogonalSlicesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  first | exact @GlobalTheory.SuperposS.superpos_isTheta | exact GlobalTheory.SuperposS.superpos_isTheta | (intros; apply GlobalTheory.SuperposS.superpos_isTheta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSobolevSupBound
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology Pointwise

namespace GlobalTheory.SupremumSobolevWords

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.ThetaGrowth GlobalTheory.Size GlobalTheory.KernelSeminorm

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem lintegral_translate (hψ : IsStdChar D ψ (-1)) {φ : WO S T → ℂ} (hφ : IsThetaFunO ψ S T φ)
    {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hm : IsCovolOne (ratL T S) μ 𝓕) (y : WO S T) :
    ∫⁻ w in 𝓕, ‖φ (y + w)‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨-, hN⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  obtain ⟨N, hN⟩ := hN φ hφ.cont (theta_norm_periodic hψ hφ)
  have hμ := hm.1
  have hs : IsAddFundamentalDomain (ratL T S) ((fun w => -y + w) ⁻¹' 𝓕) μ :=
    hm.2.1.preimage_of_equiv (measurePreserving_add_left μ (-y)).quasiMeasurePreserving (e := id)
      Function.bijective_id fun γ x => by
        change -y + (γ + x) = γ + (-y + x)
        abel
  have e1 := (measurePreserving_add_left μ y).setLIntegral_comp_preimage_emb (measurableEmbedding_addLeft y)
    (fun w => ‖φ w‖ₑ ^ 2) ((fun w => -y + w) ⁻¹' 𝓕)
  have e2 : (fun a => y + a) ⁻¹' ((fun w => -y + w) ⁻¹' 𝓕) = 𝓕 := by
    ext a
    simp
  rw [e2] at e1
  rw [e1, (hN μ _ hμ hs).2.2.1, (hN μ 𝓕 hμ hm.2.1).2.2.1, measure_preimage_add]

theorem cube_dilate_bound_at (hψ : IsStdChar D ψ (-1)) (hc : Chart θ σ) {N : ℕ} (b : Module.Basis (Fin N) ℝ (RW T S))
    {K₀ : Set (WO S T)} (h0 : K₀ ∈ 𝓝 (0 : WO S T)) (hK₀ : IsCompact K₀) :
    ∃ c : ℝ≥0, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ n : ℕ, 0 < n →
      ∀ φ, IsThetaFunO ψ S T φ → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) φ = φ) → ∀ y : WO S T,
      ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) 1),
        ‖φ (y + ∑ i, iotaW σ T S (t i • n • b i))‖ ^ 2 ≤ c * (l2O μ 𝓕 φ).toReal ^ 2 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WA T S) := ⟨rfl⟩
  obtain ⟨⟨μ₀, 𝓕₀, hμ, h𝓕, h1⟩, -⟩ := GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WA T S) (ratL T S) K hK hcov
  have : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let ι : (Fin N → ℝ) →+ WA T S := (iotaW σ T S).comp b.equivFun.symm.toLinearMap.toAddMonoidHom
  let π : WA T S →+ (Fin N → ℝ) := b.equivFun.toLinearMap.toAddMonoidHom.comp (piW θ T S)
  have hι : Continuous ι := (hc.continuous_iota T S).comp b.equivFunL.symm.continuous
  have hπ : Continuous π := b.equivFunL.continuous.comp (continuous_pi' hc.inf T S)
  have hπι : ∀ t, π (ι t) = t := fun t => by
    show b.equivFun (piW θ T S (iotaW σ T S (b.equivFun.symm t))) = t
    rw [hc.pi_iota, LinearEquiv.apply_symm_apply]
  have hιπ : ∀ w, ι (π w) = iotaW σ T S (piW θ T S w) := fun w => by
    show iotaW σ T S (b.equivFun.symm (b.equivFun (piW θ T S w))) = _
    rw [LinearEquiv.symm_apply_apply]
  obtain ⟨c, K₁, hK₁, hreal⟩ := lintegral_real_le (G := WA T S) μ₀ ι π hι hπ hπι hK₀ h0
    (isCompact_univ_pi fun _ : Fin N => isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := lintegral_compact_le (G := WA T S) (ratL T S) μ₀ h𝓕 hK₁
  refine ⟨c * M, fun μ 𝓕 hm n hn φ hφ hl y => ?_⟩
  obtain ⟨e, he, heL⟩ := exists_dilation (S := S) (T := T) hn
  have hsum : ∀ t : Fin N → ℝ, y + ∑ i, iotaW σ T S (t i • n • b i) = y + e (ι t) := fun t => by
    rw [he]
    show _ = y + n • iotaW σ T S (b.equivFun.symm t)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Module.Basis.equivFun_symm_apply, ← map_nsmul, Finset.smul_sum, map_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm]
  have en : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hmeas : Measurable fun w : WA T S => ‖φ (y + e w)‖ₑ ^ 2 :=
    (hφ.cont.comp (continuous_const.add e.continuous)).measurable.enorm.pow_const 2
  have a1 := hreal _ hmeas fun w hw => by
    have hinf : (w - ι (π w)).map (infPart D) = 0 := by
      have hp : piW θ T S (w - ι (π w)) = 0 := by rw [hιπ, AddMonoidHom.map_sub, hc.pi_iota, sub_self]
      ext i j
      exact ThetaCont.infPart_eq_zero hc _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
    have := GlobalTheory.HeisOrtho.norm_heisO hψ.1 φ (n • (w - ι (π w))) (y + e (ι (π w)))
    rw [hl _ hw hinf, ← he, add_assoc, ← map_add (f := _), add_sub_cancel] at this
    rw [← en, ← en, this]
  have a2 := hM _ hmeas fun γ hγ w => by
    rw [← en, ← en, map_add (f := _), add_left_comm, theta_norm_periodic hψ hφ _ ((heL γ).2 hγ)]
  have a3 : ∫⁻ w in 𝓕₀, ‖φ (y + e w)‖ₑ ^ 2 ∂μ₀ = ∫⁻ w in 𝓕, ‖φ (y + w)‖ₑ ^ 2 ∂μ :=
    lintegral_comp_aut (G := WA T S) (ratL T S) hK hcov e heL hμ h𝓕 h1 hm.1 hm.2.1 hm.2.2
      (f := fun x => φ (y + x)) (hφ.cont.comp (continuous_const.add continuous_id)) fun γ hγ w => by
        change ‖φ (y + (γ + w))‖ = ‖φ (y + w)‖
        rw [add_left_comm]
        exact theta_norm_periodic hψ hφ γ hγ _
  have a3' := lintegral_translate hψ hφ hm y
  simp only [hsum]
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => ‖φ (y + e (ι t))‖ ^ 2)
    (Filter.Eventually.of_forall fun w => by positivity)
    ((hφ.cont.comp (continuous_const.add (e.continuous.comp hι))).norm.pow 2).aestronglyMeasurable]
  simp only [en]
  have he : l2O μ 𝓕 φ ^ 2 = ∫⁻ w in 𝓕, ‖φ w‖ₑ ^ 2 ∂μ := by
    have : BorelSpace (WO S T) := ⟨rfl⟩
    simpa [l2O] using eLpNorm_nnreal_pow_eq_lintegral (μ := μ.restrict 𝓕) (p := 2)
      two_ne_zero hφ.cont.measurable.aestronglyMeasurable
  have a4 := a1.trans (mul_le_mul_right (a2.trans_eq (congrArg _ ((a3.trans a3').trans he.symm))) _)
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M)
    (ENNReal.pow_ne_top (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hm.1 hm.2.1 hφ)))) a4).trans_eq ?_
  simp [mul_assoc]

end GlobalTheory.SupremumSobolevWords

namespace GlobalTheory.SupremumSobolevWords

open GlobalTheory.Size

end GlobalTheory.SupremumSobolevWords

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummand
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposT

theorem symplOH_zero_left {D : D7} {S T : HSp D} (y : WO S T) : symplOH S T 0 y = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem symplOH_zero_right {D : D7} {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem psi_neg_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

theorem symplOH_resT_symm {D : D7} {T A B : HSp D} (o : OrthDec T A B) (S : HSp D) (u u' : WO S A) (v v' : WO S B) :
    symplOH S T ((o.resT S).symm (u, v)) ((o.resT S).symm (u', v')) = symplOH S A u u' + symplOH S B v v' := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem superpos_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ S A fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ := by
  intro D ψ hψ T A B S o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (Mx D B.rank S.rank) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank S.rank
  haveI : FirstCountableTopology (WO S A) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  set e := o.resT S with he
  have hsplit : ∀ (u u' : WO S A) (v : WO S B), e.symm (u + u', v) = e.symm (u, v) + e.symm (u', 0) := by
    intro u u' v
    rw [← map_add (f := _), Prod.mk_add_mk, add_zero]
  have hmeas : ∀ (F' : WO S T → ℂ), Continuous F' → ∀ (c : WO S T) (u : WO S A),
      AEStronglyMeasurable (fun ξ => F' (e.symm (u, k ξ) + c)) μ := by
    intro F' hF' c u
    exact ((hF'.comp (((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).add
      continuous_const)).measurable.comp hk).aestronglyMeasurable

  let φ : WO S A →+ WO S T := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl (WO S A) (WO S B))
  have hφ : ∀ u, φ u = e.symm (u, 0) := fun u => rfl
  have hφc : Continuous φ := (o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)
  have hφmap : ∀ (R : Type) [CommRing R] (f : Formalism.L2.Theta.AE D →+* R) (u : WO S A), u.map f = 0 → (φ u).map f = 0 := by
    intro R _ f u hu
    rw [hφ, he, o.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.map_mul, hu, Matrix.mul_zero]
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    have hr : e.symm (ratW A S γ, 0) = ratW T S (o.iA * γ) := by
      rw [he, o.resT_symm_apply, Matrix.mul_zero, add_zero]
      exact (rat_mul _ _).symm
    have h1 : ∀ ξ, F (e.symm (ratW A S γ + u, k ξ)) =
        ψ (-(symplOH S A (ratW A S γ) u)) * F (e.symm (u, k ξ)) := by
      intro ξ
      rw [add_comm (ratW A S γ) u, hsplit, add_comm, hr, hF.quasi, ← hr, symplOH_resT_symm, symplOH_zero_left, add_zero]
    simp_rw [h1]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap φ, hU.preimage hφc, fun u hu h0 => ?_⟩
    have hl' := hl (φ u) hu (hφmap _ _ u h0)
    funext w
    simp only [heisO]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    have h2 := congrFun hl' (e.symm (w, k ξ))
    simp only [heisO] at h2
    rw [hφ, symplOH_resT_symm, symplOH_zero_right, add_zero, ← hsplit] at h2
    rw [mul_left_comm, h2]
  ·
    refine continuous_of_dominated (bound := fun ξ => ‖a ξ‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · have := hmeas F hF.cont 0 u
      simp only [add_zero] at this
      exact ha.aestronglyMeasurable.mul this
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · exact Filter.Eventually.of_forall fun ξ => continuous_const.mul
        (hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := φ.comp L
    have hL'c : Continuous L' := hφc.comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => hφmap _ _ _ (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW A S :=
      ((GlobalTheory.FockCompare.piW θ A S).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ A S).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ A S (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO S A (GlobalTheory.FockCompare.piW θ A S w))
    have key : ∀ t, (∫ x, a x * F (e.symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH S A w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH S A w (L t) = symplOH S A w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := A) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, hsplit]
      have hs : symplOH S T (e.symm (w, k x)) (L' t) = symplOH S A w (L t) := by
        show symplOH S T (e.symm (w, k x)) (e.symm (L t, 0)) = _
        rw [symplOH_resT_symm, symplOH_zero_right, add_zero]
      rw [hs]
      change a x * F (_ + L' t) = ψ (-symplOH S A w (L t)) * (a x * (ψ (symplOH S A w (L t)) * F (_ + L' t)))
      have := psi_neg_mul ψ (symplOH S A w (L t))
      linear_combination (-(a x * F (e.symm (w, k x) + L' t))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F (e.symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F (e.symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.SuperposSmooth.main D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resT_symm S).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummandStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFun_superposition_target_orthSummand : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ S A fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ := by
  first | exact @GlobalTheory.SuperposT.superpos_target | exact GlobalTheory.SuperposT.superpos_target | (intros; apply GlobalTheory.SuperposT.superpos_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDeterminantsWittLeviFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDeterminantsWittLeviFactor
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitLeviDet

theorem smul_iff {R : Type*} [CommRing R] {m n : Type*} (ε : R) (N : Matrix m n R) :
    ε • N = N ↔ ∀ i j, ε * N i j = N i j :=
  ⟨fun h i j => congrFun (congrFun h i) j, fun h => by ext i j; exact h i j⟩

theorem smul_sandwich {R : Type*} [CommRing R] {k l m n : Type*} [Fintype l] [Fintype m] (ε : R)
    (P : Matrix k l R) (N : Matrix l m R) (Q : Matrix m n R) (hN : ε • N = N) : ε • (P * N * Q) = P * N * Q := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hN]

theorem det_supp {R : Type*} [CommRing R] {n : ℕ} (ε : R) (hε : ε * ε = ε) (M : Matrix (Fin n) (Fin n) R)
    (hM : ε • (M - 1) = M - 1) : (1 - ε) * M.det = 1 - ε := by
  have hid : IsIdempotentElem (1 - ε) := by unfold IsIdempotentElem; linear_combination hε
  have hf : (1 - ε) • M = (1 - ε) • (1 : Matrix (Fin n) (Fin n) R) := by
    have h0 : (1 - ε) • (M - 1) = 0 := by rw [sub_smul, one_smul, hM, sub_self]
    rw [smul_sub, sub_eq_zero] at h0
    exact h0
  have key := congrArg Matrix.det hf
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at key
  cases n with
  | zero => rw [Matrix.det_isEmpty, mul_one]
  | succ k => rw [hid.pow_succ_eq] at key; exact key

variable {D : D7}

def locU (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (AE D)ˣ where
  val := e * t + (1 - e)
  inv := e * ↑t⁻¹ + (1 - e)
  val_inv := by
    have htu : (t : AE D) * ↑t⁻¹ = 1 := t.mul_inv
    linear_combination e * htu + ((t : AE D) * ↑t⁻¹ - t - ↑t⁻¹ + 1) * h
  inv_val := by
    have htu : (↑t⁻¹ : AE D) * t = 1 := t.inv_mul
    linear_combination e * htu + ((↑t⁻¹ : AE D) * t - ↑t⁻¹ - t + 1) * h

theorem locU_val (e : AE D) (h : e * e = e) (t : (AE D)ˣ) : (locU e h t : AE D) = e * t + (1 - e) := rfl

def detU (V : HSp D) (g : GA D V) : (AE D)ˣ where
  val := (mt V g).det
  inv := (mt V g⁻¹).det
  val_inv := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_mul_inv, Matrix.det_one]
  inv_val := by rw [← Matrix.det_mul, GlobalTheory.MixModel.mt_inv_mul, Matrix.det_one]

theorem detU_val (V : HSp D) (g : GA D V) : (detU V g : AE D) = (mt V g).det := rfl

theorem det_adj {n : ℕ} (y : Mx D n n) : (adj y).det = cA D y.det := by
  rw [adj, Matrix.det_transpose]; exact (RingHom.map_det (cA D) y).symm

theorem one_add_sub {n : ℕ} (M : Mx D n n) : 1 + (M - 1) = M := by abel

end GlobalTheory.SplitLeviDet

open GlobalTheory.SplitLeviDet

theorem GlobalTheory.SplitLeviDet.emb0Part : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add (f := _), hcc, add_comm]
  intro g hg
  have hN : (e + cA D e) • (mt S₀ g - 1) = mt S₀ g - 1 := (smul_iff _ _).2 hg
  have hm : mt S (d.emb0 g) = (1 : Mx D S.rank S.rank) + d.j0 ⬝ (mt S₀ g - 1) ⬝ d.p0 := by
    rw [d.unitaryMatrix_wittCoreEmbedding]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.emb0 g)).det = (mt S₀ g).det := by
    rw [hm, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one, one_add_sub]
  refine ⟨?_, locU e h1 (detU S₀ g), ?_, ?_⟩
  · intro i j
    rw [hm, add_sub_cancel_left]
    exact (smul_iff _ _).1 (smul_sandwich _ _ _ _ hN) i j
  · rw [IsDetAt, locU_val, detU_val]
  · rw [IsDetAt, locU_val, detU_val, hdet]

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.SplitLeviDet.leviPart : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := by
  intro D S S₀ ρ d e he
  obtain ⟨h1, h2, -⟩ := he
  have hce : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have hcc : cA D (cA D e) = e := Formalism.L2.Theta.cA_cA e
  have hεε : (e + cA D e) * (e + cA D e) = e + cA D e := by linear_combination h1 + 2 * h2 + hce
  have hcε : cA D (e + cA D e) = e + cA D e := by rw [map_add (f := _), hcc, add_comm]
  intro χ n hχ hR a ha
  have hA : (e + cA D e) • (a.1 - 1 : Mx D ρ ρ) = (a.1 - 1 : Mx D ρ ρ) := by
    ext i j
    exact ha i j
  have hI : (e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ) = ((a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have hinv : ((a⁻¹).1 - 1 : Mx D ρ ρ) = -((a⁻¹).1 ⬝ (a.1 - 1 : Mx D ρ ρ)) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Units.inv_mul, neg_sub]
    rw [hinv, smul_neg, ← Matrix.mul_smul, hA]
  have hB : (e + cA D e) • (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = (adj (a⁻¹).1 - 1 : Mx D ρ ρ) := by
    have h' : (adj (a⁻¹).1 - 1 : Mx D ρ ρ) = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [adj_sub, adj_one]
    rw [h']
    calc (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) = cA D (e + cA D e) • adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hcε]
      _ = adj ((e + cA D e) • ((a⁻¹).1 - 1 : Mx D ρ ρ)) := (adj_smul _ _).symm
      _ = adj ((a⁻¹).1 - 1 : Mx D ρ ρ) := by rw [hI]
  have hm : mt S (d.levi a) = (1 : Mx D S.rank S.rank) + (d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
    rw [d.mt_levi a]; conv_rhs => rw [← d.sum_eq_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]; abel
  have hdet : (mt S (d.levi a)).det = a.1.det * cA D (a⁻¹).1.det := by
    have h' : d.jX ⬝ (a.1 - 1 : Mx D ρ ρ) ⬝ d.pX + d.jY ⬝ (adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY =
        Matrix.fromCols d.jX d.jY ⬝ Matrix.fromRows ((a.1 - 1 : Mx D ρ ρ) ⬝ d.pX) ((adj (a⁻¹).1 - 1 : Mx D ρ ρ) ⬝ d.pY) := by
      rw [Matrix.fromCols_mul_fromRows, Matrix.mul_assoc, Matrix.mul_assoc]
    rw [hm, h', Matrix.det_one_add_mul_comm, Matrix.fromRows_mul_fromCols]
    simp only [Matrix.mul_assoc, d.pX_jX, d.pX_jY, d.pY_jX, d.pY_jY, Matrix.mul_one, Matrix.mul_zero]
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
    simp only [add_zero, one_add_sub]
    rw [Matrix.det_fromBlocks_zero₂₁, det_adj]
  have hs : (1 - (e + cA D e)) * a.1.det = 1 - (e + cA D e) := det_supp _ hεε _ hA
  set t := Matrix.GeneralLinearGroup.det a with ht
  have ht1 : (t : AE D) = a.1.det := rfl
  have ht2 : ((t⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by rw [ht, ← map_inv]; rfl
  refine ⟨?_, locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹), ?_, ?_⟩
  · have X : (e + cA D e) • (mt S (d.levi a) - 1) = mt S (d.levi a) - 1 := by
      rw [hm, add_sub_cancel_left, smul_add, smul_sandwich _ _ _ _ hA, smul_sandwich _ _ _ _ hB]
    intro i j
    exact congrFun (congrFun X i) j
  · rw [IsDetAt, locU_val, hdet, Units.val_mul, Units.coe_map, ht1, ht2]; rfl
  · set w := locU (cA D e) hce t with hw
    have hdc : cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hs' : (1 - (e + cA D e)) * (t : AE D) = 1 - (e + cA D e) := by rw [ht1]; exact hs
    have key : t = locU e h1 (t * Units.map (cA D).toMonoidHom t⁻¹) * (w * Units.map (cA D).toMonoidHom w) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, Units.coe_map, locU_val, Units.val_mul, Units.coe_map, hw, locU_val]
      simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_add (f := _), map_mul, map_sub, map_one, hcc]
      linear_combination (-((e * t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) + 1 - e) * (t * cA D (t : AE D) - t - cA D (t : AE D) + 1) +
          ((t : AE D) ^ 2 * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - t + 1))) * h2 -
        ((t : AE D) * cA D ((t⁻¹ : (AE D)ˣ) : AE D) * cA D (t : AE D) - t * cA D ((t⁻¹ : (AE D)ˣ) : AE D) - cA D (t : AE D) + 1) * h1 -
        e * t * hdc + hs'
    conv_rhs => rw [key]
    rw [map_mul, map_mul, GlobalTheory.ConjAdjWeil.chi_conj hR w, mul_inv_cancel, mul_one]

theorem GlobalTheory.splitLeviDet : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) ∧ ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := fun D S S₀ ρ d e he =>
  ⟨GlobalTheory.SplitLeviDet.emb0Part D S S₀ ρ d e he, GlobalTheory.SplitLeviDet.leviPart D S S₀ ρ d e he⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDeterminantsWittLeviFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_determinants_wittLeviFactor : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (e : AE D), IsSplitIdem D e → (∀ g, SuppAt e S₀ g → SuppAt e S (d.emb0 g) ∧ ∃ x, IsDetAt e S₀ g x ∧ IsDetAt e S (d.emb0 g) x) ∧ ∀ (χ : (AE D)ˣ →* Circle) (n : ℕ), IsHeckeChar D χ → ResEta D χ n → ∀ a : GL (Fin ρ) (AE D), (∀ i j, (e + cA D e) * (a.1 - 1) i j = (a.1 - 1) i j) → SuppAt e S (d.levi a) ∧ ∃ x, IsDetAt e S (d.levi a) x ∧ χ x = χ (Matrix.GeneralLinearGroup.det a) := by
  first | exact @GlobalTheory.splitLeviDet | exact GlobalTheory.splitLeviDet | (intros; apply GlobalTheory.splitLeviDet <;> assumption)
end
end
