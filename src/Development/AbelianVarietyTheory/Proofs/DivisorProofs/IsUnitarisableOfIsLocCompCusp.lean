module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeySectionUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsThresholdRunHolds
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ParametersOkOfLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoTangentPullConstantDeformation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSqIntegrableAndIsDiscreteSplitCentre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSqIntegrableAndIsDiscreteSplitCentre
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem cuspForm_isSqInt_and_isDiscrete :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
      (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧
        ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  intro E _ _ _ a
  have hB : CuspFormsBoundedGL :=
    GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay
      (GlobalTheory.cuspRapidDecaySiegelGL_of_finite GlobalTheory.automorphicFormsFiniteGL)
  have h1 : ∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1 :=
    fun φ hφ h' =>
      have hC := hB.of_invariant hφ h'
      GlobalTheory.DiscChar.isSqInt_of_bounded h' (C := hC.choose) hC.choose_spec
  exact ⟨h1, fun x hx => ⟨fun φ hφ => (x.cusp φ hφ).1, fun φ hφ => h1 φ (x.cusp φ hφ) (hx φ hφ), x.stable, x.ne_bot,
    x.irred⟩⟩

end GlobalTheory.ResW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormSqIntegrableAndIsDiscreteSplitCentreStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ φ : Sm E a, IsCuspForm φ → (∀ t g, φ.1 (splitCentre E a t * g) = φ.1 g) → IsSqInt φ.1) ∧ ∀ x : CuspSub E a, IsNormalised x → IsDiscrete x.V := by
  first | exact @GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete | exact GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete | (intros; apply GlobalTheory.ResW.cuspForm_isSqInt_and_isDiscrete <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem nu_zero_isUnitary (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : (nu E 0).IsUnitary := by
  intro x
  simp [nu, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem isUnitarisable_of_twRep {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {χ : G →* ℂˣ} (hχ : ∀ g, ‖((χ g : ℂˣ) : ℂ)‖ = 1) (h : GlobalTheory.SmGL.IsUnitarisable (twRep ρ χ)) :
    GlobalTheory.SmGL.IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  have e := h3 g v w
  simp only [twRep_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at e
  have hc : ((χ g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ g]; simp
  rw [← e]
  linear_combination (-(B (ρ g v) (ρ g w))) * hc

theorem isUnitarisable_of_isLocComp_cusp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (x : CuspSub E a), 1 ≤ a → x.IsUnitary → ∀ (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), x.IsLocComp w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ := by
  intro E _ _ _ a x ha hu w σ hσ
  have hcex := (GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x⟩).1
  have hr : rexp (⟨a, x⟩ : Letter E) = 0 := ((GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary E ⟨a, x⟩ ha).1).2 hu
  have hd : (0 : ℝ) < (a : ℝ) * Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hre : (cex (⟨a, x⟩ : Letter E)).re = 0 := by
    have h := hr
    unfold rexp at h
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h hd.ne'
  have hdc : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) = (((a : ℝ) * Module.finrank ℚ E : ℝ) : ℂ) := by push_cast; ring
  obtain ⟨χ, hz, -, hn, -⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ)))
  have hzre : (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))).re = 0 := by
    rw [hdc, Complex.div_ofReal_re, Complex.neg_re, hre]; simp
  have hχu : χ.IsUnitary := fun y => by rw [hn y, hzre]; exact nu_zero_isUnitary E y
  have hnorm : IsNormalised (x.twist χ) := by
    have h4 := GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x.twist χ⟩
    refine h4.2.2.2.1.1 (h4.2.2.2.2 0 ?_)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.ne_bot
    refine ⟨mulChi a χ φ, ⟨φ, hφ, rfl⟩, fun h => h0 ((mulChi a χ).map_eq_zero_iff.1 h), ?_⟩
    have e1 : zc E a φ = cex (⟨a, x⟩ : Letter E) • φ := hcex φ hφ
    have e2 : cex (⟨a, x⟩ : Letter E) + (a : ℂ) * (Module.finrank ℚ E : ℂ) *
        (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))) = 0 := by
      have : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 := by
        rw [hdc]; exact_mod_cast hd.ne'
      rw [mul_div_cancel₀ _ this]; ring
    change zc E a (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ
    rw [hz, e1, ← add_smul, e2, zero_smul, map_zero, zero_smul]
  have hdisc := (GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre E a).2 _ hnorm
  obtain ⟨f, h0, hf⟩ := hσ.twist χ
  have hgl : IsLocCompGL (x.twist χ).V w (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) :=
    ⟨(x.twist χ).V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩
  have hU := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a _ hdisc w _ hgl
  exact isUnitarisable_of_twRep (χ := CuspSub.locDet a χ w) (fun g => hχu _) hU

end GlobalTheory.ResW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalIn
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DiagUniq

open MeasureTheory GlobalTheory.DiagForm

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply v.1)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1)

theorem glue_shiftOf (x : κ → AF F) : glue (shiftOf x) = x := by
  have h := glue_add_shiftOf (0 : Vi F κ × Vf F κ) x
  rwa [zero_add, GlobalTheory.DiagNonvan.glue_zero, zero_add] at h

theorem shiftOf_glue (p : Vi F κ × Vf F κ) : shiftOf (glue p) = p := by
  refine Prod.ext ?_ rfl
  refine (eI F κ).injective ?_
  show eI F κ ((eI F κ).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext i
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem continuous_shiftOf : Continuous (shiftOf : (κ → AF F) → Vi F κ × Vf F κ) :=
  ((eI F κ).symm.continuous.comp (continuous_pi fun i =>
    continuous_toMixed.comp (continuous_fst.comp (continuous_apply i)))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))


variable (F κ) in
def glueE : (Vi F κ × Vf F κ) ≃ₜ+ (κ → AF F) where
  toFun := glue
  invFun := shiftOf
  left_inv := shiftOf_glue
  right_inv := glue_shiftOf
  map_add' := GlobalTheory.DiagNonvan.glue_add
  continuous_toFun := GlobalTheory.DiagNonvan.continuous_glue
  continuous_invFun := continuous_shiftOf

theorem lDiag_eq (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), lDiag F κ Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : ((mu F κ).map (glueE F κ)).IsAddHaarMeasure := (glueE F κ).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ((mu F κ).map (glueE F κ)) μ
  refine ⟨((Measure.addHaarScalarFactor ((mu F κ).map (glueE F κ)) μ : ℝ) : ℂ), fun Φ hΦ => ?_⟩
  have e := (glueE F κ).toHomeomorph.measurableEmbedding.integral_map (μ := mu F κ) (fun u => Φ (Sum.elim u u))
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD hΦ)]
  refine e.symm.trans ?_
  change ∫ u, Φ (Sum.elim u u) ∂((mu F κ).map (glueE F κ)) = _
  conv_lhs => rw [h]
  rw [integral_smul_nnreal_measure]
  rfl


variable (F κ) in
def diagL : ((κ → F) × (κ → F)) →ₗ[F] ((κ ⊕ κ → F) × (κ ⊕ κ → F)) where
  toFun p := (Sum.elim p.1 p.1, Sum.elim p.2 (-p.2))
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [add_comm]
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

omit [NumberField F] [Fintype κ] in
theorem diagL_injective : Function.Injective (diagL F κ) := by
  intro p q h
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact congrFun (congrArg Prod.fst h) (Sum.inl i)
  · exact congrFun (congrArg Prod.snd h) (Sum.inl i)

theorem eq_mul_diagInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  intro F _ _ ψ hψ κ _ l hl hinv μ hμ
  have key : ∀ l' : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l' (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l' Φ) →
      ∀ (t : AF F), ∀ w ∈ LinearMap.range (diagL F κ), ∀ φ ∈ schA F (κ ⊕ κ),
        l' (schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ := by
    rintro l' h t _ ⟨p, rfl⟩ φ hφ
    have e : t • ((fun i => algebraMap F (AF F) ((diagL F κ p).1 i)), (fun i => algebraMap F (AF F) ((diagL F κ p).2 i))) =
        (Sum.elim (fun i => t * algebraMap F (AF F) (p.1 i)) (fun i => t * algebraMap F (AF F) (p.1 i)),
          Sum.elim (fun i => t * algebraMap F (AF F) (p.2 i)) (-fun i => t * algebraMap F (AF F) (p.2 i))) := by
      refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp [diagL]
    rw [e]
    exact h _ _ φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F ψ hψ (κ ⊕ κ) (LinearMap.range (diagL F κ))
    (by
      rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
      simp [diagL, dotProduct, Fintype.sum_sum_type])
    (by
      rw [LinearMap.finrank_range_of_inj diagL_injective]
      simp)
    l hl (lDiag F κ) lDiag_adm (key l hinv) (key _ fun x y Φ hΦ => lDiag_schr ψ x y hΦ) exists_lDiag_ne
  obtain ⟨d, hd⟩ := lDiag_eq μ hμ
  exact ⟨c * d, fun Φ hΦ => by rw [hc Φ hΦ, hd Φ hΦ, mul_assoc]⟩

end GlobalTheory.DiagUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergInvariantAdmissibleFormEqMulDiagonalInStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergInvariant_admissibleForm_eq_mul_diagonalIntegral : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ), l ∈ (adeleClass F).adm (κ ⊕ κ) →
      (∀ x y : κ → AF F, ∀ Φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) Φ) = l Φ) →
      ∀ μ : @MeasureTheory.Measure (κ → AF F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∃ c : ℂ, ∀ Φ ∈ schA F (κ ⊕ κ), l Φ = c * GlobalTheory.DiagSiegel.diagInt μ Φ := by
  first | exact @GlobalTheory.DiagUniq.eq_mul_diagInt | exact GlobalTheory.DiagUniq.eq_mul_diagInt | (intros; apply GlobalTheory.DiagUniq.eq_mul_diagInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKeySecOfFamily
noncomputable section

section Family

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT
open GlobalTheory.FrameUnif GlobalTheory.Reg GlobalTheory.KeyFourth
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyCover


set_option maxHeartbeats 1000000 in
attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem nonempty_keySec_of_family (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (σ : c.F →+* ℂ) (hσ : Formalism.L2.PjFree.GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom)
      (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (hpq : 1 ≤ Dw.p + Dw.q) (hF : FnAlgClosed (Xo := Xo) (c := c)) : Nonempty (KeySec Xo c) := by
  have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have hT : Out.SecTwistSt := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨ξ₀, hcc, hne, him⟩ := GlobalTheory.IsUnfEx.exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨M, hM, hξ, hMG⟩ := GlobalTheory.ModelsExist.exists_modelsOf GlobalTheory.QNorm.hasseNormSt E H Dw l Xo _ _ _ F _ ξ₀ Gm φ
    hcc him hφ
  have T : ∀ k, ThetaData e F M k := fun k => (GlobalTheory.T.nonempty_thetaData_flagDomainModels E H Dw l Xo c σ g e F _ M hσ hM hξ k).some
  choose un hun using fun k => GlobalTheory.T.exists_normalisedFramedPoint_on_each_component hT E H Dw l Xo c σ g e F _ M k (T k)
  have hok : FramesOK e F M un :=
    ⟨fun k => GlobalTheory.T.normalised_points_satisfy_single_frame hT E H Dw l Xo c σ g e F _ M k (T k) (un k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_triangularFrame_weightRule hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun k => GlobalTheory.T.normalisedFramedPoint_arithmeticGroup_invariant_sign hT E H Dw l Xo c σ g e F _ M un k (T k) hσ hM hξ (hun k),
      fun a n han f hf k => GlobalTheory.T.differentiableOn_readings_normalised_theta_points hB hT E H Dw l Xo c σ g e F _ M un k (T k) (hun k) a n han f hf⟩
  have hU₀ := isUnf_built hB E H Dw l Xo c σ g e F _ M un hσ hM hξ hok
  have hC : (normConst (fun j => Formalism.L2.PjFree.relab c σ (e j).1) ξ₀ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    refine (Real.sqrt_pos.2 (div_pos (by positivity) (Finset.prod_pos fun j _ => ?_))).ne'
    have : Formalism.L2.PjFree.relab c σ (e j).1 ξ₀ ≠ 0 := (map_ne_zero _).2 hne
    positivity
  obtain ⟨κ, k₁, k₂, -, k₃, -, k₄, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have hchart : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
      ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧
        GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
        ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
    have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
      charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
    choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
    refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
    haveI := C.sm
    haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
    haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
    haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
    obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
    obtain ⟨u, hu⟩ := k₄ C.R Φ.key
    refine ⟨Φ, u, hΦ, hu, ?_⟩
    rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ k₁ k₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
    exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
  obtain ⟨v, hv⟩ := hchart
  have hroot : ∀ C : FChart h, ∃ (a : c.F) (b : C.R), a ≠ 0 ∧
      ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) = a • (b : Om C.Z) ^ 4 := by
    intro C
    obtain ⟨Φ, u, hΦ, hu, huv⟩ := hv C
    letI : Algebra c.F ℂ := σ.toAlgebra
    haveI := C.sm
    haveI := GlobalTheory.GeomConn.isDomain_tensor C.R.val Subtype.val_injective (hF C.Z) ℂ
    choose z hz using fun ψ : C.R →ₐ[c.F] CAt σ => hL.bc _ _ ψ C.y
    have hex : ∀ ψ, ∃ w, RootVal (unfOf e F M un) (z ψ) w := fun ψ => by
      obtain ⟨k, x, t, ht⟩ := hU₀.2.2.1 (z ψ)
      exact ⟨_, k, x, t, ht, rfl⟩
    choose ρ hρ using hex
    obtain ⟨a, b, ha, hab⟩ := exists_eq_smul_pow (K := c.F) (A := C.R) (n := 4) (by norm_num) u
      (pow_ne_zero 4 (div_ne_zero hC (pow_ne_zero g Complex.two_pi_I_ne_zero))) ρ
      (fun m V s hV hs => GlobalTheory.T.continuousOn_keySection_complexValue E H Dw l Xo c σ g e F _ M T un hσ hM hξ hun hok C.R C.y m V s
        (fun p => z (s p)) (fun p => ρ (s p)) hV hs (fun p _ => hz _) fun p _ => hρ _)
      (fun ψ => by
        obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : FibKey Xo ℂ (z ψ).x, Tied (S := ℂ) e (z ψ).s (z ψ).u Ψ :=
          @GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (z ψ) hpq
        exact (rule_eq_of_rootVal k₁ k₂ k₃ T hun hpq hC (fun k => by rw [(hMG k).2]) (hρ ψ) Ψ hΨ).trans
          (congrArg _ (hu ℂ _ _
            (@GlobalTheory.T.universal_triple_fibres_base_change_key_data E _ _ _ H Dw l Xo c g e _ ℂ _ _ _ _ σ.toAlgebra ψ C.y (z ψ) Φ Ψ (hz ψ) hΦ hΨ))))
    exact ⟨a, b, ha, by rw [← huv, hab]; rfl⟩
  have hgen : ∀ Z : Comp Xo c, ∃ (a : c.F) (b : Om Z), a ≠ 0 ∧ (v Z : Om Z) = a • b ^ 4 := by
    intro Z
    obtain ⟨C, ψ, z, t, h1, h2⟩ := hA h (Om Z) (genFr h Z)
    obtain rfl := GlobalTheory.Reg.SecGlue.chart_comp Z C ψ z t h1 h2
    obtain ⟨a, b, ha, hab⟩ := hroot C
    refine ⟨a, b / ((kch C.t : (Om C.Z)ˣ) : Om C.Z), ha, ?_⟩
    rw [div_pow, ← smul_div_assoc, ← hab, Units.val_mul, Units.val_pow_eq_pow_val,
      mul_div_cancel_left₀ _ (pow_ne_zero 4 (kch C.t).ne_zero)]
  choose a b ha hab using hgen
  have hb0 : ∀ Z, b Z ≠ 0 := fun Z h0 => (v Z).ne_zero (by rw [hab, h0]; simp)
  refine keySec_of_generic h b hb0 fun C => ?_
  obtain ⟨-, u, -, -, huv⟩ := hv C
  haveI := C.sm
  haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
  haveI := GlobalTheory.SupGeneric.isFractionRing_chart C
  have hint : ∀ (x : Om C.Z) (y : C.R), x ^ 4 = y → x ∈ C.R := fun x y hxy => by
    have hi : IsIntegral C.R (x ^ 4) := hxy ▸ isIntegral_algebraMap (R := C.R) (x := y)
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (by norm_num : 0 < 4) hi
    exact hw ▸ w.2
  have hc : ∀ (x : c.F) (y : C.R), ((algebraMap c.F C.R x * y : C.R) : Om C.Z) = x • (y : Om C.Z) := fun x y => by
    rw [Algebra.smul_def]
    rfl
  have e₁ : (((kch C.t : (Om C.Z)ˣ) : Om C.Z) * b C.Z) ^ 4 = (a C.Z)⁻¹ • ((u : C.R) : Om C.Z) := by
    rw [huv, Units.val_mul, Units.val_pow_eq_pow_val, hab, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ (ha _), one_smul, mul_pow]
  refine ⟨hint _ _ (e₁.trans (hc _ _).symm),
    hint _ (algebraMap c.F C.R (a C.Z) * ((u⁻¹ : (C.R)ˣ) : C.R)) ?_⟩
  rw [inv_pow, e₁, hc]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀ (ha _), one_smul, ← Subalgebra.coe_mul, Units.mul_inv]
  rfl

end GlobalTheory.KeyCover

end Family

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.KeyCover

end GlobalTheory.KeyCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorCast
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.WtShape

theorem toNat_floor_cast {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem eQ_succ (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) : DV.eQ D ((i : ℕ) + 1) t = (D.hc t).e i := by
  unfold DV.eQ
  rw [dite_eq_left ⟨Nat.le_add_left _ _, i.2⟩]
  rfl

theorem lamAt_eq (D : D7) (t : D.what₂.Tau) (n : ℕ) : Formalism.L2.NTheta.lamAt (D.hc t) n = DV.sigPar D t n := rfl

theorem aPl_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) (hn : n < D.R.k + i) :
    (aPl D i (D.R.k + i) t n : ℚ) =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k : ℚ) + i) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have e : DV.aPlusQ D ((i : ℕ) + 1) t n =
      DV.sigPar D t n + (D.hc t).e i - (((D.R.k + i : ℕ) : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    rw [DV.aPlusQ_eq, eQ_succ]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aPlusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 t ⟨n, hn⟩
  have h2 := DV.aPlusQ_int D ((i : ℕ) + 1) t n
  unfold aPl
  rw [if_pos hn, lamAt_eq, ← e, toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem aMi_cast (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (c : ℕ) (hc : (i : ℕ) + 1 + c < D.R.m) :
    (aMi D i (D.R.k + i) (D.R.m - ((i : ℕ) + 1)) t (D.R.m - ((i : ℕ) + 1) - 1 - c) : ℚ) =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + (c + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have e0 : D.R.m - ((i : ℕ) + 1) - (D.R.m - ((i : ℕ) + 1) - 1 - c) = c + 1 := by omega
  have e1 : DV.sigPar D t (D.R.k + i + c) = -(D.hc t).b ⟨(i : ℕ) + 1 + c, hc⟩ := by
    unfold DV.sigPar
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 3
    omega
  have e : DV.aMinusQ D ((i : ℕ) + 1) t c =
      -((D.hc t).e i + DV.sigPar D t (D.R.k + i + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2) := by
    unfold DV.aMinusQ
    rw [dite_eq_left hc, eQ_succ, e1]; push_cast; ring
  have h1 := GlobalTheory.BlockRows.one_le_aMinusQ D ((i : ℕ) + 1) (Nat.le_add_left _ _) t c hc
  have h2 := DV.aMinusQ_int D ((i : ℕ) + 1) t c
  unfold aMi
  rw [if_pos (by omega), e0, lamAt_eq, show D.R.k + i + (c + 1) - 1 = D.R.k + i + c by omega, ← e,
    toNat_floor_cast h2 h1, e]
  push_cast; ring

theorem nV_half (R : Ranks) : ((R.nV / 2 : ℕ) : ℚ) = ((R.r : ℚ) + R.t) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hm := R.two_le_m
  have h1 : R.r + R.t = 2 * (R.nV / 2) := by unfold Ranks.nV Ranks.r; omega
  have h2 : (R.r : ℚ) + R.t = 2 * ((R.nV / 2 : ℕ) : ℚ) := by exact_mod_cast h1
  linarith

def ent (D : D7) (i : Fin D.R.m) (t : D.what₂.Tau) (n : ℕ) : ℚ :=
  DV.sigPar D t n + (D.hc t).e i + n - ((D.R.k : ℚ) + i) + ((D.R.r : ℚ) + 1) / 2 - if n < D.R.k + i then 0 else (D.R.r : ℚ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem inR : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

theorem dat_p : (dat p i).p = D.R.k + i := (p.fw.laws.pins.2.2.2 _ (inR i)).1

theorem dat_q : (dat p i).q = D.R.m - ((i : ℕ) + 1) := (p.fw.laws.pins.2.2.2 _ (inR i)).2.1

theorem dat_rank : (dat p i).p + (dat p i).q = D.R.r := by
  have := i.2
  rw [dat_p, dat_q]; unfold Ranks.r; omega

theorem exists_tau (τ : Psi p.T.Q.H) : ∃ t, τ.1 = DV.tauEmb D t :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi p.T.Q p.fw.laws.pins.1 τ.1 τ.2

theorem card_psi : Nat.card (Psi p.T.Q.H) = D.R.f := by
  have hp := p.fw.laws.pins.1
  have hb : Function.Bijective (fun t : D.what₂.Tau => (⟨DV.tauEmb D t, hp.2.2.2 t⟩ : Psi p.T.Q.H)) :=
    ⟨fun s t e => GlobalTheory.WeightExponents.tauEmb_injective D (congrArg Subtype.val e), fun τ => by
      obtain ⟨t, ht⟩ := exists_tau p τ
      exact ⟨t, Subtype.ext ht.symm⟩⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, D.what₂.card_Tau]

theorem dim_eq : dimFlag (dat p i) = D.R.f * D.R.r.choose 2 := by
  unfold dimFlag Formalism.DegreeFormula.dimFl
  rw [dat_rank, ← Nat.card_eq_fintype_card, card_psi, Nat.choose_two_right]

theorem cols_eq : (p.κ i).n = D.R.nV := by
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega)
  obtain ⟨t⟩ := hne
  exact (p.fw.kap i t).2.2

theorem unit_eq : unitE p = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := rfl

theorem laOf_read (τ : Psi p.T.Q.H) (t : D.what₂.Tau) (ht : τ.1 = DV.tauEmb D t) (n : Fin ((dat p i).p + (dat p i).q)) :
    (laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ n : ℚ) = ent D i t n := by
  have hp := p.fw.laws.pins.1
  have hs : (Wc D i).sig (TH.tauE D t) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨k1, k2, -⟩ := p.fw.kap i t
  rw [hs] at k1 k2
  have s1 : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := rfl
  have s2 : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - ((i : ℕ) + 1) := rfl
  have hn := n.2
  have e1 := dat_p p i
  have e2 := dat_q p i
  have hh := nV_half D.R
  unfold laOf weightOf ent
  rw [cols_eq, ht]
  beta_reduce
  by_cases h : (n : ℕ) < D.R.k + i
  · rw [if_pos (by omega), if_pos h, GlobalTheory.WeightExponents.wtA_tauEmb hp, ext0, dite_eq_left (show (n : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1 from h), k1]
    have := aPl_cast D i t n h
    simp only [Int.cast_add, Int.cast_natCast, s1]
    rw [this, hh]; ring
  · obtain ⟨c, hc⟩ : ∃ c, (n : ℕ) = D.R.k + i + c := ⟨n - (D.R.k + i), by omega⟩
    have e3 : (dat p i).q - 1 - ((n : ℕ) - (dat p i).p) = D.R.m - ((i : ℕ) + 1) - 1 - c := by omega
    rw [if_neg (by omega), if_neg h, e3, conjEmb, GlobalTheory.WeightExponents.conjEmb_eq, GlobalTheory.WeightExponents.wtA_conj hp, ext0,
      dite_eq_left (show D.R.m - ((i : ℕ) + 1) - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 by omega), k2]
    have := aMi_cast D i t c (by omega)
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, s1, s2]
    rw [this, hh, hc]; push_cast; ring

end GlobalTheory.CovTop.WtShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunWeightArch
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundJoin
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunJoin

theorem genOK_refill {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPJ h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (c : ℝ) (hG : GenOK h j hj large₂ G S c)
    (del th' rz alz th0 zc rq th iet et) :
    GenOK h j hj large₂ (FamilyHypotheses.refill G del th' rz alz th0 zc rq th iet et) S c := hG

end GlobalTheory.RunJoin
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open GlobalTheory.RunJoin

namespace GlobalTheory.ShareOn

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem archOne_congr {X X' : Data E r} (hX : X = X') {L Fp : Wt X.Ψ r} {L' Fp' : Wt X'.Ψ r} {T : ℕ}
    (hL : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, L ⟨τ, h1⟩ a = L' ⟨τ, h2⟩ a)
    (hF : ∀ τ (h1 : τ ∈ X.Ψ) (h2 : τ ∈ X'.Ψ) a, Fp ⟨τ, h1⟩ a = Fp' ⟨τ, h2⟩ a) (h : ArchOne X' L' Fp' T) :
    ArchOne X L Fp T := by
  subst hX
  have e1 : L = L' := funext fun τ => funext fun a => hL τ.1 τ.2 τ.2 a
  have e2 : Fp = Fp' := funext fun τ => funext fun a => hF τ.1 τ.2 τ.2 a
  subst e1 e2
  exact h

theorem archOn_of_comps {U C K : Type} [Group U] [MulAction U C] [Nonempty C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r)
    (X : K → Data E r) (e : C ≃ K) (hX : ∀ c, (M.comp c).toData = X (e c)) (lK lL lF : ∀ k, Wt (X k).Ψ r) (T n : ℕ)
    (hn : n = M.dimY)
    (hka : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = lK (e c) ⟨τ, h2⟩ a)
    (hsum : ∀ k, lK k = lF k + T • lL k)
    (hLi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lL k ⟨τ, h⟩ a = lL k' ⟨τ, h'⟩ a)
    (hFi : ∀ k k' τ (h : τ ∈ (X k).Ψ) (h' : τ ∈ (X k').Ψ) a, lF k ⟨τ, h⟩ a = lF k' ⟨τ, h'⟩ a)
    (hW : ∀ k, GapsGe (X k).p0 (lL k) 1 ∧ PairGe (lL k) (1.9 * T) ∧
      GapsGe (X k).p0 (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 0 ∧ PairGe (lF k - kLog (X k).Ψ r - (n + 2) • lL k) 1)
    (hA : ∀ k, ArchOne (X k) (lL k) (lF k) T) : ArchOn M ka T := by
  obtain ⟨c0⟩ := ‹Nonempty C›
  have hΨ : ∀ c, (X (e c)).Ψ = M.Ψ := fun c => (congrArg Data.Ψ (hX c)).symm.trans (M.comp_Ψ c)
  have hp : ∀ c, (X (e c)).p0 = M.p0 := fun c => (congrArg Data.p0 (hX c)).symm.trans (M.comp_basePoint c)
  have mem : ∀ c τ, τ ∈ M.Ψ → τ ∈ (X (e c)).Ψ := fun c τ h => (hΨ c).symm ▸ h
  let L : Wt M.Ψ r := fun τ a => lL (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  let Fp : Wt M.Ψ r := fun τ a => lF (e c0) ⟨τ.1, mem c0 τ.1 τ.2⟩ a
  have hW0 := hW (e c0)
  rw [hp c0, hn] at hW0
  obtain ⟨w1, w2, w3, w4⟩ := hW0
  refine ⟨L, Fp, ?_, fun τ a b h1 h2 => w1 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w2 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun τ a b h1 h2 => w3 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2,
    fun τ a b h1 h2 => w4 ⟨τ.1, mem c0 τ.1 τ.2⟩ a b h1 h2, fun c => ?_⟩
  · funext τ a
    rw [hka c0 τ.1 τ.2 (mem c0 τ.1 τ.2) a, hsum]
    rfl
  · refine archOne_congr (hX c) (fun τ h1 h2 a => ?_) (fun τ h1 h2 a => ?_) (hA (e c))
    · exact hLi (e c0) (e c) τ _ h2 a
    · exact hFi (e c0) (e c) τ _ h2 a

end Model

section Run

theorem row_pair {r p q : ℕ} (hpq : p + q = r) (Dm nL nF : ℤ) (hnF : 0 ≤ nF)
    (LP LM FP FM : ℕ → ℤ) (L F : Fin r → ℤ)
    (hL : ∀ a : Fin r, L a = if q ≤ (a : ℕ) then LP (a - q) + nL else -LM (q - 1 - a) - nL)
    (hF : ∀ a : Fin r, F a = if q ≤ (a : ℕ) then FP (a - q) + nF else -FM (q - 1 - a) - nF)
    (p4 : (Dm + 2) * LP (p - 1) + ((Dm + 2) * (2 * nL) + 2 * r) ≤ FP (p - 1))
    (m4 : (Dm + 2) * LM (q - 1) + 0 ≤ FM (q - 1)) (a b : Fin r) (ha : (a : ℕ) = 0) (hb : (b : ℕ) = r - 1)
    (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (F b - (2 * (b : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L b) -
      (F a - (2 * (a : ℤ) - ((r : ℤ) - 1)) - (Dm + 2) * L a) := by
  have hq1 : q ≤ (b : ℕ) := by omega
  have hq2 : ¬ q ≤ (a : ℕ) := by omega
  have e1 : (a : ℤ) = 0 := by omega
  have e2 : (b : ℤ) = r - 1 := by omega
  have e3 : (r : ℤ) = p + q := by omega
  rw [hL a, hL b, hF a, hF b, e1, e2]
  simp only [if_pos hq1, if_neg hq2]
  rw [show (b : ℕ) - q = p - 1 by omega, show q - 1 - (a : ℕ) = q - 1 by omega]
  nlinarith

theorem expand_weight {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)} (F L : Wt Ψ r)
    (n : ℕ) (τ : Ψ) (c : Fin r) :
    (F - kLog Ψ r - (n + 2) • L) τ c = F τ c - (2 * (c : ℤ) - ((r : ℤ) - 1)) - ((n : ℤ) + 2) * L τ c := by
  show F τ c - kLog Ψ r τ c - ((n + 2) • L τ c) = _
  rw [nsmul_eq_mul]
  simp only [kLog]
  push_cast
  ring


set_option maxHeartbeats 1000000 in
theorem run_weight_arch (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp)
    (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (hP : FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0) (hjm : j < D.R.m)
    (k : (T.U j T.σ₀).Comp) :
    GapsGe ((T.U j T.σ₀).X k).p0 (laR T j wL k) 1 ∧ PairGe (laR T j wL k) (1.9 * Tn) ∧
      GapsGe ((T.U j T.σ₀).X k).p0
        (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 0 ∧
      PairGe (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) 1 := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, g1, g2, h4, -, h6, h7, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, h21, -⟩ := hS
  obtain ⟨-, -, -, -, -, hp0, -, tt, hla⟩ := GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k
  have hk := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hp : 0 < (D.R.sigW j).1 := by show 0 < D.R.k + j - 1; omega
  have hq : 0 < (D.R.sigW j).2 := by show 0 < D.R.m - j; omega
  have hpq : (D.R.sigW j).1 + (D.R.sigW j).2 = D.R.r := by
    show D.R.k + j - 1 + (D.R.m - j) = D.R.k + D.R.m - 1; omega
  have hTp : ((Tp D j Tn : ℕ) : ℤ) = (Tn : ℤ) + (WeightFamilies.dimY D j : ℤ) + 2 := by unfold Tp; push_cast; ring
  have h40' : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ Tn := by exact_mod_cast h40
  have h21' : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ Tn := by exact_mod_cast h21
  have hn : (nW : ℤ) = 2 * ((wL.n / 2 : ℕ) : ℤ) := by
    have := hL.1
    obtain ⟨c, hc⟩ := wL.n_even
    omega
  have key := fun τ : ((T.U j T.σ₀).X k).Ψ => by
    have bP := GlobalTheory.RunWeightDom.block hp (ka.aP (tt τ)) (wL.aP (tt τ)) (wF.aP (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r) (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' h21'
      (fun i hi => by have := g1 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP (tt τ) i : ℝ) := by have := h6 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.1 (tt τ) i; rwa [hTp, sub_sub] at this) (hF.2.1 (tt τ))
    have bM := GlobalTheory.RunWeightDom.block hq (ka.aM (tt τ)) (wL.aM (tt τ)) (wF.aM (tt τ)) Tn (WeightFamilies.dimY D j) D.R.r
      0 (Int.natCast_nonneg _) (Int.natCast_nonneg _) h40' (Int.natCast_nonneg _)
      (fun i hi => by have := g2 (tt τ) i hi; push_cast at this; rwa [hTp] at this)
      (fun i hi => by
        have h1 : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aM (tt τ) i : ℝ) := by have := h7 (tt τ) i hi; linarith
        exact_mod_cast h1)
      (fun i => by have := hL.2.2 (tt τ) i; rwa [hTp, ← sub_zero (ka.aM (tt τ) i : ℤ)] at this) (hF.2.2 (tt τ))
    rw [hn] at bP
    exact And.intro (GlobalTheory.RunWeightDom.row hpq Tn (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ)
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) _ _ _ _ (laR T j wL k τ) (laR T j wF k τ) (Int.natCast_nonneg _)
      (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.1 bP.2.1 bP.2.2.1 bP.2.2.2
      bM.1 bM.2.1 bM.2.2.1 bM.2.2.2)
      (row_pair hpq (WeightFamilies.dimY D j) ((wL.n / 2 : ℕ) : ℤ) ((wF.n / 2 : ℕ) : ℤ) (Int.natCast_nonneg _)
        (fun i => (ext0 (wL.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wL.aM (tt τ)) i : ℤ))
        (fun i => (ext0 (wF.aP (tt τ)) i : ℤ)) (fun i => (ext0 (wF.aM (tt τ)) i : ℤ))
        (laR T j wL k τ) (laR T j wF k τ) (fun a => by rw [hla, hp0]) (fun a => by rw [hla, hp0]) bP.2.2.2 bM.2.2.2)
  rw [← hp0] at key hq
  have hq' : ((T.U j T.σ₀).X k).p0 < D.R.r := by omega
  have e : ∀ (τ : ((T.U j T.σ₀).X k).Ψ) (c : Fin D.R.r),
      (laR T j wF k - kLog ((T.U j T.σ₀).X k).Ψ D.R.r - (WeightFamilies.dimY D j + 2) • laR T j wL k) τ c =
        laR T j wF k τ c - (2 * (c : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ c := by
    intro τ c
    exact expand_weight _ _ _ τ c
  refine ⟨fun τ a b hab hb => ?_, fun τ a b ha hb => ?_, fun τ a b hab hb => ?_, fun τ a b ha hb => ?_⟩
  · obtain ⟨⟨k1, k2, -, -, -⟩, -⟩ := key τ
    have hab' : (a : ℕ) < b := by omega
    by_cases hc : (b : ℕ) < ((T.U j T.σ₀).X k).p0
    · have := k1 a b hab' hc; omega
    · have := k2 a b (by omega) hab'; omega
  · obtain ⟨⟨-, -, -, k4, -⟩, -⟩ := key τ
    have := k4 a b (by omega) (by omega)
    have h' : (19 : ℝ) * Tn ≤ 10 * ((laR T j wL k τ b - laR T j wL k τ a : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · obtain ⟨⟨-, -, k3, -, -⟩, -⟩ := key τ
    have := k3 a b hab hb
    rw [e τ a, e τ b]
    linarith
  · obtain ⟨-, k5⟩ := key τ
    have := k5 a b ha hb hp hq
    rw [e τ a, e τ b]
    have h1 : (1 : ℤ) ≤ (laR T j wF k τ b - (2 * (b : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ b) -
      (laR T j wF k τ a - (2 * (a : ℤ) - ((D.R.r : ℤ) - 1)) - ((WeightFamilies.dimY D j : ℤ) + 2) * laR T j wL k τ a) := this
    exact_mod_cast h1

theorem archOne_of_run (D : D7) (T : Top D) (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (p j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ)
    (hpar : ParOK T EX p j) (hpg : PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0)
    (hC : HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0 nus)
    (hjm : j < D.R.m) :
    ∀ k : (T.U j T.σ₀).Comp, ArchOne ((T.U j T.σ₀).X k) (GlobalTheory.Shares.laR T j wL k) (GlobalTheory.Shares.laR T j wF k) Tn := by
  obtain ⟨G, hG⟩ := GlobalTheory.RunJoin.exists_genOK D T h hinj EX p j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpar.orient hpg
  obtain ⟨i, et, he⟩ := GlobalTheory.EtaBoundForm.exists_etaOK D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hpg hjm
  let G' := FamilyHypotheses.refill G G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  have hG' : GenOK h j hj large₂ G' _ _ := genOK_refill h j hj large₂ G _ _ hG G.del G.th' G.rz G.alz G.th0 G.zc G.rq G.th i et
  obtain ⟨A⟩ := GlobalTheory.RunJoin.archAt_of_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p _ nus hpar hpg hC hjm G' hG' he
  obtain ⟨t, -, ⟨Fl⟩⟩ := GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj _ wL wF G'.w Tn _ A
  intro k
  exact ⟨A.Xa k, A.hL k, A.hF k, A.hT k, A.mar k, ⟨Fl.Fl k⟩⟩

end Run

section Point

open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar


end Point

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiAdditive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiAdditive
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.ConstDefCub

theorem isPullCubical_constPt : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq htan A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg1 hg2 hF
  haveI : IsProper o.t.G.hom := o.proper
  have hA : IsAbelianScheme o.t.G := AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi
  refine GlobalTheory.TripleModel.isPullCubical_of_lbIso GlobalTheory.SemiRigid.globalFns hA hF o.t.cub Xo.univ.t.cub ?_
  obtain ⟨w, -, hw, -⟩ := rigIso_congr rfl m.cm m.lin rfl rfl
  have K2 : LBIso (Xo.univ.t.PP.L.pull π') (Xo.univ.t.PP.L.pull (q ≫ π)) :=
    GlobalTheory.T.lineBundle_iso_tangent_pull_constant_deformation E H Dw l Xo c K y.x x' A A' π π' i q hi hπ hπ' hiπ hiq hq
  have hM := Xo.univ.t.PP.isLB
  have h1 : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull (g ≫ π')) := hg1 ▸ ⟨w, hw⟩
  have h2 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ q ≫ π)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull K2 g rfl
  have h3 : LBIso ((Xo.univ.t.PP.L.pull π').pull g) (Xo.univ.t.PP.L.pull (g ≫ π')) :=
    GlobalTheory.FamRep.lbIso_pull_pull hM π' g
  exact LBIso.trans o.t.PP.isLB (pull_isLB hM _) (pull_isLB hM _) h1
    (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) h3.symm h2)

end GlobalTheory.ConstDefCub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiAdditiveStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_lift_tangent_Phi_additive : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), (cubeMapOf hF).IsPullCubical o.t.cub Xo.univ.t.cub := by
  first | exact @GlobalTheory.ConstDefCub.isPullCubical_constPt | exact GlobalTheory.ConstDefCub.isPullCubical_constPt | (intros; apply GlobalTheory.ConstDefCub.isPullCubical_constPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MassLinkSD

open Formalism.BasicNotions.TH Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_det_ne {D : D7} (V : HSp D) : V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  have hx : ∀ y, V.hT y (∑ j, v j • V.frame j) = 0 := by
    intro y
    rw [← V.frame.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
    calc _ = (starRingEnd _) (V.frame.repr y i) * ∑ j, V.hT (V.frame i) (V.frame j) * v j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have := V.nondeg.2 _ hx
  exact hv (funext (Fintype.linearIndependent_iff.1 V.frame.linearIndependent v this))

end GlobalTheory.MassLinkSD

namespace GlobalTheory.MassLinkSD

open Formalism.BasicNotions.TH Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.MassLinkSD

namespace GlobalTheory.MassLinkSD

end GlobalTheory.MassLinkSD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponent
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

namespace GlobalTheory.BddCusp

theorem mul_mem_cuspOn_of_bdd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s hK hU hpq h0 hdec hs hZ hb G hG f hf
  exact mul_mem_cuspOn_of_isSec h0 hs hZ
    (fun σ hσ k => GlobalTheory.T.isSec_reading_decreasing_integer_exponents E H Dw l Xo c σ r (U σ) hK hσ (hU σ hσ) hpq G₀ h0 hdec s hs k) hb hG hf

end GlobalTheory.BddCusp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemCuspFormsOfBoundedSectionComponentStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  first | exact @GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd | exact GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd | (intros; apply GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd <;> assumption)
end
end
