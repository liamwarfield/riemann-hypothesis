module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.InfinitePlaceGluing.AdmissibleRightTranslate
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleEqDiagonalMulUnitOfAbsEqOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private lemma eq_one_of_mul {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma ab_pos_eq {p : IdeleGroup ℚ} (hp : p ∈ RationalIdeles.positiveSubgroup) :
    ab p = (RationalIdeles.realPart p : ℝ) := by
  obtain ⟨h1, h2⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  have hw := RationalIdeles.isReal_infinitePlace (default : InfinitePlace ℚ)
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [InfinitePlace.mult, hw]
  have hn : ‖(p : AdeleRing (𝓞 ℚ) ℚ).1 default‖ = (RationalIdeles.realPart p : ℝ) := by
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _), ← RationalIdeles.realEquiv_apply, ← RationalIdeles.coe_realPart, Real.norm_eq_abs, abs_of_pos h2]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, IdeleGroup.finiteModule_eq_one_of_mem h1, mul_one, IdeleGroup.infiniteModule,
    Fintype.prod_subsingleton _ (default : InfinitePlace ℚ), hmult, pow_one, hn]

theorem UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one :
    ∀ a : IdeleGroup ℚ, ab a = 1 → ∃ (r : ℚˣ), ∃ u ∈ UU, a = IdeleGroup.diagonal ℚ r * u := by
  intro a ha
  obtain ⟨⟨r, p⟩, hp⟩ := RationalIdeles.mulMap_bijective.2 a
  rw [RationalIdeles.mulMap_apply] at hp
  have hp' : a = IdeleGroup.diagonal ℚ r * (p : IdeleGroup ℚ) := hp.symm
  have hab : ab (p : IdeleGroup ℚ) = 1 := by
    rw [hp', ab_mul, ab_diagonal, one_mul] at ha
    exact ha
  obtain ⟨h1, -⟩ := RationalIdeles.mem_positiveSubgroup.1 p.2
  have hre : RationalIdeles.realEquiv ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
    rw [← RationalIdeles.coe_realPart, ← ab_pos_eq p.2, hab]
  have hone : ((p : IdeleGroup ℚ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
    RationalIdeles.realEquiv.injective (hre.trans (map_one _).symm)
  refine ⟨r, p, ⟨hone, fun v => ?_⟩, hp'⟩
  obtain ⟨ha', hb'⟩ := (IdeleGroup.mem_standardOpenSubgroup ℚ).1 h1 v
  have hm := IdeleGroup.finite_mul_inv (p : IdeleGroup ℚ) v
  have hmv := congrArg Valued.v hm
  rw [map_mul, map_one] at hmv
  exact eq_one_of_mul ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha')
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb') hmv
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.CuspSubspaceTranslateEqSmulSpecialTranslate
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem cinf_sq {E : Type} [Field E] (y : (Cinf E)ˣ) : ∃ r : (Cinf E)ˣ, r ^ 2 = y := by
  have hy : ∀ w, y.val w ≠ 0 := fun w h => by
    have := congrFun y.mul_inv w
    simp [h] at this
  choose z hz using fun w => IsAlgClosed.exists_pow_nat_eq (y.val w) (n := 2) (by norm_num)
  have hz0 : ∀ w, z w ≠ 0 := fun w h => hy w (by rw [← hz w, h]; simp)
  refine ⟨⟨z, fun w => (z w)⁻¹, funext fun w => mul_inv_cancel₀ (hz0 w), funext fun w => inv_mul_cancel₀ (hz0 w)⟩, Units.ext (funext fun w => ?_)⟩
  exact hz w

private theorem pInf_infId {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : (Cinf E)ˣ) :
    Units.map (pInf E).toMonoidHom (infId E r) = r := by
  have h : ∀ x, pInf E (GlobalTheory.CuspRep.sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  refine Units.ext ?_
  change pInf E (1 - GlobalTheory.CuspRep.sInf E 1 + GlobalTheory.CuspRep.sInf E r.val) = r.val
  simp [h]

private theorem dM_fin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (t : (A E)ˣ)
    (ht : pInf E (t : A E) = 1) : ∃ k, dM t = finGL E 2 k := by
  refine ⟨GeneralLinearGroup.map (pFin E) (dM t), ?_⟩
  have h : GeneralLinearGroup.map (pInf E) (dM t) = 1 := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht]
  conv_lhs => rw [← infGL_mul_finGL (dM t), h, map_one, one_mul]

theorem UpperTheory.cuspSubspace_translate_eq_smul_special_translate :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → ∀ f ∈ P.V, ∀ x : GL (Fin 2) (A E), ∃ (c : ℂ) (f' : Sm E 2) (h : G1 E), f' ∈ P.V ∧ ∀ g, f.1 (g * x) = c * f'.1 (g * gl h) := by
  intro E _ _ _ P ω hω f hf x
  obtain ⟨g0, hg0⟩ := exists_gl_mul_dM x
  obtain ⟨r, hr⟩ := cinf_sq (Units.map (pInf E).toMonoidHom (GeneralLinearGroup.det x))
  obtain ⟨s, hs⟩ : ∃ s : (A E)ˣ, Units.map (pInf E).toMonoidHom s = r := ⟨infId E r, pInf_infId r⟩
  obtain ⟨t, ht⟩ : ∃ t : (A E)ˣ, GeneralLinearGroup.det x = s ^ 2 * t := ⟨(s ^ 2)⁻¹ * GeneralLinearGroup.det x, by group⟩
  have ht1 : pInf E (t : A E) = 1 := by
    have h1 : Units.map (pInf E).toMonoidHom t = 1 := by
      have h2 := congrArg (Units.map (pInf E).toMonoidHom) ht
      rw [map_mul, map_pow, hs, hr] at h2
      exact (mul_eq_left.1 h2.symm)
    exact congrArg Units.val h1
  obtain ⟨k, hk⟩ := dM_fin t ht1
  refine ⟨((ω.1 (ideleNorm ℚ E s) : ℂˣ) : ℂ), act (.fin k) f, g0 * (mD s)⁻¹, P.stable (.fin k) f hf, fun g => ?_⟩
  have hx : x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (gl (g0 * (mD s)⁻¹) * dM t) := by
    have e : dM (s ^ 2) = (gl (mD s))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
      rw [← gl_mD_mul_dM_sq, inv_mul_cancel_left]
    rw [gl_mul, gl_inv]
    conv_lhs => rw [hg0, ht, dM_mul, e]
    rw [ConvolutionTheory.R2.scalar_comm s (gl g0 * (gl (mD s))⁻¹ * dM t), mul_assoc (gl (mD s))⁻¹, ConvolutionTheory.R2.scalar_comm s (dM t)]
    simp only [mul_assoc]
  have hg : g * x = Matrix.GeneralLinearGroup.scalar (Fin 2) s * (g * gl (g0 * (mD s)⁻¹) * finGL E 2 k) := by
    rw [hx, hk, ← mul_assoc g, ← ConvolutionTheory.R2.scalar_comm s g, mul_assoc, mul_assoc]
  rw [hg, hω f hf]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.DiagInvVal
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

private theorem diag_val (F : Type) [Field F] [NumberField F] (t : Fˣ) :
    ((IdeleGroup.diagonal F t : (A F)ˣ) : A F) = rt (t : F) := rfl

private theorem diag_inv_val (F : Type) [Field F] [NumberField F] (t : Fˣ) :
    (((IdeleGroup.diagonal F t : (A F)ˣ)⁻¹ : (A F)ˣ) : A F) = rt ((t : F)⁻¹) := by
  rw [← map_inv, ← Units.val_inv_eq_inv_val]
  rfl

private def cR {F : Type} [Field F] (t : Fˣ) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![g 0 0, g 0 1 * (t : F)⁻¹; (t : F) * g 1 0, g 1 1], by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    have ht : (t : F) ≠ 0 := t.ne_zero
    have : g 0 1 * (t : F)⁻¹ * ((t : F) * g 1 0) = g 0 1 * g 1 0 := by field_simp
    rw [this]
    exact h⟩

private theorem cD_ratS {F : Type} [Field F] [NumberField F] (t : Fˣ)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    cD (IdeleGroup.diagonal F t) (ratS F g) = ratS F (cR t g) := by
  refine Subtype.ext ?_
  rw [M.val_ratS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cD, cR, M.val_ratS, diag_inv_val, diag_val, rt, map_mul]

private theorem cD_mem {F : Type} [Field F] [NumberField F] (t : Fˣ) {x : G1 F} (hx : x ∈ Gam F) :
    cD (IdeleGroup.diagonal F t) x ∈ Gam F := by
  obtain ⟨g, rfl⟩ := hx
  exact ⟨cR t g, (cD_ratS t g).symm⟩

theorem UpperTheory.ConvolutionTheory.R2.M.dConj :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F) (u : G1 F → ℂ), (∀ γ g, u (ratS F γ * g) = u g) → ∀ t : Fˣ, (IntegrableOn (fun g => u (cD (IdeleGroup.diagonal F t) g)) M₀.D M₀.μ ↔ IntegrableOn u M₀.D M₀.μ) ∧ ∫ g in M₀.D, u (cD (IdeleGroup.diagonal F t) g) ∂M₀.μ = ∫ g in M₀.D, u g ∂M₀.μ := by
  intro F _ _ M₀ u hu t
  haveI := M₀.haar
  set T : (A F)ˣ := IdeleGroup.diagonal F t with hT
  have hTi : T⁻¹ = IdeleGroup.diagonal F t⁻¹ := by rw [hT, map_inv]
  let e : G1 F ≃ₜ G1 F :=
    { toFun := cD T
      invFun := cD T⁻¹
      left_inv := fun g => by rw [M.cD_cD, inv_mul_cancel, M.cD_one]
      right_inv := fun g => by rw [M.cD_cD, mul_inv_cancel, M.cD_one]
      continuous_toFun := M.continuous_cD T
      continuous_invFun := M.continuous_cD T⁻¹ }
  let eG : Gam F ≃ Gam F :=
    { toFun := fun γ => ⟨cD T⁻¹ γ.1, by rw [hTi]; exact cD_mem t⁻¹ γ.2⟩
      invFun := fun γ => ⟨cD T γ.1, cD_mem t γ.2⟩
      left_inv := fun γ => Subtype.ext (by
        show cD T (cD T⁻¹ γ.1) = γ.1
        rw [M.cD_cD, mul_inv_cancel, M.cD_one])
      right_inv := fun γ => Subtype.ext (by
        show cD T⁻¹ (cD T γ.1) = γ.1
        rw [M.cD_cD, inv_mul_cancel, M.cD_one]) }
  have hmp : MeasurePreserving (cD T) M₀.μ M₀.μ := M.cdMeas F M₀ T
  have hmpi : MeasurePreserving (cD T⁻¹) M₀.μ M₀.μ := M.cdMeas F M₀ T⁻¹
  have hemb : MeasurableEmbedding (cD T : G1 F → G1 F) := e.measurableEmbedding
  have hD' : IsFundamentalDomain (Gam F) (cD T '' M₀.D) M₀.μ :=
    M₀.fund.image_of_equiv e.toEquiv hmpi.quasiMeasurePreserving eG (fun γ x => by
      show cD T (cD T⁻¹ γ.1 * x) = γ.1 * cD T x
      rw [M.cD_mul, M.cD_cD, mul_inv_cancel, M.cD_one])
  have hpre : cD T ⁻¹' (cD T '' M₀.D) = M₀.D := Set.preimage_image_eq _ e.injective
  have hinv : ∀ (γ : Gam F) (x : G1 F), u (γ • x) = u x := by
    rintro ⟨_, γ, rfl⟩ x
    exact hu γ x
  constructor
  · have h1 := hmp.integrableOn_comp_preimage hemb (f := u) (s := cD T '' M₀.D)
    rw [hpre] at h1
    exact h1.trans (hD'.integrableOn_iff M₀.fund hinv)
  · have h1 := hmp.setIntegral_preimage_emb hemb u (cD T '' M₀.D)
    rw [hpre] at h1
    exact h1.trans (hD'.setIntegral_eq M₀.fund hinv)
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private noncomputable def Bt (M : Meas ℚ) (Φ : GL (Fin 2) (A E) → ℂ) (t : IdeleGroup ℚ) : ℂ :=
  ∫ g in M.D, Φ (em E (gl g * dM t)) ∂M.μ

private theorem continuous_em : Continuous (em E) := by
  have h : Continuous (AdeleBaseChange.adeleMap ℚ E) := AdeleBaseChange.continuous_adeleMap
  refine continuous_adelicGL2_of_continuous_entries (fun i j => ?_) (fun i j => ?_)
  · exact h.comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (A ℚ))).matrix_elem i j)
  · have e : (fun x : GL (Fin 2) (A ℚ) => (((em E x)⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) i j) =
        fun x => AdeleBaseChange.adeleMap ℚ E (((x⁻¹ : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) := by
      funext x
      rw [← map_inv]
      rfl
    rw [e]
    exact h.comp (((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (A ℚ))).comp continuous_inv).matrix_elem i j)

private theorem exists_em_ratGL (γ : GL (Fin 2) ℚ) : ∃ γ', em E (ratGL ℚ 2 γ) = ratGL E 2 γ' := by
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap ℚ E) γ, ?_⟩
  apply Units.ext
  ext i j
  rw [ratGL_apply, show ((em E) ((ratGL ℚ 2) γ)).val i j = AdeleBaseChange.adeleMap ℚ E (((ratGL ℚ 2) γ).val i j) from rfl, ratGL_apply]
  exact AdeleBaseChange.adeleMap_algebraMap _

private theorem Bt_cont (M : Meas ℚ) {Φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous Φ) {C : ℝ} (hb : ∀ g, ‖Φ g‖ ≤ C) :
    Continuous (Bt M Φ) := by
  have hv : M.μ M.D < ⊤ := _root_.UpperTheory.ConvolutionTheory.R2.M.volD ℚ M
  have hcc : Continuous fun p : IdeleGroup ℚ × G1 ℚ => Φ (em E (gl p.2 * dM p.1)) :=
    hc.comp (continuous_em.comp ((continuous_gl.comp continuous_snd).mul (continuous_dM.comp continuous_fst)))
  refine continuous_of_dominated (bound := fun _ => C) (fun t => ?_) (fun t => ?_) ?_ ?_
  · exact (hcc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ fun g => hb _
  · haveI : IsFiniteMeasure (M.μ.restrict M.D) := ⟨by simpa using hv⟩
    exact integrable_const _
  · exact ae_of_all _ fun g => hc.comp (continuous_em.comp (continuous_const.mul continuous_dM))

private theorem Bt_bdd (M : Meas ℚ) {Φ : GL (Fin 2) (A E) → ℂ} {C : ℝ} (hb : ∀ g, ‖Φ g‖ ≤ C) (t : IdeleGroup ℚ) :
    ‖Bt M Φ t‖ ≤ C * M.μ.real M.D :=
  norm_setIntegral_le_of_norm_le_const (_root_.UpperTheory.ConvolutionTheory.R2.M.volD ℚ M) fun g _ => hb _

private theorem Bt_rat (M : Meas ℚ) {Φ : GL (Fin 2) (A E) → ℂ} (hl : ∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) (r : ℚˣ) (t : IdeleGroup ℚ) :
    Bt M Φ (IdeleGroup.diagonal ℚ r * t) = Bt M Φ t := by
  set u : G1 ℚ → ℂ := fun g => Φ (em E (gl g * dM t)) with hu
  have hinv : ∀ γ g, u (ratS ℚ γ * g) = u g := fun γ g => by
    obtain ⟨γ', h'⟩ := exists_em_ratGL (E := E) (Matrix.SpecialLinearGroup.toGL γ)
    simp only [hu]
    rw [gl_mul, gl_ratS, mul_assoc, map_mul, h', hl]
  have hd := (_root_.UpperTheory.ConvolutionTheory.R2.M.dConj ℚ M u hinv r⁻¹).2
  unfold Bt
  rw [← hd]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  obtain ⟨γ, hγ⟩ := exists_ratGL_dM (F := ℚ) r
  obtain ⟨γ', h'⟩ := exists_em_ratGL (E := E) γ
  have e : gl g * dM (IdeleGroup.diagonal ℚ r * t) = ratGL ℚ 2 γ * (gl (cD (IdeleGroup.diagonal ℚ r⁻¹) g) * dM t) := by
    rw [hγ, dM_mul, ← mul_assoc, ← mul_assoc, dM_mul_gl, ← cD_mul_left, ← map_mul, mul_inv_cancel, map_one, cD_one_left]
  simp only [hu]
  rw [e, map_mul, h', hl]

end

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

private theorem UPer_eq (D : Dat ℚ E) (M : Meas ℚ) {ω : HChar ℚ} {Φ : GL (Fin 2) (A E) → ℂ}
    (hcen : ∀ z g, Φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 (ideleNorm ℚ E z) : ℂˣ) : ℂ) * Φ g) (t : IdeleGroup ℚ) :
    UPer D M (fun x => Φ (x * em E (dM t))) =
      ∫ z in normOneFundamentalDomain E, ((ω.1 (ideleNorm ℚ E (z : IdeleGroup E)) : ℂˣ) : ℂ) *
        Bt M Φ ((ideleNorm ℚ E (z : IdeleGroup E))⁻¹ * t) ∂normOneMeasure E := by
  unfold UPer UI SLP Bt
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only []
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  simp only []
  obtain ⟨-, -, -, -, -, -, -, -, hs, -⟩ := szLaws E D
  rw [hs, ← hcen]
  congr 1
  rw [dM_mul, map_mul (em E) (gl g), map_mul (em E) (dM _), ← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.ConvolutionTheory.R2.scalar_comm (z : (A E)ˣ) (em E (gl g))]

private theorem unitCharacter_of_central {P : CuspSub E 2} (D : Dat ℚ E) {ω : HChar ℚ} (hN : GlobalTheory.DiscSpec.IsNormalised P) (hC : CenN P ω) : Unit1 ω := by
  have hu : P.IsUnitary := GlobalTheory.SpehPair.isUnitary_of_isNormalised hN
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 P.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := Function.ne_iff.1 fun e => h0 (Subtype.ext e)
  have hfr : Module.finrank ℚ E = 2 := by rw [Module.finrank_eq_card_basis D.b]; simp
  intro a
  have h1 := hC φ hφ (ideleEmbedding ℚ E a) g
  have h2 := hu.norm_eq hφ (ideleEmbedding ℚ E a) g
  rw [h1, norm_mul, ideleNorm_ideleEmbedding, hfr, map_pow, Units.val_pow_eq_pow_val, norm_pow] at h2
  have h3 : ‖((ω.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := (mul_eq_right₀ (norm_ne_zero_iff.2 hg)).1 h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

private theorem per_zero (D : Dat ℚ E) (M : Meas ℚ) (U : UMeas) {ω ε : HChar ℚ} {Φ : GL (Fin 2) (A E) → ℂ}
    (hA : admitted D ω Φ) (hω : Unit1 ω) (hε : Unit1 ε) (hεN : ∀ z, ε.1 (ideleNorm ℚ E z) = 1)
    (hU : ∀ t, UPer D M (fun x => Φ (x * em E (dM t))) = 0) : Per M U (ω⁻¹ * ε) Φ = 0 := by
  obtain ⟨C, hC⟩ := hA.bdd
  haveI := U.prob
  have hBc := Bt_cont M hA.cont hC
  have hBb := Bt_bdd M hC
  have hdiag : ∀ (χ : HChar ℚ) (r : ℚˣ), χ.1 (IdeleGroup.diagonal ℚ r) = 1 := fun χ r => χ.2.2 r
  have hcm : ∀ t, (ω⁻¹ * ε).1 t = (ω.1 t)⁻¹ * ε.1 t := fun _ => rfl
  set c : IdeleGroup ℚ → ℂ := fun t => (((ω⁻¹ * ε).1 t : ℂˣ) : ℂ) with hc
  have hcc : Continuous c := Units.continuous_val.comp (ω⁻¹ * ε).2.1
  have hcn : ∀ t, ‖c t‖ = 1 := fun t => by
    simp only [hc, hcm, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    rw [hω t, hε t]; simp
  set N : IdeleGroup.normOneSubgroup E → IdeleGroup ℚ := fun z => ideleNorm ℚ E (z : IdeleGroup E) with hNdef
  have hN : Continuous N := continuous_ideleNorm.comp continuous_subtype_val
  set e : IdeleGroup.normOneSubgroup E → ℂ := fun z => ((ω.1 (N z) : ℂˣ) : ℂ) with he
  have hec : Continuous e := Units.continuous_val.comp (ω.2.1.comp hN)
  let f : IdeleGroup ℚ → IdeleGroup.normOneSubgroup E → ℂ := fun t z => c t * (e z * Bt M Φ ((N z)⁻¹ * t))
  let ν := (normOneMeasure E).restrict (normOneFundamentalDomain E)
  haveI : IsFiniteMeasure ν := ⟨by simpa [ν] using normOneMeasure_normOneFundamentalDomain_lt_top E⟩
  have hfc : Continuous (Function.uncurry f) :=
    (hcc.comp continuous_fst).mul ((hec.comp continuous_snd).mul
      (hBc.comp ((hN.comp continuous_snd).inv.mul continuous_fst)))
  have hint : Integrable (Function.uncurry f) (U.υ.prod ν) := by
    refine Integrable.of_bound hfc.aestronglyMeasurable (C * M.μ.real M.D) (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, f, norm_mul, hcn, one_mul]
    rw [show ‖e p.2‖ = 1 from hω _, one_mul]
    exact hBb _
  have hsw := integral_integral_swap hint
  have h1 : ∫ t, ∫ z, f t z ∂ν ∂U.υ = 0 := by
    have : ∀ t, ∫ z, f t z ∂ν = 0 := fun t => by
      simp only [f]
      rw [integral_const_mul]
      have h := UPer_eq D M hA.cen t
      rw [hU t] at h
      rw [show ∫ z, e z * Bt M Φ ((N z)⁻¹ * t) ∂ν = 0 from h.symm, mul_zero]
    simp [this]
  have h2 : ∀ z, ∫ t, f t z ∂U.υ = Per M U (ω⁻¹ * ε) Φ := by
    intro z
    have hab : ab (N z)⁻¹ = 1 := by
      rw [ab_inv]
      have : ab (N z) = 1 := by
        have h := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := ℚ) (L := E) (z : IdeleGroup E)
        simp only [ab, hNdef]
        rw [h]
        have hz : IdeleGroup.ideleModule E (z : IdeleGroup E) = 1 := z.2
        rw [hz]; rfl
      rw [this, inv_one]
    obtain ⟨r, u, hu, e1⟩ := UpperTheory.rat_idele_eq_diagonal_mul_unit_of_abs_eq_one _ hab
    have hεu : ε.1 u = 1 := by
      have h := congrArg ε.1 e1
      rw [map_inv, hεN, map_mul, hdiag, inv_one, one_mul] at h
      exact h.symm
    have hωu : ω.1 u = (ω.1 (N z)⁻¹) := by
      rw [e1, map_mul, hdiag, one_mul]
    have hcu : c u = e z := by
      simp only [hc, he, hcm, hεu, hωu, mul_one, map_inv, inv_inv]
    set G : IdeleGroup ℚ → ℂ := fun t => c t * Bt M Φ t with hG
    have hGc : Continuous G := hcc.mul hBc
    have hfG : ∀ t, f t z = G (u * t) := fun t => by
      simp only [f, hG, e1, mul_assoc]
      rw [Bt_rat M hA.left]
      have : c (u * t) = c u * c t := by
        simp only [hc, map_mul, Units.val_mul]
      rw [this, hcu]
      ring
    simp only [hfG]
    have hm : Measurable fun x : IdeleGroup ℚ => (u * x : (A ℚ)ˣ) := (continuous_const.mul continuous_id).measurable
    have := integral_map (μ := U.υ) hm.aemeasurable (f := G) hGc.aestronglyMeasurable
    rw [U.inv u hu] at this
    exact this.symm
  rw [h1] at hsw
  simp only [h2, integral_const] at hsw
  have hν : ν.real Set.univ ≠ 0 := by
    have hne : (normOneMeasure E) (normOneFundamentalDomain E) ≠ 0 :=
      (isFundamentalDomain_normOneFundamentalDomain E (normOneMeasure E)).measure_ne_zero (NeZero.ne _)
    simp only [ν, measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.toReal_ne_zero.2 ⟨hne, (normOneMeasure_normOneFundamentalDomain_lt_top E).ne⟩
  exact (smul_eq_zero.1 hsw.symm).resolve_left hν

end

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.perU_of :
    PerU := by
  intro E _ _ _ D W M _ P U ω hN hC hZ
  have h1 : Unit1 ω := unitCharacter_of_central D hN hC
  have hT : ∀ φ ∈ Tr P, admitted D ω φ := trAdm_of decE E D P ω ω⁻¹ hC h1 (fun a => by
    rw [show (ω⁻¹ : HChar ℚ).1 a = (ω.1 a)⁻¹ from rfl, inv_mul_cancel, one_pow])
  have key : ∀ ε : HChar ℚ, Unit1 ε → (∀ z, ε.1 (ideleNorm ℚ E z) = 1) → NoPer M U (ω⁻¹ * ε) P := by
    intro ε h1ε hεN f hf h
    refine per_zero D M U (hT _ (Submodule.subset_span ⟨f, hf, h, rfl⟩)) h1 h1ε hεN fun t => ?_
    obtain ⟨c, f', h', hf', e⟩ := UpperTheory.cuspSubspace_translate_eq_smul_special_translate E P ω hC f hf (em E (dM t) * h)
    have e2 : (fun x => (fun g => f.1 (g * h)) (x * em E (dM t))) = fun x => c * f'.1 (x * gl h') := by
      funext x
      simp only [mul_assoc, e]
    rw [e2]
    have hZ' := hZ f' hf' h'
    unfold UPer UI SLP at hZ' ⊢
    simp only [mul_assoc] at hZ' ⊢
    simp only [integral_const_mul]
    rw [hZ', mul_zero]
  have hη : Unit1 W.η⁻¹ := fun a => by
    have h := W.η_sq a
    have h2 : ‖((W.η.1 a : ℂˣ) : ℂ)‖ ^ 2 = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, h]; simp
    have h3 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
    rw [show (W.η⁻¹ : HChar ℚ).1 a = (W.η.1 a)⁻¹ from rfl, Units.val_inv_eq_inv_val, norm_inv, h3, inv_one]
  have k1 := key 1 (fun a => by simp) (fun z => rfl)
  have k2 := key W.η⁻¹ hη (fun z => by
    rw [show (W.η⁻¹ : HChar ℚ).1 (ideleNorm ℚ E z) = (W.η.1 (ideleNorm ℚ E z))⁻¹ from rfl, W.η_norm, inv_one])
  rw [mul_one] at k1
  rw [mul_inv]
  exact ⟨k1, k2⟩
