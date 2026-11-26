module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
public import GroundTheory.AutomorphicForms.GL2.GJGlobalMean
public import Development.AutomorphicArithmetic.WhittakerHecke.IsCompactIntegralIdeleUnitsAndAbsEqOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ZDom
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.zDom :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.ZDom := by
  intro E _ _
  refine ⟨normOneMeasure_normOneFundamentalDomain_lt_top E,
    measurableSet_normOneFundamentalDomain E, ?_⟩
  have hc : Continuous (fun z : ↥(IdeleGroup.normOneSubgroup E) =>
      ((z : IdeleGroup E) : (A E)ˣ)) := continuous_subtype_val
  refine ⟨_, (isCompact_closure_normOneFundamentalDomain E).image hc, ?_⟩
  intro z hz
  exact ⟨z, subset_closure hz, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.QuadraticFormRationalPoints
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

variable {E : Type} [Field E] [NumberField E]

private theorem rp_injective : Function.Injective (rp : (Fin 4 → ℚ) → V4 ℚ) := by
  intro ξ ξ' h
  funext i
  exact AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ (congrFun h i)

private theorem quadraticForm_rational_points (δ : ℚ) (ξ : Fin 4 → ℚ) : q4 δ (rp ξ) = rt (qr δ ξ) := by
  simp [q4, qr, rp, map_sub, map_mul, map_pow]


variable (E) in
private noncomputable def jE : G1 ℚ →* G1 E := Matrix.SpecialLinearGroup.map (am E)

private theorem gl_jE (g : G1 ℚ) : gl (jE E g) = em E (gl g) := by
  apply Units.ext
  ext i j
  rfl

private theorem continuous_jE : Continuous (jE E) := by
  have h : Continuous fun g : G1 ℚ => (g.1).map (am E) :=
    continuous_subtype_val.matrix_map continuous_am
  exact h.subtype_mk _

private theorem injective_jE : Function.Injective (jE E) := by
  intro g g' h
  apply Subtype.ext
  ext i j
  exact am_injective (E := E) (congrFun (congrFun (congrArg Subtype.val h) i) j)

private theorem jE_ratS (g : Matrix.SpecialLinearGroup (Fin 2) ℚ) :
    jE E (ratS ℚ g) = ratS E (Matrix.SpecialLinearGroup.map (algebraMap ℚ E) g) := by
  apply Subtype.ext
  ext i j
  exact am_rt (g i j)

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent.Cp in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.reps :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Reps := by
  intro E _ _ _ D
  obtain ⟨h1, h2, h3⟩ := orbS E D
  obtain ⟨ρ1, -⟩ := orb1 E D
  choose γ hγ using fun i : Orb D.δ => h1 i.1 i.2
  refine ⟨jE E, fun i => ratS E (γ i), gl_jE, continuous_jE, injective_jE,
    fun i => ⟨⟨γ i, rfl⟩, hγ i⟩, ?_, ?_⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, (jE_ratS g).symm⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨ρ, hρ⟩ := ρ1 c
    have hq : qr D.δ (ρ X0) = qr D.δ X0 := by
      apply AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ
      change UpperTheory.ConvolutionTheory.R2.rt _ = UpperTheory.ConvolutionTheory.R2.rt _
      rw [← quadraticForm_rational_points, ← quadraticForm_rational_points, ← hρ, D.quadForm_act, nu_gl]
      simp
    let i : Orb D.δ := ⟨ρ X0, hq⟩
    have hi : rp i.1 = D.act (gl (ratS E c)) (rp X0) := (hρ X0).symm
    have hfix : ∀ x : G1 ℚ, D.act (gl (jE E x)) (rp X0) = rp X0 := fun x =>
      (h2 (jE E x)).2 ⟨x, gl_jE x⟩
    have hstab : D.act (gl (ratS E ((γ i)⁻¹ * c))) (rp X0) = rp X0 := by
      have e : ratS E ((γ i)⁻¹ * c) = (ratS E (γ i))⁻¹ * ratS E c := by rw [map_mul, map_inv]
      rw [e, gl_mul, gl_inv, D.act_mul, ← hi, hγ i, D.act_inv_act]
    obtain ⟨g, hg⟩ := (h3 _).1 hstab
    have hj : ratS E ((γ i)⁻¹ * c) = jE E (ratS ℚ g) := gl_injective (hg.trans (gl_jE _).symm)
    refine ⟨i, ⟨ratS ℚ g, ⟨g, rfl⟩, ?_⟩, ?_⟩
    · rw [← hj, map_mul, map_inv, mul_inv_cancel_left]
    · rintro i' ⟨_, ⟨g', rfl⟩, hi'⟩
      apply Subtype.ext
      apply rp_injective
      rw [hγ i', hi, hi', gl_mul, D.act_mul, hfix]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.BddE
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical Pointwise

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.bddE :
    UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.BddE := by
  intro E _ _ _ P φ hφ C hC
  obtain ⟨c, C₀, hc, hC₀, hred⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.redE E
  have hC' : IsCompact ((gl (F := E) '' C₀) * C) := (hC₀.image continuous_gl).mul hC
  obtain ⟨hL, -, hd⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.decE E P φ hφ
  obtain ⟨B, hB⟩ := hd _ hC' c hc 0
  refine ⟨B, fun h k hk => ?_⟩
  obtain ⟨γ, u, b, k₀, hk₀, hg, hb⟩ := hred h
  have e1 : φ.1 (gl h * k) = φ.1 (gl (nU u * mD b) * (gl k₀ * k)) := by
    rw [← mul_assoc, ← gl_mul, ← hg, gl_mul, gl_ratS, mul_assoc, hL.2]
  have h1 := hB u b (gl k₀ * k) (Set.mul_mem_mul ⟨k₀, hk₀, rfl⟩ hk) hb
  rw [e1]
  simpa using h1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.ExistsForm0
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem exists_form0 {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    {v : LL μ} (hv : v ∈ cuspidalL2 μ) (h0 : v ≠ 0) :
    ∃ V, IsSummand μ V ∧ ∃ f ∈ formsIn μ V, inner ℂ v (clsL μ f) ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : (⨆ V : {V // IsSummand μ V}, V.1) ≤ (ℂ ∙ v)ᗮ := iSup_le fun V => by
    rw [← (formsIrr K n μ V.1 V.2).2.2.2]
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hc _ V.2 f hf)
  have h2 := Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
  rw [summandsSpan K n μ] at h2
  exact h0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 hv)))

private theorem oneInt (f : (AutomorphicForm.UPos 2 1 → A ℚ) → ℂ) :
    ∫ y in GroundTheory.Global.fundamentalSet ℚ, f (fun _ => y) ∂GroundTheory.Global.adeleMeasure ℚ =
      ∫ Y in unipFundamentalDomain ℚ 2 1, f Y ∂unipMeasure ℚ 2 1 := by
  let _ : Unique (AutomorphicForm.UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (AutomorphicForm.UPos 2 1) (A ℚ)) (unipMeasure ℚ 2 1)
      (GroundTheory.Global.adeleMeasure ℚ) := by
    convert measurePreserving_funUnique (GroundTheory.Global.adeleMeasure ℚ) (AutomorphicForm.UPos 2 1)
  rw [← hm.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  · congr 1
    ext Y
    simp [unipFundamentalDomain, Unique.forall_iff]
  · funext Y
    congr 1
    funext p
    simp [Subsingleton.elim p default]

private theorem unip_eq (y : A ℚ) : (unipGL (fun _ : AutomorphicForm.UPos 2 1 => y) : GL (Fin 2) (A ℚ)) = gl (nU y) := by
  ext i j
  change unipMatrix (fun _ : AutomorphicForm.UPos 2 1 => y) i j = (!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply]

private theorem cusp_conj {F : GL (Fin 2) (A ℚ) → ℂ}
    (h : ∀ x, ∫ b in GroundTheory.Global.fundamentalSet ℚ, F (gl (nU b) * x) ∂(GroundTheory.Global.adeleMeasure ℚ) = 0) :
    IsCuspidal (fun x : AdelicGLn.AdelicGL ℚ 2 => starRingEnd ℂ (F x)) := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  rw [constantTerm, ← oneInt (fun X => starRingEnd ℂ (F (unipGL X * g)))]
  simp only [unip_eq]
  rw [integral_conj, h g, map_zero]

private theorem exists_one {F : GL (Fin 2) (A ℚ) → ℂ} (hF : Bd F) (h0 : F ≠ 0) :
    ∃ x : normOneGL (K := ℚ) (n := 2), F (x : AdelicGLn.AdelicGL ℚ 2) ≠ 0 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
  refine ⟨retractOne g, ?_⟩
  rw [coe_retractOne, ← centralSection_inv_mul_comm, ← map_inv, hF.cen]
  exact hg

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent.Cp in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.pairL : UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.PairL := by
  intro μ _ F hF hne hct
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := ℚ) (n := 2) μ
  set ψ : AdelicGLn.AdelicGL ℚ 2 → ℂ := fun x => starRingEnd ℂ (F x) with hψdef
  have hψc : Continuous ψ := continuous_star.comp hF.cont
  have hψl : IsLeftInvariant ψ := fun γ g => congrArg (starRingEnd ℂ) (hF.left γ g)
  obtain ⟨C, hC⟩ := hF.bdd
  have hbd : ∃ C, ∀ g ∈ normOneGL (K := ℚ) (n := 2), ‖ψ g‖ ≤ C := ⟨C, fun g _ => by simpa [hψdef] using hC g⟩
  have hm := GJGlobal.memLp_cuspQuot_of_bounded μ hψc hψl hbd
  have hv : hm.toLp _ ∈ cuspidalL2 μ := GJGlobal.toLp_cuspQuot_mem_cuspidalL2 μ hψc hψl (cusp_conj hct) hbd
  have hv0 : hm.toLp _ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := exists_one hF hne
    have h1 : cuspQuot hψl =ᵐ[quotientMeasure (rationalGLOne (K := ℚ) (n := 2)) μ] 0 := by
      refine (MemLp.coeFn_toLp hm).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have h2 : (fun y : normOneGL (K := ℚ) (n := 2) => ψ y) =ᵐ[μ] 0 :=
      QuasiMeasurePreserving.ae_eq_comp (quasiMeasurePreserving_mk _ μ) h1
    have h3 : starRingEnd ℂ (F (x : AdelicGLn.AdelicGL ℚ 2)) = 0 :=
      congrFun ((Continuous.ae_eq_iff_eq μ (hψc.comp continuous_subtype_val) continuous_const).1 h2) x
    exact hx ((map_eq_zero _).1 h3)
  obtain ⟨V, hV, f, hf, hi⟩ := exists_form0 μ hv hv0
  obtain ⟨hs, hne, hirr, -⟩ := formsIrr ℚ 2 μ V hV
  have hiπ := hs.isIrreducible_iff.2 ⟨hne, hirr⟩
  let π := Fb.ofIrr (formsIn μ V) hs hiπ
  have hπ : Fb.carrier π = formsIn μ V := Fb.carrier_ofIrr _ hs hiπ
  have hfπ : f ∈ Fb.carrier π := by rwa [hπ]
  refine ⟨π, ?_, Fb.ofCusp ℚ 2 f, Fb.mem_carrier.1 hfπ, fun hz => hi ?_⟩
  · intro φ hφ s g
    rw [← Fb.map_carrier π, hπ] at hφ
    obtain ⟨ψ', hψ', rfl⟩ := hφ
    exact hψ'.1 s g
  · rw [L2.inner_def, ← hz]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hm, (clsBasic ℚ 2 μ).2.2.2 f hf.1] with q e1 e2
    rw [e1, e2, RCLike.inner_apply]
    have e3 : cuspQuot hψl q = ψ (Quotient.out q : normOneGL (K := ℚ) (n := 2)) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e3]
    simp [hψdef, Fb.ofCusp]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.MeasurableSetUS
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical
open scoped ENNReal NNReal

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb

def US : Subgroup (A ℚ)ˣ where
  carrier := UU
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨?_, fun v => ?_⟩
    · change (a : A ℚ).1 * (b : A ℚ).1 = 1
      rw [ha, hb, one_mul]
    · rw [Units.val_mul, map_mul, map_mul, ha' v, hb' v, one_mul]
  one_mem' := ⟨rfl, fun v => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨?_, fun v => ?_⟩
    · have h : ((a⁻¹ : (A ℚ)ˣ) : A ℚ).1 * (a : A ℚ).1 = 1 := congrArg Prod.fst (Units.inv_mul a)
      rwa [ha, mul_one] at h
    · have h : Valued.v (H.cp v ((a⁻¹ : (A ℚ)ˣ) : A ℚ)) * Valued.v (H.cp v (a : A ℚ)) = 1 := by
        rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
      rwa [ha' v, mul_one] at h

abbrev GG : Type := ↥(GroundTheory.Automorphic.Reduction.normOneGL (K := ℚ) (n := 2))

abbrev Ga : Subgroup GG := GroundTheory.Automorphic.Reduction.rationalGLOne (K := ℚ) (n := 2)

theorem det_el (g : G1 ℚ) (t : (A ℚ)ˣ) : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl g * dM t) = t := by
  refine Units.ext ?_
  rw [GroundTheory.Automorphic.AdelicGLn.coe_det]
  have h : ((gl g * dM t : GL (Fin 2) (A ℚ)) : Matrix (Fin 2) (Fin 2) (A ℚ)) =
      (g : Matrix (Fin 2) (Fin 2) (A ℚ)) * !![1, 0; 0, (t : A ℚ)] := rfl
  rw [h, Matrix.det_mul, g.det_coe, one_mul, Matrix.det_fin_two_of]
  simp

theorem mem_norm (g : G1 ℚ) (t : US) : gl g * dM (t : (A ℚ)ˣ) ∈ GroundTheory.Automorphic.Reduction.normOneGL (K := ℚ) (n := 2) := by
  rw [GroundTheory.Automorphic.Reduction.mem_normOneGL, det_el]
  exact UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one.2 _ t.2

def pm (p : G1 ℚ × US) : GG := ⟨gl p.1 * dM (p.2 : (A ℚ)ˣ), mem_norm _ _⟩

def us (U : UMeas) : Measure US := U.υ.comap Subtype.val

theorem measurableSet_US : MeasurableSet (US : Set (A ℚ)ˣ) := UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one.1.isClosed.measurableSet

theorem val_emb : MeasurableEmbedding (Subtype.val : US → (A ℚ)ˣ) := MeasurableEmbedding.subtype_coe measurableSet_US

instance us_prob (U : UMeas) : IsProbabilityMeasure (us U) := by
  haveI := U.prob
  refine ⟨?_⟩
  have h : U.υ (US : Set (A ℚ)ˣ)ᶜ = 0 := U.supp
  have h1 : U.υ (US : Set (A ℚ)ˣ) = 1 := (prob_compl_eq_zero_iff measurableSet_US).1 h
  unfold us
  rw [val_emb.comap_apply, Set.image_univ, Subtype.range_coe]
  exact h1

theorem us_mul (U : UMeas) (t : US) : MeasurePreserving (fun x : US => t * x) (us U) (us U) := by
  have hm : Measurable (fun x : US => t * x) := (continuous_const.mul continuous_id).measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs]
  unfold us
  rw [val_emb.comap_apply, val_emb.comap_apply]
  have hs' : MeasurableSet (Subtype.val '' s : Set (A ℚ)ˣ) := val_emb.measurableSet_image.2 hs
  have hmt : Measurable (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ)) :=
    (continuous_const.mul continuous_id).measurable
  have hi : (U.υ.map (fun x : IdeleGroup ℚ => (t * x : (A ℚ)ˣ))) (Subtype.val '' s) = U.υ (Subtype.val '' s) := by
    rw [U.inv t t.2]
  rw [Measure.map_apply hmt hs'] at hi
  rw [← hi]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hx : x ∈ US := by
      have : x = ((t⁻¹ * y : US) : (A ℚ)ˣ) := by
        simp [hyx]
      rw [this]
      exact Subtype.coe_prop _
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have : t * ⟨x, hx⟩ = y := Subtype.ext hyx.symm
    simpa [this] using hy

theorem dM_mul (s t : (A ℚ)ˣ) : dM (s * t) = dM s * dM t := by
  apply Units.ext
  change !![1, 0; 0, ((s * t : (A ℚ)ˣ) : A ℚ)] = !![1, 0; 0, (s : A ℚ)] * !![1, 0; 0, (t : A ℚ)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem dM_gl (t : (A ℚ)ˣ) (g : G1 ℚ) : dM t * gl g = gl (cD t g) * dM t := by
  apply Units.ext
  change !![1, 0; 0, (t : A ℚ)] * (g : Matrix (Fin 2) (Fin 2) (A ℚ)) =
    (cD t g : Matrix (Fin 2) (Fin 2) (A ℚ)) * !![1, 0; 0, (t : A ℚ)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem pm_mul (p q : G1 ℚ × US) : pm p * pm q = pm (p.1 * cD (p.2 : (A ℚ)ˣ) q.1, p.2 * q.2) := by
  apply Subtype.ext
  change gl p.1 * dM (p.2 : (A ℚ)ˣ) * (gl q.1 * dM (q.2 : (A ℚ)ˣ)) =
    gl (p.1 * cD (p.2 : (A ℚ)ˣ) q.1) * dM ((p.2 : (A ℚ)ˣ) * (q.2 : (A ℚ)ˣ))
  have h : gl (p.1 * cD (p.2 : (A ℚ)ˣ) q.1) = gl p.1 * gl (cD (p.2 : (A ℚ)ˣ) q.1) := Units.ext rfl
  rw [dM_mul, h, mul_assoc, ← mul_assoc (dM _) (gl _), dM_gl]
  simp only [mul_assoc]

theorem exists_sl (y : GL (Fin 2) (A ℚ)) (h : GroundTheory.Automorphic.AdelicGLn.det ℚ 2 y = 1) : ∃ g : G1 ℚ, gl g = y := by
  refine ⟨⟨y.val, ?_⟩, Units.ext rfl⟩
  have := congrArg Units.val h
  rwa [GroundTheory.Automorphic.AdelicGLn.coe_det] at this

theorem range_pm : Set.range pm = {x : GG | GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)) ∈ UU} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (gl p.1 * dM (p.2 : (A ℚ)ˣ)) ∈ UU
    rw [det_el]
    exact p.2.2
  · intro hx
    obtain ⟨g, hg⟩ := exists_sl ((x : GL (Fin 2) (A ℚ)) * (dM (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ))))⁻¹) (by
      have h1 := det_el 1 (GroundTheory.Automorphic.AdelicGLn.det ℚ 2 (x : GL (Fin 2) (A ℚ)))
      simp only [map_one, one_mul] at h1
      rw [map_mul, map_inv, h1, mul_inv_cancel])
    refine ⟨(g, ⟨_, hx⟩), Subtype.ext ?_⟩
    change gl g * dM _ = _
    rw [hg, inv_mul_cancel_right]

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.Fb
end
end
