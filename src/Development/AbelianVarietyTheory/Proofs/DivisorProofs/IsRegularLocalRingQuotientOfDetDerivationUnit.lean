module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDatumBaseChangeToCoarserPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalTau

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
open IsLocalRing TensorProduct

namespace GlobalTheory.JacobianDerivation

theorem isRegularLocalRing_quotient : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T)
    (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) →
    (Matrix.of fun i j => D i (f j)).det ∉ n →
    IsRegularLocalRing (Localization.AtPrime n ⧸
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  intro T _ _ h f D n _ hf hdet
  classical
  let A := Localization.AtPrime n
  haveI : IsRegularLocalRing A := IsRegularRing.isRegularLocalRing_localization n
  let x : Fin h → A := fun j => algebraMap T A (f j)
  have hx : ∀ j, x j ∈ maximalIdeal A := fun j =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff A n (f j)).mpr (hf j)

  have hrow0 : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 →
      ∀ i, ∑ j, a j * algebraMap T A (D i (f j)) ∈ maximalIdeal A := by
    intro a ha i
    obtain ⟨D', hD'⟩ := @GlobalTheory.derivation_extend_localization_atPrime ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
      (@IsScalarTower.of_algebraMap_eq' ℤ T A _ _ _ (Ring.toIntAlgebra T) _ (Ring.toIntAlgebra A)
        (Subsingleton.elim _ _)) n _ _
      { toFun := fun t => algebraMap T A (D i t)
        map_add' := fun s t => by simp
        map_smul' := fun m t => by simp [Algebra.smul_def]
        map_one_eq_zero' := by simp
        leibniz' := fun s t => by simp [Algebra.smul_def] }
    letI : Algebra ℤ A := Ring.toIntAlgebra A
    have hsq : ∀ y ∈ maximalIdeal A ^ 2, D' y ∈ maximalIdeal A := by
      intro y hy
      rw [pow_two] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun y z hy hz => ?_)
      · rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_right _ _ hb)
      · rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    have h1 := hsq _ ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    have h2 : ∀ j, D' (a j * x j) = a j * algebraMap T A (D i (f j)) + x j * D' (a j) := by
      intro j
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hD']
      rfl
    simp_rw [h2, Finset.sum_add_distrib] at h1
    have h3 : ∑ j, x j * D' (a j) ∈ maximalIdeal A :=
      Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx j)
    simpa using Ideal.sub_mem _ h1 h3
  have hind : ∀ a : Fin h → A, ∑ j, a j * x j ∈ maximalIdeal A ^ 2 → ∀ j, a j ∈ maximalIdeal A := by
    intro a ha
    have hrow := hrow0 a ha
    let φ : T →+* ResidueField A := (residue A).comp (algebraMap T A)
    let M : Matrix (Fin h) (Fin h) (ResidueField A) := φ.mapMatrix (Matrix.of fun i j => D i (f j))
    have hM : M.det ≠ 0 := by
      rw [← RingHom.map_det]
      intro h0
      have hu : IsUnit (algebraMap T A (Matrix.of fun i j => D i (f j)).det) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A n _).mpr hdet
      exact (residue_ne_zero_iff_isUnit _).mpr hu h0
    have hv : M.mulVec (fun j => residue A (a j)) = 0 := by
      funext i
      have := (residue_eq_zero_iff _).mpr (hrow i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simp only [Matrix.mulVec, dotProduct, M, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, Pi.zero_apply, φ, RingHom.comp_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_comm]
    intro j
    have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hv) j
    exact (residue_eq_zero_iff _).mp this

  let τ : Fin h → maximalIdeal A := fun i => ⟨x i, hx i⟩
  have hτ : LinearIndependent (ResidueField A) (fun i => (maximalIdeal A).toCotangent (τ i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose a ha using fun j => residue_surjective (g j)
    have h1 : (maximalIdeal A).toCotangent (∑ j, a j • τ j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, ← ha j]
      rfl
    rw [Ideal.toCotangent_eq_zero] at h1
    have h2 : ∑ j, a j * x j ∈ maximalIdeal A ^ 2 := by
      simpa [τ] using h1
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr (hind a h2 i)
  obtain ⟨J, _, t, hs, hd⟩ := GlobalTheory.RegularQuotient.exists_extend A τ hτ
  have hrange : (Set.range fun i => ((τ i : maximalIdeal A) : A)) = Set.range x := rfl
  rw [hrange] at hs
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quot_regular A t x hs hd
  have hmap : (Ideal.span (Set.range f)).map (algebraMap T A) = Ideal.span (Set.range x) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  show IsRegularLocalRing (A ⧸ (Ideal.span (Set.range f)).map (algebraMap T A))
  rw [hmap]
  exact hreg

end GlobalTheory.JacobianDerivation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnitStatement
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T) (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) → (Matrix.of fun i j => D i (f j)).det ∉ n → IsRegularLocalRing (Localization.AtPrime n ⧸ (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  first | exact @GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient | exact GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient | (intros; apply GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSPkg

open GlobalTheory.DeRham GlobalTheory.Cris

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem ksPackage : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  intro PP E _ _ _ H Dw l Xo c TF U δ K _ _ P hU y' hU' hs hev
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ y' = frX P := by
    apply GlobalTheory.FlagMod.xF_ext (Y := TF.Y)
    · rw [Category.assoc, hs, spMap_comp_spMap]
      congr 1
    · exact GlobalTheory.FlagMod.frX_snd P
    · have h1 : ⊤ ≤ (spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ (y' ≫ TF.Y.j)) ⁻¹ᵁ U.1 :=
        GlobalTheory.FlagMod.le_preimage_comp _ hU'
      rw [Category.assoc, ← GlobalTheory.FlagMod.spMap_ev _ U.2 h1, ← GlobalTheory.FlagMod.spMap_ev _ U.2 hU,
        GlobalTheory.FlagMod.ev_spMap _ _ _ hU' h1]
      refine congrArg (fun f => spMap f ≫ (U.2 : IsAffineOpen U.1).fromSpec) ?_
      ext r
      rw [RingHom.comp_apply, hev r]
      simp [GlobalTheory.FlagTan.red]
  have hx : GlobalTheory.FlagTan.IsTanX P (y' ≫ pullback.fst _ _) := by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, spMap_comp_spMap]
      rfl
    · rw [← Category.assoc, hred, GlobalTheory.FlagMod.frX_fst]
  have P5 := PP.p5
  obtain ⟨A', _, π', hπ'⟩ := GlobalTheory.FlagTan.exists_isGrpPullback Xo.univ.t.G (y' ≫ pullback.fst _ _)
  obtain ⟨A, _, j, hj⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A' (GlobalTheory.DeRham.epsRed K)
  have hπ : IsGrpPullback A Xo.univ.t.G P.x (j ≫ π') := by
    have := hj.comp hπ'
    rw [← hx.2]
    exact this
  have hUn := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hUn hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  have : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ j = j ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc j π', ← ha z]
    · rw [Category.assoc, Category.assoc, Over.w, hj.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ, hpol, hiso, hperf, hlag⟩ := GlobalTheory.PolExists.polForm_exists P5 Xo hπ
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P5 Xo hπ a ha hpol
  have hK := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_field P5 hj hA' gA'
  obtain ⟨ub, hu, ht, he, hbasis⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback P hπ a ha
  have hL := (P5.2.1 K A _ hA gA).1
  choose hb hbl using fun k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) => hL.2 (ub k.1 k.2) (ht k.1 k.2)
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P5 P hπ ub hu hb hbl
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hbl k).push (a.act z)
    rw [he] at h1
    exact h1.sub_mem ((hbl k).smul _)
  have hrow : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (a₀ : Fin (Dw.mult (conjEmb τ.1))),
      ∃ w, GlobalTheory.FlagTan.IsKSRow hj ψ hb ⟨conjEmb τ.1, a₀⟩ w := fun τ a₀ => by
    obtain ⟨_, w, -, hw⟩ := GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field hj a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift hj a a' hc z hw)
      χ ub hb hspan hind heig hbasis τ.1 (conjEmb τ.1)
      (fun z => by simp only [χ, RingHom.comp_apply, GlobalTheory.KSExist.conj_embK]) a₀
    exact ⟨w, hw⟩
  exact ⟨A, inferInstance, A', inferInstance, j ≫ π', π', j, hj, ψ, ub, hb, _, hπ, hπ', rfl, hpol, hu,
    fun σ k => hbl ⟨σ, k⟩, hrow, hA, gA, hA', gA', LB.isLB_pull Xo.univ.t.PP.isLB _⟩

end GlobalTheory.KSPkg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_derivation_affine_chart : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (δ : Γ(TF.Y.X, U.1) → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P : FrPt Xo c K) (hU : ⊤ ≤ (frX P ≫ TF.Y.j) ⁻¹ᵁ U.1) (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) → (∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P ≫ TF.Y.j) U.1 hU (δ r))) → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)) (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)) (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → GlobalTheory.DeRham.HdR A) (g : ℕ), IsGrpPullback A Xo.univ.t.G P.x π ∧ IsGrpPullback A' Xo.univ.t.G (y' ≫ pullback.fst _ _) π' ∧ i ≫ π' = π ∧ GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ σ k, (ub σ k).left ≫ π = P.u σ k) ∧ (∀ σ k, GlobalTheory.DeRham.IsLieImage (hb ⟨σ, k⟩) (ub σ k)) ∧ (∀ (τ : GlobalTheory.FlagTan.psiSet H) (a : Fin (Dw.mult (conjEmb τ.1))), ∃ w, GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, a⟩ w) ∧ IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧ IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom ∧ (Xo.univ.t.PP.L.pull π).IsLB := by
  first | exact @GlobalTheory.KSPkg.ksPackage | exact GlobalTheory.KSPkg.ksPackage | (intros; apply GlobalTheory.KSPkg.ksPackage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePoint
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

theorem frameVector_isCombination_tangentBasis_flagCover_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}
    (X : GlobalTheory.FlagMod.FlagCover Y) (U : Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left))
    (h1 : ∀ i, IsTanAtG Y.t (LogKS.chart U) (v i))
    (h2 : ∀ w', IsTanAtG Y.t (LogKS.chart U) w' →
      ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (LogKS.chart U) v cf w')
    (h3 : ∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG Y.t (LogKS.chart U) v
      (Pi.single (e ⟨τ, i⟩) (algX Y.s U.1 (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (Y.t.act.act a).left))
    (k : X.F.J) (S : Type) [CommRing S] (z' : Sp S ⟶ X.YY) (x : Sp S ⟶ Y.X) (hU : ⊤ ≤ x ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ z' ⁻¹ᵁ X.F.U k) (hx : z' ≫ X.π = x) :
    ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
      IsCombAtG Y.t x (fun j => spMap (dualMap (ev x U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i)
        (tv (X.F.vecAt k z' hk hx σ i)).left := by
  classical
  subst hx
  have hxψ : spMap (ev (z' ≫ X.π) U.1 hU) ≫ LogKS.chart U = z' ≫ X.π := GlobalTheory.FlagMod.spMap_ev _ U.2 hU
  obtain ⟨b1, b2⟩ := GlobalTheory.LocM.FrameBase.tanBasis_baseChange Y.t (ev (z' ≫ X.π) U.1 hU) (LogKS.chart U) n v h1 h2
  rw [hxψ] at b1 b2

  set ψ := ev (z' ≫ X.π) U.1 hU with hψ
  let φ : c.F →+* S := (ev ((z' ≫ X.π) ≫ Y.s) ⊤ le_top).comp (toΓ c.F)
  have hφ : z' ≫ X.π ≫ Y.s = spMap φ := by
    rw [GlobalTheory.FlagMod.spMap_ev_top, Category.assoc]
  have hφψ : ∀ r : c.F, ψ (algX Y.s U.1 r) = φ r := fun r =>
    GlobalTheory.FlagMod.ev_appLE (z' ≫ X.π) Y.s (by simp) hU le_top (toΓ c.F r)
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (z' ≫ X.π) Y.t.G := fun m => GlobalTheory.LieMet.tanOf (b1 m)
  have hb : ∀ W, ∃! a : Fin n → S, ∑ i, a i • V i = W := fun W => by
    obtain ⟨a, ha, hu⟩ := b2 _ (GlobalTheory.LieMet.isTan_tv W)
    exact ⟨a, ((GlobalTheory.LieMet.isComb_iff V a W).1 ha).symm,
      fun a' ha' => hu a' ((GlobalTheory.LieMet.isComb_iff V a' W).2 ha'.symm)⟩
  have hV : ∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)) (a : 𝓞 E),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)) = φ (embK c τ a) • V (e ⟨τ, j⟩) := by
    intro τ j a
    have h := (GlobalTheory.TanBaseChange.tan_comb_baseChange E H Y.X Y.t _ S ψ (LogKS.chart U) _ hxψ).2 n v _ _ (h3 a τ j)
    have e1 : (fun i => ψ ((Pi.single (e ⟨τ, j⟩) (algX Y.s U.1 (embK c τ a)) : Fin n → Γ(Y.X, U.1)) i)) =
        fun i => (Pi.single (e ⟨τ, j⟩) (φ (embK c τ a)) : Fin n → S) i := by
      funext i
      by_cases hi : i = e ⟨τ, j⟩
      · subst hi; simp [hφψ]
      · simp [Pi.single_apply, hi]
    rw [e1] at h
    have e2 : spMap (dualMap ψ) ≫ v (e ⟨τ, j⟩) ≫ (Y.t.act.act a).left =
        (tv (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act a (V (e ⟨τ, j⟩)))).left := by
      rw [← Category.assoc]; rfl
    rw [e2] at h
    rw [(GlobalTheory.LieMet.isComb_iff V _ _).1 h]
    simp [Pi.single_apply]
  letI : Algebra c.F S := φ.toAlgebra
  have hs := GlobalTheory.FlagEmb.EigSpread.splits (E := E) c
  have hu : ∀ z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR Y.t.act) (embK c z.1) (V (e z)) :=
    fun z a => hV z.1 z.2 a
  have hb' : ∀ w, ∃! a : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → S, ∑ z, a z • V (e z) = w := fun w => by
    obtain ⟨a, ha, hu⟩ := hb w
    refine ⟨fun z => a (e z), ?_, fun a' ha' => ?_⟩
    · rw [← ha]; exact Equiv.sum_comp e (fun i => a i • V i)
    · have h' : ∑ i, a' (e.symm i) • V i = w := by
        rw [← ha', ← Equiv.sum_comp e.symm (fun z => a' z • V (e z))]; simp
      have := hu _ h'
      funext z
      have := congrFun this (e z)
      simpa using this
  have key : ∀ σ i, ∃ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • V (e ⟨σ, j⟩) = X.F.vecAt k z' hk rfl σ i :=
    fun σ i => (GlobalTheory.FlagEmb.EigSpread.block_basis hs (fun z => V (e z)) hu hb' σ _
      (fun a => GlobalTheory.VarFlag.actR_vecAt X φ z' k hk hφ σ i a)).exists
  choose C hC using key
  refine ⟨fun σ => Matrix.of fun i j => C σ i j, fun σ i => ?_⟩
  exact (GlobalTheory.LieMet.isComb_iff (fun j => V (e ⟨σ, j⟩)) (C σ i) _).2 (hC σ i).symm

theorem isCombAtG_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv k S _ z hU hk hx
  exact frameVector_isCombination_tangentBasis_flagCover_point TF.X U e v hv.1 hv.2.1 hv.2.2 k S (z ≫ inc₀ TF.X Z) (z ≫ toBase TF Z) hU hk hx

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameVectorIsCombinationEigenbasisFlagSpacePointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameVector_isCombination_eigenbasis_flagSpace_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (k : TF.X.F.J) (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1) (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z), ∃ C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, ∀ (σ : E →+* ℂ) (i : Fin (Dw.mult σ)), IsCombAtG TF.Y.t (z ≫ toBase TF Z) (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (C σ i) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left := by
  first | exact @GlobalTheory.LogPole.isCombAtG_block | exact GlobalTheory.LogPole.isCombAtG_block | (intros; apply GlobalTheory.LogPole.isCombAtG_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqOfIsUnitFinrank
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep


open Module in
theorem comap_map_eq_of_isUnit_finrank : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing V'] [IsDomain V'] [Algebra V V'] [Module.Finite V V'], Function.Injective (algebraMap V V') → IsUnit ((Module.finrank V V' : ℕ) : V) → ∀ I : Ideal V, (I.map (algebraMap V V')).comap (algebraMap V V') = I := by
  intro V V' _ _ _ _ _ _ _ hinj hunit I
  refine le_antisymm ?_ Ideal.le_comap_map
  let K := FractionRing V
  let L := FractionRing V'
  have hinjL : Function.Injective (algebraMap V L) := by
    rw [IsScalarTower.algebraMap_eq V V' L]
    exact (IsFractionRing.injective V' L).comp hinj
  haveI : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr hinjL
  letI : Algebra K L := FractionRing.liftAlgebra V L
  haveI : IsScalarTower V K L := FractionRing.isScalarTower_liftAlgebra V L
  have hrank : finrank K L = finrank V V' := IsFractionRing.finrank_eq V K V' L
  have hn0 : finrank K L ≠ 0 := by
    intro h
    rw [← hrank, h, Nat.cast_zero] at hunit
    exact not_isUnit_zero hunit
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hn0)
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  haveI : Algebra.IsIntegral V V' := Algebra.IsIntegral.of_finite V V'

  have htrV : ∀ z : V', ∃ t : V, algebraMap V K t = Algebra.trace K L (algebraMap V' L z) := by
    intro z
    have hz : IsIntegral V (algebraMap V' L z) :=
      (Algebra.IsIntegral.isIntegral (R := V) z).map (IsScalarTower.toAlgHom V V' L)
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace hz)
  have hmul : ∀ (i : V) (w : L), Algebra.trace K L (algebraMap V L i * w) =
      algebraMap V K i * Algebra.trace K L w := by
    intro i w
    rw [IsScalarTower.algebraMap_apply V K L, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have key : ∀ y ∈ I.map (algebraMap V V'), ∀ z : V', ∃ c ∈ I,
      algebraMap V K c = Algebra.trace K L (algebraMap V' L (z * y)) := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩ z
      obtain ⟨t, ht⟩ := htrV z
      refine ⟨i * t, I.mul_mem_right t hi, ?_⟩
      rw [map_mul, ht, mul_comm z, map_mul, ← IsScalarTower.algebraMap_apply V V' L, hmul]
    · intro z
      exact ⟨0, I.zero_mem, by simp⟩
    · intro x y _ _ hx hy z
      obtain ⟨c, hc, hcx⟩ := hx z
      obtain ⟨d, hd, hdy⟩ := hy z
      exact ⟨c + d, I.add_mem hc hd, by rw [map_add (f := _), hcx, hdy, mul_add, map_add (f := _), map_add (f := _)]⟩
    · intro w x _ hx z
      obtain ⟨c, hc, hcx⟩ := hx (z * w)
      exact ⟨c, hc, by rw [hcx, smul_eq_mul, _root_.mul_assoc]⟩
  intro a ha
  obtain ⟨c, hc, hca⟩ := key _ ha 1
  rw [_root_.one_mul, ← IsScalarTower.algebraMap_apply V V' L, IsScalarTower.algebraMap_apply V K L,
    Algebra.trace_algebraMap, hrank, nsmul_eq_mul, ← map_natCast (algebraMap V K), ← map_mul] at hca
  have hc' : c = (finrank V V' : V) * a := IsFractionRing.injective V K hca
  obtain ⟨u, hu⟩ := hunit
  have : a = ↑u⁻¹ * c := by rw [hc', ← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [this]
  exact I.mul_mem_left _ hc

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegree
open IsLocalRing

namespace GlobalTheory.LocExt

theorem exists_isCN_integralClosure_of_isUnit_finrank : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.TorRef.IsCN V → ∀ (K' : Type) [Field K'] [Algebra (FractionRing V) K'] [FiniteDimensional (FractionRing V) K'], IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (j : V' →+* K'), GlobalTheory.TorRef.IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ Function.Injective j ∧ j.comp io = (algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V)) ∧ ∀ x : K', (∃ P : Polynomial V, P.Monic ∧ P.eval₂ ((algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V))) x = 0) → ∃ y, j y = x := by
  intro V _ _ _ hV K' _ _ _ hunit
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hV
  let K := FractionRing V
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective V K)
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := integralClosure V K'
  haveI hWf : Module.Finite V W := IsIntegralClosure.finite V K K' W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := V) W
  have hVL : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinjW : Function.Injective (algebraMap V W) := fun x y h => hVL (congrArg Subtype.val h)
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have h1 : (maximalIdeal W).comap (algebraMap V W) = maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal W))
  have hlocW : IsLocalHom (algebraMap V W) := ((local_hom_tfae _).out 1 5).2 h1
  haveI : IsFractionRing W K' := IsIntegralClosure.isFractionRing_of_finite_extension V K K' W
  have hrank : Module.finrank V W = Module.finrank K K' := (IsFractionRing.finrank_eq V K W K').symm
  have hunit' : IsUnit ((Module.finrank V W : ℕ) : V) := by rw [hrank]; exact hunit
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, (integralClosure V K').val.toRingHom,
    ⟨IsNoetherianRing.of_finite V W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hinjW,
    RingHom.finite_algebraMap.2 hWf, hlocW,
    GlobalTheory.Poinc.Sep.comap_map_eq_of_isUnit_finrank V W hinjW hunit',
    Subtype.val_injective, RingHom.ext fun _ => rfl, ?_⟩
  rintro x ⟨P, hmon, hP⟩
  exact ⟨⟨x, P, hmon, hP⟩, rfl⟩

end GlobalTheory.LocExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalIntegralClosureUnitDegreeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_normal_integralClosure_unit_degree : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.TorRef.IsCN V → ∀ (K' : Type) [Field K'] [Algebra (FractionRing V) K'] [FiniteDimensional (FractionRing V) K'], IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (j : V' →+* K'), GlobalTheory.TorRef.IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ Function.Injective j ∧ j.comp io = (algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V)) ∧ ∀ x : K', (∃ P : Polynomial V, P.Monic ∧ P.eval₂ ((algebraMap (FractionRing V) K').comp (algebraMap V (FractionRing V))) x = 0) → ∃ y, j y = x := by
  first | exact @GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank | exact GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank | (intros; apply GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelAutomorphismIntegralMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelMoveRestr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frPt_ptF {K : Type} [Field K] [Algebra c.F K] (t : Sp K ⟶ Xo.XF c)
    (ht : t ≫ pullback.snd _ _ = spMap (algebraMap c.F K)) : ∃ y : FrPt Xo c K, ptF y = t := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt (Xo := Xo) (c := c) (S := K) (t ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, sOf, ← Spec.map_comp]; rfl)
  refine ⟨y, pullback.hom_ext ?_ ?_⟩
  · simp only [ptF, pullback.lift_fst]; exact hy
  · simp only [ptF, pullback.lift_snd]; exact ht.symm

theorem restr_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ γ
  haveI : IsSeparated Xo.s := Formalism.L2.Pj.sepX Xo
  haveI : IsReduced (Xo.XF c) := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  refine ext_of_fromSpecResidueField_eq _ _ (pullback.snd _ _) Set.univ dense_univ (fun x _ => ?_) ?_
  · let t : Spec ((V₀ TF.Y Z).residueField x) ⟶ Sp c.F :=
      (V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z ≫ pullback.snd _ _
    letI : Algebra c.F ((V₀ TF.Y Z).residueField x) := (Spec.preimage t).hom.toAlgebra
    obtain ⟨y, hy⟩ := exists_frPt_ptF (K := (V₀ TF.Y Z).residueField x)
      ((V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z) (by
        rw [Category.assoc]
        exact (Spec.map_preimage t).symm)
    have h1 := hρ.2 γ ((V₀ TF.Y Z).residueField x) y ((V₀ TF.Y Z).fromSpecResidueField x) hy.symm
    rw [h1, GlobalTheory.CompLevelStab.ptF_move hpq hA Xo c, hy, Category.assoc]
  · have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    have h0 := hρ.1 γ
    rw [GlobalTheory.CompLevelStab.j₀_s₀, hid, Category.comp_id] at h0
    rw [Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_snd]
    exact h0

end GlobalTheory.LevelMoveRestr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InteriorLevelActionEqRestrictionLevelMoveInvStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interiorLevelAction_eq_restriction_levelMove_inv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).asIso.hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  first | exact @GlobalTheory.LevelMoveRestr.restr_eq | exact GlobalTheory.LevelMoveRestr.restr_eq | (intros; apply GlobalTheory.LevelMoveRestr.restr_eq <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem exists_isGrpPullback_extend : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X' V : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → ∀ (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ] (σ : V ⟶ V) (σ' : X' ⟶ X'), σ ≫ ℓ = ℓ ≫ σ' → ∀ (G' : Over X') [GrpObj G'], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' → ∀ (A : Over V) [GrpObj A] (κ : A.left ⟶ G'.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A G' ℓ κ → ∀ ν : A.left ⟶ A.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A σ ν → ∃ M : G'.left ⟶ G'.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G' σ' M ∧ κ ≫ M = ν ≫ κ := by
  intro hext X' V _ hS ℓ _ _ σ σ' hσ G' _ hG A _ κ hκ ν hν
  have hGσ : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback σ').obj G') := IsSemiAbelian.pullback _ _ hG
  have h1 : IsGrpPullback A G' (ℓ ≫ σ') (ν ≫ κ) := (hν.comp hκ).congr hσ rfl
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor σ' ℓ h1
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨e, ⟨he, he'⟩, -⟩ := hext.existsUnique_iso_of_isGrpPullback hS hG hGσ hκ h2 (Iso.refl A)
  haveI := he
  refine ⟨e.hom.left ≫ pullback.fst _ _, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' σ')).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, ← he']
    exact pullback.lift_fst _ _ _

theorem eq_of_comp_eq_of_isGrpPullback {X' V : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X']
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ]
    (G' : Over X') [GrpObj G'] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G') (A : Over V) [GrpObj A]
    (κ : A.left ⟶ G'.left) (hκ : IsGrpPullback A G' ℓ κ) (f g : G'.left ⟶ G'.left)
    (h : f ≫ G'.hom = g ≫ G'.hom) (hfg : κ ≫ f = κ ≫ g) : f = g := by
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS ℓ
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G' hG
  have : IsSchemeTheoreticallyDominant κ := .of_isPullback hκ.1.flip
  exact GlobalTheory.ExtUnique.hom_ext_of_dominant G'.hom h κ hfg

end GlobalTheory.EqvAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautBaseChangeTripleLiftLeft
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautEx

theorem toUnit_left {S : Scheme.{0}} (X : Over S) : (toUnit X).left = X.hom := by
  simpa using Over.w (toUnit X)

section Gen

variable {Y : Scheme.{0}} {M : LB Y}

def mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩

theorem gm_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {y : Y} {i : M.ι} (h : y ∈ M.U i) :
    gm (𝟙 Y) y (M.U i) ((mulU u t).s i) = gm (𝟙 Y) y ⊤ u * gm (𝟙 Y) y (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res (𝟙 Y) y _ h _))

theorem isGen_mulU (u : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (mulU u t).IsGen := by
  intro i j
  refine unit_ext fun x hx => ?_
  have e := congrArg (gm (𝟙 Y) x _) (ht i j)
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx] at e
  rw [gm_res (𝟙 Y) x inf_le_left hx, map_mul, gm_res (𝟙 Y) x inf_le_right hx, gm_mulU u t hx.1, gm_mulU u t hx.2, e]
  exact mul_left_comm _ _ _

variable {X Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem val_mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι)
    (hJ : Good L z J) : val (mulU u t) r z J = gm r z ⊤ u * val t r z J :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ (hJ.mem φ r) _))

end Gen

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

abbrev fC : Sp (MvPowerSeries (Fin N) W) ⟶ Sp W := spMap MvPowerSeries.C

abbrev Bp : Over (Sp (MvPowerSeries (Fin N) W)) := (Over.pullback (fC (W := W) N)).obj T.B

theorem isAb_Bp : IsAbelianScheme (Bp T N) := GlobalTheory.isAbelianScheme_pullback_obj _ _ T.isAb

instance : IsCommMonObj (Bp T N) := (isAb_Bp T N).comm

theorem cart : IsGrpPullback (Bp T N) T.B (fC N) (pullback.fst T.B.hom (fC N)) := isGrpPullback_pullback T.B _

abbrev cm : CubeMap (Bp T N) T.B := cubeMapOf (cart T N)

theorem pullSt : ∃ (hL : (T.M.L.pull (cm T N).F).IsLB) (hr : ((cm T N).rigPull T.M.L T.M.rig).IsGen),
    (∃ c' : CubicalStr (Bp T N) ((cm T N).rigLB T.M hL hr), (cm T N).IsPullCubical c' T.cub) ∧
      (T.M.IsSymmetric → ((cm T N).rigLB T.M hL hr).IsSymmetric) :=
  proved_CubePullSt _ _ T.B (Bp T N) (cm T N) T.M T.cub

abbrev Mp : RigLB (Bp T N) := (cm T N).rigLB T.M (pullSt T N).fst (pullSt T N).snd.fst

abbrev cubP : CubicalStr (Bp T N) (Mp T N) := CubePf.cubical (cm T N) T.M T.cub _ _

end Base

section Pts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

theorem lamPts_w {S : Scheme.{0}} {G Tt : Over S} [GrpObj G] (x y : Tt ⟶ G) (k : Fin 4) :
    lamPts x y k ≫ G.hom = Tt.hom := by
  fin_cases k <;> simp [lamPts]

theorem unit_hom (S : Scheme.{0}) : (𝟙_ (Over S)).hom = 𝟙 S := rfl

end Pts

section Periods

variable (W : Type) [CommRing W] [IsDomain W] (N : ℕ)

end Periods

section Charts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)


end Charts

section Tau

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v := map_mul _ _ _

theorem triple_lift_comp_projections {S : Scheme.{0}} {G Tt : Over S} (x y w : Tt ⟶ G) :
    lift x (lift y w) ≫ x3 G 0 = x ∧ lift x (lift y w) ≫ x3 G 1 = y ∧ lift x (lift y w) ≫ x3 G 2 = w := by
  simp [x3]

theorem alg_step {G : Type} [CommGroup G] {g₁ g₂ v c a b : G} (e : v * c = a * b) :
    g₁ * g₂ * v * c = g₁ * a * (g₂ * b) := by
  rw [mul_assoc (g₁ * g₂), e, _root_.mul_mul_mul_comm]

end Tau

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

end Main

end GlobalTheory.PolDeg.TautEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.PinchLift

open TopologicalSpace

theorem sec_eq_of_germ {X : Scheme.{0}} {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ x (hx : x ∈ U), X.presheaf.germ U x hx a = X.presheaf.germ U x hx b) : a = b :=
  TopCat.Presheaf.section_ext X.sheaf U a b h

theorem germ_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (a : Γ(X, U)) :
    X.presheaf.germ V x hx (resG X h a) = X.presheaf.germ U x (h hx) a :=
  X.presheaf.germ_res_apply (homOfLE h) x hx a

theorem epi_toPushforward_of_closedImm {X' Z' : Scheme.{0}} (i' : Z' ⟶ X') [IsClosedImmersion i'] {L' : LB X'}
    (hL : L'.IsLB) : Epi (GlobalTheory.LB.toPushforward L' i') := by
  refine GlobalTheory.QCoh.epi_of_locally_app_surjective _ fun W x hx => ?_
  obtain ⟨k, hk⟩ := exists_chart hL x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W ⊓ L'.U k from ⟨hx, hk⟩) (W ⊓ L'.U k).2
  have hVW : V ≤ W ⊓ L'.U k := hle
  have hVk : V ≤ L'.U k := hVW.trans inf_le_right
  refine ⟨V, hxV, hVW.trans inf_le_left, fun t => ?_⟩
  have h' : i' ⁻¹ᵁ V ≤ (L'.pull i').U (fun _ => k) := (i'.preimage_mono hVk).trans (GlobalTheory.LB.pull_U i' (fun _ => k)).ge
  obtain ⟨b, hb⟩ := i'.app_surjective V hV
    (GlobalTheory.LB.chartEquiv (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i') (fun _ => k) h' t)
  refine ⟨(GlobalTheory.LB.chartEquiv hL k hVk).symm b, ?_⟩
  apply (GlobalTheory.LB.chartEquiv (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i') (fun _ => k) h').injective
  rw [← hb]
  exact (GlobalTheory.LB.chartEquiv_pullSec i' hL (fun _ => k) hVk h' _).trans
    (congrArg (i'.app V).hom (LinearEquiv.apply_symm_apply _ _))

theorem lift_section_of_closedImm : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  intro X' Z' i' _ L' hL Y' hY τ hτ
  have hL' := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hL i'
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL'
  haveI := epi_toPushforward_of_closedImm i' hL
  have hsurj := GlobalTheory.QCoh.app_surjective_of_epi_of_isAffineOpen (GlobalTheory.LB.toPushforward L' i') hY
  have le1 : ∀ m : (L'.pull i').ι, i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U m ≤ i' ⁻¹ᵁ (L'.U (m PUnit.unit) ⊓ Y') :=
    fun m z hz => ⟨GlobalTheory.LB.pull_U_le i' m hz.2, hz.1⟩
  let c : ∀ m, Γ(Z', i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U m) := fun m => resG Z' (le1 m) (τ (m PUnit.unit))
  have hc : c ∈ secOn (L'.pull i') (i' ⁻¹ᵁ Y') := by
    intro m n
    apply sec_eq_of_germ
    intro z hz
    have hzm : z ∈ i' ⁻¹ᵁ (L'.U (m PUnit.unit) ⊓ Y') := le1 m ⟨hz.1.1, hz.1.2⟩
    have hzn : z ∈ i' ⁻¹ᵁ (L'.U (n PUnit.unit) ⊓ Y') := le1 n ⟨hz.1.1, hz.2⟩
    simp only [c, map_mul, germ_resG]
    rw [hτ (m PUnit.unit) (n PUnit.unit) z hzm hzn]
    congr 1
    have e := GlobalTheory.LB.resG_pull_g (L := L') i' m n (le_refl _)
    rw [GlobalTheory.LB.resG_self] at e
    rw [e, ← GlobalTheory.LB.resG_app, germ_resG]
  obtain ⟨s, hs⟩ := hsurj (GlobalTheory.LB.mkSec c hc)
  have hcoord : ∀ k, (i'.appLE (Y' ⊓ L'.U k) (i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U (fun _ => k))
      (GlobalTheory.LB.pull_inf_le i' Y' (fun _ => k))).hom (GlobalTheory.LB.coord s k) = c (fun _ => k) := fun k => by
    have := congrArg (fun u => GlobalTheory.LB.coord u (fun _ : PUnit => k)) hs
    exact Eq.trans (GlobalTheory.LB.coord_pullSec i' s _).symm this
  refine ⟨fun k => resG X' (le_inf inf_le_right inf_le_left : L'.U k ⊓ Y' ≤ Y' ⊓ L'.U k) (GlobalTheory.LB.coord s k),
    ?_, ?_⟩
  · intro k l x hk hl
    have hx3 : x ∈ Y' ⊓ L'.U k ⊓ L'.U l := ⟨⟨hk.2, hk.1⟩, hl.1⟩
    have e := GlobalTheory.LB.coord_mem s k l
    simp only [germ_resG]
    rw [← germ_resG (inf_le_left : Y' ⊓ L'.U k ⊓ L'.U l ≤ Y' ⊓ L'.U k) x hx3, e, map_mul, germ_resG, germ_resG]
  · intro k
    have h : L'.U k ⊓ Y' ≤ Y' ⊓ L'.U k := le_inf inf_le_right inf_le_left
    apply sec_eq_of_germ
    intro z hz
    have hzB : z ∈ i' ⁻¹ᵁ Y' ⊓ (L'.pull i').U (fun _ => k) :=
      ⟨hz.2, (GlobalTheory.LB.pull_U i' (fun _ => k)).ge hz.1⟩
    have e1 : (i'.app (L'.U k ⊓ Y')).hom (resG X' h (GlobalTheory.LB.coord s k)) =
        (i'.appLE (Y' ⊓ L'.U k) (i' ⁻¹ᵁ (L'.U k ⊓ Y')) (i'.preimage_mono h)).hom (GlobalTheory.LB.coord s k) := by
      rw [← Scheme.Hom.appLE_eq_app, GlobalTheory.LB.appLE_resG]
    show Z'.presheaf.germ _ z hz ((i'.app (L'.U k ⊓ Y')).hom (resG X' h (GlobalTheory.LB.coord s k))) = _
    rw [e1, ← GlobalTheory.LB.resG_app, germ_resG,
      ← germ_resG (GlobalTheory.LB.pull_inf_le i' Y' (fun _ => k)) z hzB, GlobalTheory.LB.resG_app, hcoord k]
    simp only [c, germ_resG]

end GlobalTheory.PinchLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_lineBundle_section_of_closedImmersion_affineOpen : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  first | exact @GlobalTheory.PinchLift.lift_section_of_closedImm | exact GlobalTheory.PinchLift.lift_section_of_closedImm | (intros; apply GlobalTheory.PinchLift.lift_section_of_closedImm <;> assumption)
end
end
