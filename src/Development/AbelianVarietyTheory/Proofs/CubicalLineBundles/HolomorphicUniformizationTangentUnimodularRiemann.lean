module

public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByM
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PowObjSmoothOfRelativeDimensionMul
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RelAmplePowObjBoxLB

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.AnyUnif

theorem injective_of_ker_le_discrete {g g' : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ z, F z = 0 → z ∈ Λ) : Function.Injective F := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  let c : ℂ → Λ := fun t => ⟨t • z, h _ (by rw [map_smul, hz, smul_zero])⟩
  have hc : Continuous c := Continuous.subtype_mk (by fun_prop) _
  have e : c 1 = c 0 := (IsLocallyConstant.iff_continuous c).2 hc |>.apply_eq_of_preconnectedSpace 1 0
  simpa [c] using congrArg Subtype.val e

theorem lbIso_pow_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) :
    LBIso (lbPow (L.pull (𝟙 X)) n) (lbPow L n) := by
  obtain ⟨w, hw⟩ : LBIso (L.pull (𝟙 X)) L :=
    LBIso.chartPull (chartPullPull L (𝟙 X) (𝟙 X) rfl) (chartPullId L) (PolBaseChange.lbIso_refl hL)
  exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩

theorem tangent_and_unimodular : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g),
    (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    ∀ (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
      ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧
        Function.Bijective Ef := by
  intro hU P u
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u', Hm', χ', Ef', hA', -, h1, h2, -, -, hE, hB, -⟩ := hU P rig hrig
  obtain ⟨F, hF₀, -⟩ := HomLinear.exists_linear_of_isMonHom P.A P.A P.isAb P.isAb P.L P.L P.g P.g u u' h1 h2
    (𝟙 P.A) inferInstance
  have hF : ∀ z, u'.ex (F z) = u.ex z := fun z => (hF₀ z).trans (Category.comp_id _)
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by rw [← u'.ker, hF, u.ker]
  haveI := u.discrete
  have hinj := injective_of_ker_le_discrete u.Λ F fun z hz => (hΛ z).1 (hz ▸ u'.Λ.zero_mem)
  let e := LinearEquiv.ofInjectiveEndo F hinj
  have he : ∀ z, e z = F z := fun _ => rfl
  have hd : ∀ w v, IsTangent v → (u.IsDiff w v ↔ u'.IsDiff (e w) v) := fun w v hv => by
    constructor
    · intro h
      simpa [he] using HomLinear.isDiff_comp u u' (𝟙 P.A) F hF₀ hv h
    · intro h
      simpa using HomLinear.isDiff_comp u' u (𝟙 P.A) e.symm.toLinearMap
        (fun z => by rw [Category.comp_id, ← hF, ← he]; simp) hv h
  refine ⟨fun v hv => ?_, fun w => ?_, fun Hm χ hA => ?_⟩
  · obtain ⟨w, hw, hu⟩ := h1 v hv
    refine ⟨e.symm w, (hd _ v hv).2 (by simpa using hw), fun w' hw' => ?_⟩
    rw [← hu _ ((hd _ v hv).1 hw'), e.symm_apply_apply]
  · obtain ⟨v, ⟨hv, hw⟩, hu⟩ := h2 (e w)
    exact ⟨v, ⟨hv, (hd w v hv).2 hw⟩, fun v' hv' => hu v' ⟨hv'.1, (hd w v' hv'.1).1 hv'.2⟩⟩
  · have hH := hermForm_pull_eq_of_lbIso_pow P.A P.A P.L P.L P.isLB P.isLB P.g P.g u u' Hm χ Hm' χ' hA hA'
      (𝟙 P.A) F hF₀ 1 1 (lbIso_pow_pull_id P.isLB 1)
    simp only [Nat.cast_one, _root_.one_mul] at hH
    let l : u.Λ ≃ₗ[ℤ] u'.Λ :=
      { toFun := fun a => ⟨e a, (hΛ a).2 a.2⟩
        invFun := fun b => ⟨e.symm b, (hΛ _).1 (by rw [← he, e.apply_symm_apply]; exact b.2)⟩
        map_add' := fun a b => Subtype.ext (map_add e _ _)
        map_smul' := fun n a => Subtype.ext (map_zsmul e n _)
        left_inv := fun a => Subtype.ext (e.symm_apply_apply _)
        right_inv := fun b => Subtype.ext (e.apply_symm_apply _) }
    refine ⟨Ef'.comp l.toLinearMap l.toLinearMap, fun a b => ?_, ?_⟩
    · rw [← hH]
      exact hE (l a) (l b)
    · exact l.dualMap.bijective.comp (hB.comp l.bijective)

end GlobalTheory.AnyUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace PolFibre

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMapR_id : Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem spMap_dual_hom (f : R →+* R') : spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso (L.pull φ) M) (ψ : Z ⟶ Y) :
    LBIso (L.pull (ψ ≫ φ)) (M.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (chartPullPull M ψ ψ rfl) h

theorem refl (P : Out.PolAV (Sp R)) : IsPolFibre (RingHom.id R) P P (𝟙 _) :=
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  ⟨rfl, (isGrpPullback_of_iso (Iso.refl P.A)).congr (Spec.map_id (CommRingCat.of R)).symm rfl,
    LBIso.chartPull (chartPullPull P.L _ (𝟙 _) rfl) (chartPullId P.L) (PolBaseChange.lbIso_refl P.isLB)⟩

theorem vec_refl {A : Over (Sp R)} (v : epsR R ⟶ A) : IsVecOver (RingHom.id R) (𝟙 _) v v := by
  unfold IsVecOver
  rw [dualMapR_id, Category.comp_id]
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of (DualNumber R))).symm)

variable {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')}
  {φ : P'.A.left ⟶ P.A.left}

theorem comp (h : IsPolFibre f P P' φ) {ψ : P''.A.left ⟶ P'.A.left} (h' : IsPolFibre g P' P'' ψ) :
    IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap f g) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem cancel (h : IsPolFibre f P P' φ) {χ : P''.A.left ⟶ P.A.left} (h' : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ := by
  have n := h'.2.1.congr (spMap_comp_spMap f g).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := h.2.1.1.lift_fst _ _ w
  have e₂ := h.2.1.1.lift_snd _ _ w
  generalize h.2.1.1.lift _ _ w = ψ at e₁ e₂
  subst e₁
  exact ⟨ψ, ⟨h'.1.trans h.1.symm, h.2.1.cancel n e₂,
    LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ).symm h'.2.2⟩, rfl⟩

theorem vec_iff {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')} {φ : A'.left ⟶ A.left}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    {v'' : epsR R'' ⟶ A''} (w : ψ ≫ A'.hom = A''.hom ≫ spMap g) (h : IsVecOver f φ v v') :
    IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  have e : (spMap (Chart.dualMapR g) ≫ v'.left) ≫ φ = spMap (Chart.dualMapR (g.comp f)) ≫ v.left := by
    rw [Category.assoc, h, ← Category.assoc, ← dualMapR_comp]
    exact congrArg (· ≫ v.left) (spMap_comp_spMap _ _)
  refine ⟨fun h' => ?_, fun h' => hφ.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) h').trans e)
  · exact (Category.assoc _ _ _).trans (Eq.trans h' e.symm)
  · rw [Category.assoc, Category.assoc, w, Over.w v', ← Category.assoc, Over.w v'']
    exact (spMap_dual_hom g).symm

end PolFibre

theorem polFibre_id_comp_cancel : (∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), IsPolFibre (RingHom.id R) P P (𝟙 _) ∧ IsVecOver (RingHom.id R) (𝟙 _) v v) ∧ ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') (P : Out.PolAV (Sp R)) (P' : Out.PolAV (Sp R')) (P'' : Out.PolAV (Sp R'')) (φ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' φ → (∀ ψ : P''.A.left ⟶ P'.A.left, IsPolFibre g P' P'' ψ → IsPolFibre (g.comp f) P P'' (ψ ≫ φ)) ∧ (∀ χ : P''.A.left ⟶ P.A.left, IsPolFibre (g.comp f) P P'' χ → ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ) ∧ ∀ (ψ : P''.A.left ⟶ P'.A.left) (v : epsR R ⟶ P.A) (v' : epsR R' ⟶ P'.A) (v'' : epsR R'' ⟶ P''.A), ψ ≫ P'.A.hom = P''.A.hom ≫ spMap g → IsVecOver f φ v v' → (IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'') :=
  ⟨fun _ _ P v => ⟨PolFibre.refl P, PolFibre.vec_refl v⟩, fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun _ h' => PolFibre.comp h h', fun _ h' => PolFibre.cancel h h',
      fun _ _ _ _ w hv => PolFibre.vec_iff h.2.1.1 w hv⟩⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff_comp (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x = Chart.spMap (Chart.scaleD a) ≫ v := by
  rw [Chart.isLieComb_iff]
  simp [Chart.prodPts]

theorem isLieComb_one_iff (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left := by
  rw [isLieComb_one_iff_comp]
  exact ⟨fun h => by rw [h]; rfl, fun h => Over.OverMorphism.ext h⟩

theorem scale_add {v : epsR R ⟶ G} (hv : IsTangent v) (a b : R) :
    Chart.spMap (Chart.scaleD (a + b)) ≫ v =
      (Chart.spMap (Chart.scaleD a) ≫ v) * (Chart.spMap (Chart.scaleD b) ≫ v) := by
  rw [SqZero.scaleD_eq, SqZero.scaleD_eq, SqZero.scaleD_eq,
    ← SqZero.epsTo_add_comp ((Chart.isTan_iff _).2 hv) _ _ _ _ (TrivSqZeroExt.inr_mul_inr _ _ _)
      (by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
  congr 3
  exact TrivSqZeroExt.inr_add _ _ _

theorem scaleD_comp (a b : R) : (Chart.scaleD a).comp (Chart.scaleD b) = Chart.scaleD (a * b) := by
  rw [SqZero.scaleD_eq a, SqZero.epsTo_comp_scaleD, SqZero.scaleD_eq]
  congr 1
  rw [← TrivSqZeroExt.inr_smul, smul_eq_mul, _root_.mul_comm]

theorem scaleD_one : Chart.scaleD (1 : R) = AlgHom.id R _ :=
  DualNumber.algHom_ext (by rw [SqZero.scaleD_eq, SqZero.epsTo_eps]; rfl)

theorem lieMultiple_calculus : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (v x y : epsR R ⟶ G) (a b : R), (IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left) ∧ (IsTangent v → IsLieComb ![a] ![v] x → IsLieComb ![b] ![v] y → IsLieComb ![a + b] ![v] (x * y)) ∧ (IsLieComb ![b] ![v] x → IsLieComb ![a] ![x] y → IsLieComb ![a * b] ![v] y) ∧ (∀ f : G ⟶ G', IsLieComb ![a] ![v] x → IsLieComb ![a] ![v ≫ f] (x ≫ f)) ∧ IsLieComb ![1] ![v] v ∧ (IsTangent v → IsLieComb ![0] ![v] 1) := by
  intro R _ G G' _ _ v x y a b
  refine ⟨isLieComb_one_iff a v x, fun hv hx hy => ?_, fun hx hy => ?_, fun f hx => ?_, ?_, fun hv => ?_⟩
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hx, hy]
    exact (scale_add hv a b).symm
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hy, hx, ← scaleD_comp, ← Chart.spMap_comp]
    exact (Category.assoc _ _ _).symm
  · rw [isLieComb_one_iff_comp] at hx ⊢
    rw [hx]
    exact Category.assoc _ _ _
  · rw [isLieComb_one_iff_comp, scaleD_one, Chart.spMap_id]
    exact (Category.id_comp _).symm
  · rw [isLieComb_one_iff_comp, SqZero.scaleD_eq]
    exact (SqZero.epsTo_zero_comp ((Chart.isTan_iff _).2 hv) _ (TrivSqZeroExt.inr_zero _) _).symm

end GlobalTheory.LieMultiple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane nonZeroDivisors

namespace GlobalTheory

namespace CMData

variable {K : Type} [Field K] [NumberField K]

theorem exists_periodPair (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ x ∈ I.1, z = σ x := by
  obtain ⟨b, hspan⟩ : ∃ b : Module.Basis (Fin 2) ℚ K, ∀ x : K, x ∈ I.1 ↔ x ∈ Submodule.span ℤ (Set.range b) := by
    have hcard := (Module.finrank_eq_card_basis (basisOfFractionalIdeal K I)).symm.trans h2
    refine ⟨(basisOfFractionalIdeal K I).reindex (Fintype.equivFinOfCardEq hcard), fun x => ?_⟩
    rw [Module.Basis.coe_reindex, EquivLike.range_comp, mem_span_basisOfFractionalIdeal]
    exact Iff.rfl
  obtain ⟨a, ha⟩ := CMLattice.exists_im_ne_zero σ hσ
  have hX : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im ≠ 0 := by
    intro h0
    have e := CMLattice.im_mul_conj_eq_det σ b ![1, (a : K)]
    rw [h0, mul_zero] at e
    apply ha
    simpa using e
  have e2 : (σ (b 0) * starRingEnd ℂ (σ (b 1))).im =
      (σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hind : LinearIndependent ℝ ![σ (b 0), σ (b 1)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have e1 := congrArg (fun w => (starRingEnd ℂ (σ (b 0)) * w).im) hst
      simp only [Complex.real_smul, mul_add, Complex.add_im, Complex.mul_im, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, mul_zero,
        Complex.zero_im] at e1
      have hprod : t * ((σ (b 0)).im * (σ (b 1)).re - (σ (b 0)).re * (σ (b 1)).im) = 0 := by
        linear_combination -e1
      rcases mul_eq_zero.mp hprod with h | h
      · exact h
      · exact absurd (e2.trans h) hX
    subst ht
    have h0 : σ (b 0) ≠ 0 := by
      intro h
      apply hX
      rw [h, zero_mul, Complex.zero_im]
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right h0, rfl⟩
  refine ⟨⟨σ (b 0), σ (b 1), hind⟩, fun z => ?_⟩
  show z ∈ Submodule.span ℤ {σ (b 0), σ (b 1)} ↔ _
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m • b 0 + n • b 1, ?_, by simp⟩
    rw [hspan]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rintro ⟨x, hx, rfl⟩
    rw [hspan, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c 0, c 1, ?_⟩
    simp [Fin.sum_univ_two]

theorem exists_mul_of_invariants {L L' : PeriodPair} {c₄ Δ : ℂ}
    (h : c₄ ^ 3 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = 1728 * L.g₂ ^ 3 * Δ)
    (h₄ : c₄ = 12 * L'.g₂) (hΔ : Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ w ∈ L.lattice, z = c * w := by
  subst h₄ hΔ
  exact (lattice_determined_by_invariants L L').2 (by linear_combination (-1 / 1728 : ℂ) * h)

theorem exists_field (h2 : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ a, σ a ∈ M) ∧
      ∀ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ W : WeierstrassCurve (𝓞 M), IsUnit W.Δ ∧
        ∀ L' : PeriodPair,
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.c₄ = 12 * L'.g₂ →
          ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) W.Δ = L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 →
          ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ I.1, z = c * σ x := by
  obtain ⟨M, hfin, hσM, hF⟩ := exists_field_cm_curves_unit_discriminant K h2 σ hσ
  refine ⟨M, hfin, hσM, fun I => ?_⟩
  obtain ⟨L, hL⟩ := exists_periodPair h2 σ hσ I
  have hstab : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice := by
    intro a z hz
    obtain ⟨x, hx, rfl⟩ := (hL z).1 hz
    refine (hL _).2 ⟨(a : K) * x, ?_, by rw [map_mul]⟩
    have hax := Submodule.smul_mem (I.1 : Submodule (𝓞 K) K) a hx
    simpa [Algebra.smul_def] using hax
  obtain ⟨W, hW, hj⟩ := hF L hstab
  refine ⟨W, hW, fun L' h4 hD => ?_⟩
  obtain ⟨c, hc, hc'⟩ := exists_mul_of_invariants hj h4 hD
  refine ⟨c, hc, fun z => ?_⟩
  rw [hc' z]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hL w).1 hw
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨σ x, (hL _).2 ⟨x, hx, rfl⟩, rfl⟩

theorem mem_inv_iff (𝔟 : (Ideal (𝓞 K))⁰) (x : K) :
    x ∈ ((FractionalIdeal.mk0 K 𝔟)⁻¹).1 ↔ ∀ b ∈ (𝔟 : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K)) := by
  have hne : ((FractionalIdeal.mk0 K 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, FractionalIdeal.mem_inv_iff hne, FractionalIdeal.coe_mk0]
  constructor
  · intro h b hb
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩))
    have hint : IsIntegral ℤ (algebraMap (𝓞 K) K a) := RingOfIntegers.isIntegral_coe a
    rw [ha] at hint
    exact hint
  · intro h y hy
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, h b hb⟩, rfl⟩

end CMData

open CMData in
theorem exists_cm_curves_of_weierstrass_curves :
    (∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) ∧ ∀ s : R →+* ℂ, s W.c₄ = 12 * (Lf s).g₂ ∧ s W.c₆ = 216 * (Lf s).g₃ ∧ s W.Δ = (Lf s).g₂ ^ 3 - 27 * (Lf s).g₃ ^ 2) → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (κ : K →+* M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (L₀ : (𝓞 M →+* ℂ) → PeriodPair) (Q : ClassGroup (𝓞 K) → Out.PolAV (Sp (𝓞 M))) (t : ∀ C, epsR (𝓞 M) ⟶ (Q C).A) (L : ClassGroup (𝓞 K) → (𝓞 M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ), (∀ a, (κ a : ℂ) = σ₀ a) ∧ (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L₀ s').lattice ↔ z • w' ∈ u'.Λ)) ∧ (∀ C, ((Q C).g = 1 ∧ IsLieBasis ![(t C)] ∧ (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' (Q C) P' φ' → IsVecOver f' φ' (t C) v' → IsLieBasis ![v']) ∧ ∀ s' : (𝓞 M) →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ (Q C).A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' (Q C) P' φ' → IsVecOver s' φ' (t C) v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (L C s').lattice ↔ z • w' ∈ u'.Λ))) ∧ (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s (δ C : 𝓞 M)) ∧ (∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔ ∃ a : 𝓞 K, z = c * σ₀ (a : K)) ∧ ∃ β : ClassGroup (𝓞 K) → ℂ, (∀ C, β C ≠ 0) ∧ (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → ∀ z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, β C * σ₀ x * z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice) ∧ ∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), ∀ z ∈ (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice, (β C)⁻¹ * σ₀ (y : K) * z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice := by
  intro H K _ _ h2 σ₀ hσ₀ 𝔟
  obtain ⟨M, hfin, hσM, hF⟩ := CMData.exists_field h2 σ₀ hσ₀
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  obtain ⟨W₀, hW₀, hF₀⟩ := hF 1
  obtain ⟨P, v, L₀, hP, hP₀⟩ := H (𝓞 M) W₀ hW₀
  obtain ⟨c₀, hc₀, hc₀L⟩ := hF₀ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hP₀ _).1 (hP₀ _).2.2
  have hL0 : ∀ z, z ∈ (L₀ ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))).lattice ↔
      ∃ a : 𝓞 K, z = c₀ * σ₀ (a : K) := by
    intro z
    rw [hc₀L z, Units.val_one]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K), (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩, rfl⟩
  choose W hW hWL using fun C : ClassGroup (𝓞 K) => hF (FractionalIdeal.mk0 K (𝔟 C))⁻¹
  choose Q t L hQ hQL using fun C => H (𝓞 M) (W C) (hW C)
  choose c hc hcL using fun C => hWL C (L C ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)))
    (hQL C _).1 (hQL C _).2.2
  refine ⟨M, hNF, σ₀.codRestrict M hσM, P, v, L₀, Q, t, L, fun C => (hW C).unit, fun a => rfl, hP, hQ,
    fun C s => ?_, ⟨c₀, hc₀, hL0⟩, fun C => c C / c₀, fun C => div_ne_zero (hc C) hc₀, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact ((hQL C s).2.2).symm
  · intro C x hx z hz
    obtain ⟨a, rfl⟩ := (hL0 z).1 hz
    have hxI := (CMData.mem_inv_iff (𝔟 C) x).2 hx
    rw [hcL C]
    refine ⟨x * (a : K), ?_, ?_⟩
    · have hax := Submodule.smul_mem (((FractionalIdeal.mk0 K (𝔟 C))⁻¹).1 : Submodule (𝓞 K) K) a hxI
      simpa [Algebra.smul_def, mul_comm] using hax
    · rw [map_mul]
      field_simp
  · intro C y hy z hz
    obtain ⟨x', hx', rfl⟩ := (hcL C z).1 hz
    have hint := (CMData.mem_inv_iff (𝔟 C) x').1 hx' y hy
    rw [hL0]
    refine ⟨⟨x' * (y : K), hint⟩, ?_⟩
    show _ = c₀ * σ₀ (x' * (y : K))
    have hcC := hc C
    rw [map_mul]
    field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory

namespace IsogenyModel

private theorem over_pullback_map_left_fst {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.fst X.hom φ = pullback.fst _ _ ≫ io.left :=
  pullback.lift_fst _ _ _

private theorem over_pullback_map_left_snd {S S' : Scheme} (φ : S' ⟶ S) (Ga X : Over S) (io : Ga ⟶ X) :
    ((Over.pullback φ).map io).left ≫ pullback.snd X.hom φ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

theorem _root_.GlobalTheory.IsogenyModel.exists_flat_closure (T K : Type) [CommRing T] [IsDedekindDomain T] [Field K] [Algebra T K]
    [IsFractionRing T K] (X : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (Z : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K))
    (i : Z ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj X) (hi : IsClosedImmersion i.left) :
    ∃ (Ga : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp T)) (io : Ga ⟶ X)
      (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).obj Ga ≅ Z), IsClosedImmersion io.left ∧
      Flat Ga.hom ∧ e.hom ≫ i = (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))).map io := by
  haveI := hi
  haveI : Flat (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.flat_specMap_localization (nonZeroDivisors T) K
  haveI : Mono (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := _root_.GlobalTheory.mono_specMap_localization (nonZeroDivisors T) K
  set u := pullback.fst X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) with hu
  set j := i.left ≫ u with hj
  have hjs : Z.hom ≫ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = j ≫ X.hom := by
    rw [hj, Category.assoc, hu, pullback.condition, ← Category.assoc]
    congr 1
    exact (Over.w i).symm
  haveI : QuasiCompact (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := by dsimp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]; infer_instance
  haveI : QuasiCompact j := by rw [hj, hu]; infer_instance
  have hflat : Flat (j.imageι ≫ X.hom) :=
    _root_.GlobalTheory.flat_image_of_over_fractionField j X.hom Z.hom hjs
  have hA : IsPullback i.left j.toImage u j.imageι :=
    _root_.GlobalTheory.isPullback_toImage_of_isClosedImmersion j i.left u rfl
  have hB : IsPullback u (pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) := IsPullback.of_hasPullback X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))
  have hC : IsPullback j.toImage (i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K))) (j.imageι ≫ X.hom) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) :=
    IsPullback.paste_vert hA.flip hB
  have hZ : i.left ≫ pullback.snd X.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap T K)) = Z.hom := Over.w i
  rw [hZ] at hC
  refine ⟨Over.mk (j.imageι ≫ X.hom), Over.homMk j.imageι rfl,
    Over.isoMk hC.isoPullback.symm (by simp), (show IsClosedImmersion j.imageι from inferInstance), hflat, ?_⟩
  ext1
  simp only [Over.comp_left, Over.isoMk_hom_left, Iso.symm_hom]
  rw [Iso.inv_comp_eq]
  apply pullback.hom_ext
  · rw [Category.assoc, over_pullback_map_left_fst]
    erw [hC.isoPullback_hom_fst_assoc]
    simp [hj, hu]
  · rw [Category.assoc, over_pullback_map_left_snd]
    erw [hC.isoPullback_hom_snd]
    exact hZ

variable {S : Scheme.{0}}

theorem _root_.GlobalTheory.IsogenyModel.exists_kernel {G B : Over S} [GrpObj G] [GrpObj B] [IsSeparated B.hom] (f : G ⟶ B)
    [IsMonHom f] [IsFinite f.left] :
    ∃ (Z : Over S) (_ : GrpObj Z) (i : Z ⟶ G), IsMonHom i ∧ IsClosedImmersion i.left ∧
      IsFinite Z.hom ∧ IsPullback i (toUnit Z) f η[B] := by
  have hP := IsPullback.of_hasPullback f η[B]
  have hL := IsPullback.map (Over.forget S) hP
  haveI : IsClosedImmersion η[B].left :=
    _root_.GlobalTheory.Retract.isClosedImmersion_section (f := 𝟙 S) (r := B.hom) (Over.w η[B])
      (Category.comp_id _)
  haveI : Mono η[B] := ⟨fun a b _ => toUnit_unique a b⟩
  set i := pullback.fst f η[B] with hi
  have key : ∀ {X : Over S} (a : X ⟶ pullback f η[B]), (a ≫ i) ≫ f = 1 := fun a => by
    rw [Category.assoc, hi, pullback.condition, ← Category.assoc,
      toUnit_unique (a ≫ pullback.snd f η[B]) (toUnit _), ← Hom.one_def]
  have key1 : i ≫ f = 1 := by simpa using key (𝟙 _)
  have hinv : ∀ {X : Over S} (a : X ⟶ G), a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro X a
    exact GrpObj.inv_comp a f
  obtain ⟨inst, hmon⟩ := _root_.GlobalTheory.exists_grpObj_of_mono i
    (pullback.lift η[G] (𝟙 _) (by simp))
    (pullback.lift ((fst _ _ ≫ i) * (snd _ _ ≫ i)) (toUnit _)
      (by rw [mul_comp, key, key, _root_.mul_one, Hom.one_def]))
    (pullback.lift i⁻¹ (toUnit _) (by rw [hinv, key1, _root_.inv_one, Hom.one_def]))
    (pullback.lift_fst _ _ _)
    (by rw [pullback.lift_fst, Hom.mul_def, lift_fst_comp_snd_comp])
    (by rw [pullback.lift_fst, Hom.inv_def])
  refine ⟨pullback f η[B], inst, i, hmon, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) hL.flip (show IsClosedImmersion η[B].left from inferInstance)
  · have hw := Over.w (pullback.snd f η[B])
    have : IsFinite (pullback.snd f η[B]).left :=
      MorphismProperty.of_isPullback (P := @IsFinite) hL (show IsFinite f.left from inferInstance)
    rw [← hw]
    simpa using this
  · simpa [toUnit_unique (pullback.snd f η[B]) (toUnit _)] using hP

theorem _root_.GlobalTheory.IsogenyModel.exists_iso_of_same_kernel {G A B Z : Over S} [GrpObj G] [GrpObj A] [GrpObj B]
    (q : G ⟶ A) (f : G ⟶ B) (i : Z ⟶ G) [IsMonHom q] [IsMonHom f] [Flat q.left]
    [Surjective q.left] [QuasiCompact q.left] [Surjective f.left] [IsProper A.hom]
    [IsSeparated B.hom] [IsReduced B.left] (hq : IsPullback i (toUnit Z) q η[A])
    (hf : IsPullback i (toUnit Z) f η[B]) :
    ∃ e : A ≅ B, IsMonHom e.hom ∧ q ≫ e.hom = f := by
  obtain ⟨β, hβ, hqβ⟩ := _root_.GlobalTheory.FlatQuotient.exists_desc q i f hq hf.w
  have htriv : ∀ {X : Over S} (x : X ⟶ A), x ≫ β = 1 → x = 1 := by
    intro X x hx
    have hP := IsPullback.of_hasPullback x q
    have hL := IsPullback.map (Over.forget S) hP
    haveI : Flat (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Flat) hL.flip (show Flat q.left from inferInstance)
    haveI : Surjective (pullback.fst x q).left :=
      MorphismProperty.of_isPullback (P := @Surjective) hL.flip
        (show Surjective q.left from inferInstance)
    haveI : Epi (pullback.fst x q) := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective _
    have hg : pullback.snd x q ≫ f = toUnit _ ≫ η[B] := by
      rw [← hqβ, ← Category.assoc, ← pullback.condition, Category.assoc, hx, Hom.one_def,
        ← Category.assoc, toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
    have hgq : pullback.snd x q ≫ q = toUnit _ ≫ η[A] := by
      rw [← hf.lift_fst _ _ hg, Category.assoc, hq.w, ← Category.assoc,
        toUnit_unique (hf.lift _ _ hg ≫ toUnit Z) (toUnit _)]
    rw [← cancel_epi (pullback.fst x q), pullback.condition, hgq, Hom.one_def, ← Category.assoc,
      toUnit_unique (pullback.fst x q ≫ toUnit X) (toUnit _)]
  haveI : Mono β := ⟨fun a b hab => by
    have h1 : (a * b⁻¹) ≫ β = 1 := by
      rw [mul_comp, GrpObj.inv_comp, hab, _root_.mul_inv_cancel]
    have h2 := htriv _ h1
    exact (mul_inv_eq_one.mp h2)⟩
  haveI : Surjective (q.left ≫ β.left) := by
    rw [← Over.comp_left, hqβ]; infer_instance
  haveI : Surjective β.left := Surjective.of_comp q.left β.left
  haveI : IsProper (β.left ≫ B.hom) := by rw [Over.w β]; infer_instance
  haveI : IsProper β.left := IsProper.of_comp β.left B.hom
  haveI : IsClosedImmersion β.left :=
    (IsClosedImmersion.iff_isProper_and_mono (f := β.left)).mpr ⟨inferInstance, inferInstance⟩
  haveI : IsIso β.left := isIso_of_isClosedImmersion_of_surjective β.left
  refine ⟨Over.isoMk (asIso β.left) (Over.w β), ?_, ?_⟩
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hβ
  · have : (Over.isoMk (asIso β.left) (Over.w β)).hom = β := by ext1; rfl
    rw [this]; exact hqβ

end IsogenyModel

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ExtendLineBundle

noncomputable section

namespace GlobalTheory.GenericFibreExtend

theorem exists_specializes_of_mem_closure {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] {O F : Set X} (hO : IsOpen O) (hF : IsClosed F) {y : X}
    (hy : y ∈ closure (O ∩ F)) : ∃ z ∈ O ∩ F, z ⤳ y := by
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  have h1 : O ∩ F ⊆ ⋃ s ∈ {s ∈ S | (s ∩ O).Nonempty}, s := by
    rintro x ⟨hxO, hxF⟩
    rw [hU] at hxF
    obtain ⟨s, hs, hx⟩ := hxF
    exact Set.mem_biUnion (show s ∈ {s ∈ S | (s ∩ O).Nonempty} from ⟨hs, x, hx, hxO⟩) hx
  have h2 : IsClosed (⋃ s ∈ {s ∈ S | (s ∩ O).Nonempty}, s) :=
    (hS.subset (Set.sep_subset _ _)).isClosed_biUnion fun s hs => hc s hs.1
  obtain ⟨s, ⟨hs, hsO⟩, hys⟩ := Set.mem_iUnion₂.1 (closure_minimal h1 h2 hy)
  obtain ⟨z, hz⟩ := QuasiSober.sober (hi s hs) (hc s hs)
  refine ⟨z, ⟨(hz.mem_open_set_iff hO).2 hsO, ?_⟩, hz.specializes hys⟩
  rw [hU]
  exact ⟨s, hs, hz.mem⟩

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem exists_equations' (L : LB Y) (hL : L.IsLB) : ∃ f : L.ι → Y.functionFieldˣ,
    ∀ i k, genericPoint Y ∈ L.U i → genericPoint Y ∈ L.U k →
      unitVal _ (L.g i k) = f i / f k := by
  by_cases h : ∃ i₀, genericPoint Y ∈ L.U i₀
  · obtain ⟨i₀, h₀⟩ := h
    refine ⟨fun i => unitVal _ (L.g i i₀), fun i k hi hk => ?_⟩
    have hη : genericPoint Y ∈ L.U i ⊓ L.U k ⊓ L.U i₀ := ⟨⟨hi, hk⟩, h₀⟩
    have e := congrArg (unitVal _) (hL.cocycle i k i₀)
    rw [map_mul, unitVal_res _ hη, unitVal_res _ hη, unitVal_res _ hη] at e
    exact eq_div_iff_mul_eq'.2 e
  · exact ⟨1, fun i _ hi => (h ⟨i, hi⟩).elim⟩

theorem isGen_of_equations' (M N : LB Y) (a : M.ι → Y.functionFieldˣ) (b : N.ι → Y.functionFieldˣ)
    (ha : ∀ i k, genericPoint Y ∈ M.U i → genericPoint Y ∈ M.U k →
      unitVal _ (M.g i k) = a i / a k)
    (hb : ∀ i k, genericPoint Y ∈ N.U i → genericPoint Y ∈ N.U k →
      unitVal _ (N.g i k) = b i / b k)
    (s : ∀ p : M.ι × N.ι, Γ(Y, M.U p.1 ⊓ N.U p.2)ˣ)
    (hs : ∀ p, genericPoint Y ∈ (M.U p.1 ⊓ N.U p.2) → unitVal _ (s p) = a p.1 / b p.2) :
    LB.Gen.IsGen (⟨s⟩ : LB.Iso N M) := by
  intro (p : M.ι × N.ι) (q : M.ι × N.ι)
  refine ExtendLineBundle.unit_ext (U := M.U p.1 ⊓ N.U p.2 ⊓ (M.U q.1 ⊓ N.U q.2)) fun h => ?_
  have hp := h.1
  have hq := h.2
  have e₁ := ha p.1 q.1 hp.1 hq.1
  have e₂ := hb p.2 q.2 hp.2 hq.2
  have key : ∀ (V : Y.Opens) (_ : genericPoint Y ∈ V) (l₁ : V ≤ M.U p.1 ⊓ N.U p.2)
      (l₂ : V ≤ M.U p.1 ⊓ M.U q.1) (l₃ : V ≤ N.U p.2 ⊓ N.U q.2) (l₄ : V ≤ M.U q.1 ⊓ N.U q.2),
      unitVal V (res l₁ (s p)) =
        unitVal V (res l₂ (M.g p.1 q.1) * (res l₃ (N.g p.2 q.2))⁻¹ * res l₄ (s q)) := by
    intro V h l₁ l₂ l₃ l₄
    rw [map_mul, map_mul, map_inv, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h,
      unitVal_res _ h, e₁, e₂, hs p hp, hs q hq]
    rw [inv_div, mul_right_comm, div_mul_div_cancel, div_mul_div_cancel]
  exact key _ h _ _ _ _

variable (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X)

def fieldMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fieldMap_germ {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    fieldMap j hη (X.presheaf.germ U _ h s) = Y.presheaf.germ (j ⁻¹ᵁ U) _ h' (j.app U s) := by
  change j.stalkMap _ (X.presheaf.stalkSpecializes hη (X.presheaf.germ U _ h s)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact Scheme.Hom.germ_stalkMap_apply j U _ _ s

theorem exists_fieldMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : u ∈ localSubring y) : ∃ t ∈ localSubring (j y), fieldMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq b
  refine ⟨_, germ_mem hx (genericPoint_mem hx) s, ?_⟩
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fieldMap_germ j hη _ (genericPoint_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem fieldMap_surjective [IsPreimmersion j] : Function.Surjective (fieldMap j hη) := by
  intro u
  obtain ⟨U, hx, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) u
  obtain ⟨t, -, ht⟩ := exists_fieldMap_eq j hη (germ_mem hx hx s)
  exact ⟨t, ht⟩

theorem fieldMap_mem_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    fieldMap j hη t ∈ localSubring y ↔ t ∈ localSubring (j y) := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fieldMap_eq j hη h
    rwa [← (fieldMap j hη).injective e]
  · intro h
    obtain ⟨U, hx, s, rfl⟩ := exists_section_of_mem h
    have hy : y ∈ j ⁻¹ᵁ U := hx
    rw [fieldMap_germ j hη _ (genericPoint_mem hy)]
    exact germ_mem hy _ _

def unitMap : X.functionFieldˣ →* Y.functionFieldˣ := Units.map (fieldMap j hη).toMonoidHom

theorem unitMap_mem_iff [IsPreimmersion j] {y : Y} {t : X.functionFieldˣ} :
    unitMap j hη t ∈ localUnits y ↔ t ∈ localUnits (j y) := by
  rw [mem_localUnits, mem_localUnits, ← fieldMap_mem_iff j hη, ← fieldMap_mem_iff j hη, map_inv₀]
  rfl

theorem unitMap_surjective [IsPreimmersion j] : Function.Surjective (unitMap j hη) := by
  intro u
  obtain ⟨t, ht⟩ := fieldMap_surjective j hη u
  have h0 : t ≠ 0 := by
    rintro rfl
    exact u.ne_zero (ht.symm.trans (map_zero _))
  exact ⟨Units.mk0 t h0, Units.ext ht⟩

theorem unitVal_pullU {U : X.Opens} (h' : genericPoint Y ∈ j ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    unitVal (j ⁻¹ᵁ U) (pullU j U a) = unitMap j hη (unitVal U a) := by
  have h : genericPoint X ∈ U := genericPoint_mem (x := j (genericPoint Y)) h'
  apply Units.ext
  rw [val_unitVal h']
  change _ = fieldMap j hη (unitVal U a).val
  rw [val_unitVal h, fieldMap_germ j hη h h']
  rfl

theorem unitVal_pull (M : LB X) (p q : PUnit → M.ι)
    (h : genericPoint Y ∈ (LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q)) :
    unitVal _ ((M.pull j).g p q) = unitMap j hη (unitVal _ (M.g (p ⟨⟩) (q ⟨⟩))) := by
  have hle : LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q ≤
      j ⁻¹ᵁ (M.U (p ⟨⟩) ⊓ M.U (q ⟨⟩)) := fun y hy =>
    ⟨LB.wchart_le M (fun _ => j) p ⟨⟩ hy.1, LB.wchart_le M (fun _ => j) q ⟨⟩ hy.2⟩
  have e : (M.pull j).g p q = res hle (pullU j _ (M.g (p ⟨⟩) (q ⟨⟩))) := by
    change (∏ _k : PUnit.{1}, (res hle (pullU j _ (M.g (p _k) (q _k)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e]
  refine (unitVal_res _ h _).trans (unitVal_pullU j hη ?_ _)
  exact ⟨LB.wchart_le M (fun _ => j) p ⟨⟩ h.1, LB.wchart_le M (fun _ => j) q ⟨⟩ h.2⟩

omit [IsIntegral Y] in
theorem isOpen_localUnits (t : X.functionFieldˣ) : IsOpen {x : X | t ∈ localUnits x} := by
  rw [isOpen_iff_eventually]
  intro x hx
  have := mem_localUnits.1 hx
  filter_upwards [eventually_mem this.1, eventually_mem this.2] with y h1 h2
  exact mem_localUnits.2 ⟨h1, h2⟩

end GlobalTheory.GenericFibreExtend

namespace GlobalTheory

open GenericFibreExtend

theorem exists_lineBundle_extension_of_generalizing (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X) [IsPreimmersion j]
    (hj : GeneralizingMap j)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (L : LB Y) (hL : L.IsLB) :
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  have : IsNoetherian X := {}
  have hη : j (genericPoint Y) ⤳ genericPoint X := by
    obtain ⟨y, -, hy⟩ := hj (genericPoint_specializes (j (genericPoint Y)))
    rw [← hy]
    exact (genericPoint_specializes y).map j.continuous
  have : NoetherianSpace Y := j.isEmbedding.isInducing.noetherianSpace
  obtain ⟨f', hf'⟩ := exists_equations' L hL
  choose f hf using fun i => unitMap_surjective j hη (f' i)
  have hfu : ∀ i k y, y ∈ L.U i → y ∈ L.U k → f i / f k ∈ localUnits (j y) := fun i k y hi hk => by
    rw [← unitMap_mem_iff j hη, map_div, hf, hf,
      ← hf' i k (genericPoint_mem hi) (genericPoint_mem hk)]
    exact unitVal_mem (U := L.U i ⊓ L.U k) ⟨hi, hk⟩ _
  choose V hVo hV using fun i => j.isEmbedding.isInducing.isOpen_iff.1 (L.U i).isOpen
  have hV' : ∀ i y, j y ∈ V i ↔ y ∈ L.U i := fun i y => Set.ext_iff.1 (hV i) y
  obtain ⟨ι, hι⟩ := (NoetherianSpace.isCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun i => (L.U i : Set Y)) (fun i => (L.U i).isOpen) (fun y _ => by
      have : y ∈ ⨆ i, L.U i := hL.cover ▸ trivial
      exact Set.mem_iUnion.2 (Opens.mem_iSup.1 this))
  let Z : ι × ι → Set X := fun p => (V p.1 ∩ V p.2) ∩ {x : X | f p.1 / f p.2 ∈ localUnits x}ᶜ
  let W : Set X := ⋂ p, (closure (Z p))ᶜ
  have hWo : IsOpen W := isOpen_iInter_of_finite fun p => isClosed_closure.isOpen_compl
  have hW : ∀ y, j y ∈ W := fun y => Set.mem_iInter.2 fun p hp => by
    obtain ⟨z, hz, hzy⟩ := exists_specializes_of_mem_closure ((hVo _).inter (hVo _))
      (isOpen_localUnits _).isClosed_compl hp
    obtain ⟨y', -, rfl⟩ := hj hzy
    exact hz.2 (hfu _ _ y' ((hV' _ _).1 hz.1.1) ((hV' _ _).1 hz.1.2))
  obtain ⟨T, h₀, hT, hc⟩ := exists_compatible_cover hX
    (T₀ := Set.range fun i : ι => ((⟨V i ∩ W, (hVo i).inter hWo⟩ : X.Opens), f i)) (by
      rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ x hi hk
      by_contra h
      exact Set.mem_iInter.1 hi.2 (i, k) (subset_closure ⟨⟨hi.1, hk.1⟩, h⟩))
  choose g hg using fun p q : T => exists_unit (U := p.1.1 ⊓ q.1.1) (t := p.1.2 / q.1.2)
    fun y hy => hT _ p.2 _ q.2 y hy.1 hy.2
  let L' : LB X := ⟨T, fun p => p.1.1, g⟩
  choose s hs using fun p : L.ι × (PUnit → T) => exists_unit
    (U := L.U p.1 ⊓ LB.wchart L' (fun _ => j) p.2)
    (t := f' p.1 / unitMap j hη (p.2 ⟨⟩).1.2) fun y hy => by
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (hι (Set.mem_univ y))
      rw [← hf, ← map_div, unitMap_mem_iff]
      have := mul_mem (hfu p.1 i y hy.1 hyi) (hT _ (h₀ ⟨⟨i, hi⟩, rfl⟩) _ (p.2 ⟨⟩).2 (j y)
        ⟨(hV' _ _).2 hyi, hW y⟩ (LB.wchart_le L' (fun _ => j) p.2 ⟨⟩ hy.2))
      rwa [div_mul_div_cancel] at this
  refine ⟨L', ⟨?_, fun p => ExtendLineBundle.unit_ext fun h => ?_,
    fun p q r => ExtendLineBundle.unit_ext fun h => ?_⟩,
    ⟨s⟩, isGen_of_equations' L (L'.pull j) f' (fun p => unitMap j hη (p ⟨⟩).1.2) hf'
      (fun p q hp hq => ?_) s hs⟩
  · refine top_unique fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := hc x
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hx⟩
  · rw [unitVal_res _ h, map_one]
    exact (hg p p ⟨h, h⟩).trans (div_self' _)
  · rw [map_mul, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h]
    exact (congrArg₂ (· * ·) (hg p q h.1) (hg q r ⟨h.1.2, h.2⟩)).trans
      ((div_mul_div_cancel _ _ _).trans (hg p r ⟨h.1.1, h.2⟩).symm)
  · refine (unitVal_pull j hη L' p q ⟨hp, hq⟩).trans ?_
    rw [← map_div]
    refine congrArg _ (hg (p ⟨⟩) (q ⟨⟩) (genericPoint_mem (x := j (genericPoint Y)) ?_))
    exact ⟨LB.wchart_le L' (fun _ => j) p ⟨⟩ hp, LB.wchart_le L' (fun _ => j) q ⟨⟩ hq⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CM

theorem exists_polAV_isPowGrp : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (n : ℕ), ∃ (Q : Out.PolAV (Sp R)) (_ : Out.IsPowGrp Q.A P.A n), Q.g = n * P.g := by
  intro R _ P n
  have := P.isAb.comm
  obtain ⟨hL, hS, hr⟩ := BoxPower.boxPower_basic R P n
  obtain ⟨rig, hrig⟩ := P.rigid
  exact ⟨{ A := Out.powObj P.A n
           isAb := (PowGrp.powers _ _ _ n (Out.powIsPowGrp P.A n)).2.2.2.1 P.isAb
           g := n * P.g
           smoothDim := powObj_smoothOfRelativeDimension_mul _ _ _ n P.smoothDim
           L := Out.boxLB P.L (Out.powPr P.A (n := n))
           isLB := hL
           rigid := ⟨_, hr rig hrig⟩
           sym := hS
           ample := relAmple_powObj_boxLB R P n
           ktriv := kTriv_boxLB _ (Out.powObj P.A n) P.A n (Out.powIsPowGrp P.A n) P.L P.isLB P.ktriv },
    Out.powIsPowGrp P.A n, rfl⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensorFinite

variable {S : Scheme.{0}}

set_option autoImplicit false in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.TensorFinite.isFinite_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y') (hf : IsFinite f.left)
    (hg : IsFinite g.left) : IsFinite (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsFinite) hf hg (Over.w f).symm (Over.w g).symm

end GlobalTheory.TensorFinite
end
end
