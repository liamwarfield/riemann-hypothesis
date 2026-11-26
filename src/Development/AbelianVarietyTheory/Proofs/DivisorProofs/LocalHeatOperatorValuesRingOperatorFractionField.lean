module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem genPt_mem_cover : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  intro R _ G Ω _ _ φ x' hx c hc J W hW
  set K := FractionRing Ω
  have hK : (⊤ : (Sp K).Opens) ≤ (spMap (algebraMap Ω K) ≫ x') ⁻¹ᵁ (⨆ i, W i) := by
    rw [hW, ← Scheme.Hom.comp_preimage]
    rw [Category.assoc, hx]
    simp only [GlobalTheory.HeatV.bo, Scheme.affineBasicOpen_coe, Scheme.preimage_basicOpen_top]
    rw [Scheme.basicOpen_of_isUnit]
    have e : spMap (algebraMap Ω K) ≫ spMap φ = Spec.map (CommRingCat.ofHom ((algebraMap Ω K).comp φ)) := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e]
    have h1 := congrArg (fun f => f.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((algebraMap Ω K).comp φ)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
    rw [← h1]
    refine IsUnit.map _ ?_
    refine isUnit_iff_ne_zero.mpr ?_
    intro h0
    exact hc ((IsFractionRing.injective Ω K) (by simpa using h0))
  obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
  have hp := hK (Set.mem_univ p)
  obtain ⟨i, hi⟩ := (TopologicalSpace.Opens.mem_iSup).mp hp
  refine ⟨i, fun q _ => ?_⟩
  have : q = p := Subsingleton.elim _ _
  subst this
  exact hi

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverMemberContainingFractionFieldPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_member_containing_fractionField_point : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R), φ c ≠ 0 → ∀ (J : Type) (W : J → G.left.Opens), ⨆ i, W i = G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → ∃ i, ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ W i := by
  first | exact @GlobalTheory.genPt_mem_cover | exact GlobalTheory.genPt_mem_cover | (intros; apply GlobalTheory.genPt_mem_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRingMapOfPointValuesDetectFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRingMapOfPointValuesDetectFunctions
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ValInj

theorem valR_top_comp (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] (φ : R →+* Ω)
    (x' : Sp Ω ⟶ G.left) (hx : x' ≫ G.hom = spMap φ) (r : R) :
    valR x' ⊤ (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = φ r := by
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : G.left.Opens) := fun _ _ => trivial
  unfold valR
  rw [dite_eq_left ht]
  have h1 : (x'.appLE ⊤ ⊤ ht).hom (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (spMap φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← hx]
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1]
  have h2 := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.comp_apply] at h2
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at h2
  exact h2

theorem injective_of_val (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (φ : R →+* Ω)
    (x' : Sp Ω ⟶ G.left) : x' ≫ G.hom = spMap φ →
    (∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → Function.Injective φ := by
  intro hx hv
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have hf := hv ⊤ _ (fun _ _ => trivial) ((valR_top_comp R G Ω φ x' hx r).trans hr)
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w (η[G])]
    rfl
  have h3 : (η[G]).left.appTop.hom (G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    rfl
  rw [hf, map_zero] at h3
  have h4 := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom h3
  simpa using h4.symm

end GlobalTheory.ValInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRingMapOfPointValuesDetectFunctionsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_ringMap_of_pointValues_detect_functions : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → (∀ (O : G.left.Opens) (f : Γ(G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → Function.Injective φ := by
  first | exact @GlobalTheory.ValInj.injective_of_val | exact GlobalTheory.ValInj.injective_of_val | (intros; apply GlobalTheory.ValInj.injective_of_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericVal

theorem exists_affine_le_preimage {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ⊤ ≤ x ⁻¹ᵁ U := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := x.base (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  refine ⟨U, hU, fun p _ => ?_⟩
  have hsp : (p : PrimeSpectrum Ω) ⤳ IsLocalRing.closedPoint Ω :=
    (PrimeSpectrum.le_iff_specializes (R := Ω) p (IsLocalRing.closedPoint Ω)).1
      (show p.asIdeal ≤ IsLocalRing.maximalIdeal Ω from IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  exact hsp.mem_open (x ⁻¹ᵁ U).isOpen hyU

theorem valR_generic : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ x dd δ δL hF hx hδL O f hO
  obtain ⟨U, hU, hxU⟩ := exists_affine_le_preimage x
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := fun q _ => hxU (show (spMap (algebraMap Ω (FractionRing Ω))).base q ∈ (⊤ : (Sp Ω).Opens) from trivial)
  let q₀ : Sp (FractionRing Ω) := default
  have hq : ξ.base q₀ ∈ O ⊓ U := ⟨hO trivial, hξU trivial⟩
  obtain ⟨s, hsle, hsmem⟩ := hU.exists_basicOpen_le (V := O ⊓ U) ⟨ξ.base q₀, hq⟩ hq.2
  set W := X.basicOpen s with hWdef
  have hWO : W ≤ O := hsle.trans inf_le_left
  have hWU : W ≤ U := X.basicOpen_le s
  have hW : ⊤ ≤ ξ ⁻¹ᵁ W := fun q _ => by
    rw [Subsingleton.elim q q₀]; exact hsmem
  letI : Algebra Γ(X, U) Γ(X, W) := (resG X hWU).toAlgebra
  haveI : IsLocalization.Away s Γ(X, W) := hU.isLocalization_basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) (resG X hWO f)
  have hmu : IsUnit (resG X hWU (m : Γ(X, U))) := IsLocalization.map_units Γ(X, W) m
  change resG X hWO f * resG X hWU (m : Γ(X, U)) = resG X hWU a at hm
  have vres : ∀ {V' : X.Opens} (e : W ≤ V') (g : Γ(X, V')), valR ξ W (resG X e g) = valR ξ V' g :=
    fun e g => GlobalTheory.Points.valR_res ξ e hW g
  have vU : ∀ g : Γ(X, U), valR ξ U g = algebraMap Ω (FractionRing Ω) (valR x U g) := fun g =>
    GlobalTheory.Points.valR_spMap_comp _ x U hxU g
  have hdd : ∀ g : Γ(X, U), dd W (resG X hWU g) = resG X hWU (dd U g) := fun g => hF.2.2 U W hWU le_top g
  have hddO : dd W (resG X hWO f) = resG X hWO (dd O f) := hF.2.2 O W hWO le_top f
  have hL := hF.2.1 W le_top (resG X hWO f) (resG X hWU (m : Γ(X, U)))
  rw [hm, hdd, hdd, hddO] at hL
  have e1 := congrArg (valR ξ W) hL
  have e2 := congrArg (valR ξ W) hm
  simp only [GlobalTheory.Points.valR_add ξ W hW, GlobalTheory.Points.valR_mul ξ W hW, vres, vU, hx U _ hxU] at e1 e2
  have hM : IsUnit (algebraMap Ω (FractionRing Ω) (valR x U (m : Γ(X, U)))) := by
    have h1 := hmu.map (GlobalTheory.Points.valMap ξ W hW).hom
    rwa [← GlobalTheory.Points.valR_eq, vres, vU] at h1
  have e3 := congrArg δL e2
  rw [Derivation.leibniz, hδL, hδL, smul_eq_mul, smul_eq_mul] at e3
  apply hM.mul_left_cancel
  linear_combination -e1 - e3

end GlobalTheory.GenericVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldCommVectorFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_fractionField_comm_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (dd : Fld X) (δ : Derivation ℤ Ω Ω) (δL : Derivation ℤ (FractionRing Ω) (FractionRing Ω)), IsField ⊤ dd → (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd O f) = δ (valR x O f)) → (∀ ω, δL (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω)) → ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (dd O f) = δL (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenericVal.valR_generic | exact GlobalTheory.GenericVal.valR_generic | (intros; apply GlobalTheory.GenericVal.valR_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionField
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FracPt

theorem stalkIso_gs {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (f : Sp K ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom.hom (gs f (closedPoint K) U a) = valR f U a := by
  have e1 : gs f (closedPoint K) U a = (Sp K).presheaf.germ ⊤ (closedPoint K) trivial ((f.appLE U ⊤ h).hom a) := by
    erw [gs_eq f _ U (h trivial)]
    rw [← TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE h) (closedPoint K) trivial]
    rfl
  erw [e1]
  rw [valR, dite_eq_left h]
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of K)]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.FracPt

namespace GlobalTheory.FracPt

theorem valR_spMap_const {Ω K : Type} [CommRing Ω] [CommRing K] (f : Ω →+* K) (ω : Ω) :
    valR (spMap f) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = f ω := by
  have h : ⊤ ≤ spMap f ⁻¹ᵁ ⊤ := le_rfl
  rw [valR, dite_eq_left h]
  calc _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom f).hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) := by
          rw [← Scheme.ΓSpecIso_naturality]; rfl
    _ = f ω := by
          have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = ω := by
            rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
          rw [CommRingCat.hom_comp, RingHom.comp_apply, e, CommRingCat.hom_ofHom]

theorem chart_eq_value_mul_pow : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω]
    (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j →
    ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ,
      ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω →
        valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) =
          algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  intro X L hL Ω _ _ x g j O hO hxO
  let ηF := spMap (algebraMap Ω (FractionRing Ω))
  let z : Sp (FractionRing Ω) := closedPoint (FractionRing Ω)
  have hz : ((ηF ≫ x) ≫ 𝟙 X) z ∈ L.U j := by
    rw [Category.comp_id]; exact hO (hxO trivial)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := PUnit) (fun _ => (ηF ≫ x) ≫ 𝟙 X) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  let φ := (stalkClosedPointIso (CommRingCat.of (FractionRing Ω))).hom.hom
  refine ⟨Units.map φ.toMonoidHom (val g ηF z J), fun k σ ω hv => ?_⟩
  have e := congrArg φ (hv _ ηF z J hJ)
  have hOW : O ≤ (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ))).U (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hO hy
  rw [sval_of σ (ηF ≫ x) z J (fun _ => j) (fun _ => hJj PUnit.unit)] at e
  erw [← gs_res (ηF ≫ x) z hOW (hxO trivial) (σ.f fun _ => j)] at e
  rw [map_mul, Units.val_pow_eq_pow_val, map_pow] at e
  have e1 := stalkIso_gs (ηF ≫ x) O hxO ((X.presheaf.map (homOfLE hOW).op).hom (σ.f fun _ => j))
  have e2 := stalkIso_gs ηF ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)
  rw [valR_spMap_const] at e2
  erw [e1, e2] at e
  rw [GlobalTheory.KS.rsT, dite_eq_left hOW]
  exact e

end GlobalTheory.FracPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunction_eq_value_mul_unit_pow_fractionField : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ, ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) = algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  first | exact @GlobalTheory.FracPt.chart_eq_value_mul_pow | exact GlobalTheory.FracPt.chart_eq_value_mul_pow | (intros; apply GlobalTheory.FracPt.chart_eq_value_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenDer

open GlobalTheory.Points

theorem top_le_preimage_of_mem {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (y : Sp A ⟶ X)
    (V : X.Opens) (h : y (IsLocalRing.closedPoint A) ∈ V) : ⊤ ≤ y ⁻¹ᵁ V := by
  intro z _
  exact (IsLocalRing.specializes_closedPoint z).mem_open (y ⁻¹ᵁ V).isOpen h

theorem germ_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (p : X) (hp : p ∈ V) (f : Γ(X, U)) :
    X.presheaf.germ V p hp (resG X h f) = X.presheaf.germ U p (h hp) f :=
  X.presheaf.germ_res_apply (homOfLE h) p hp f

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem eventually_zero {X : Scheme.{0}} {Ω : Type} [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X)
    (hx : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) (O : X.Opens) (f : Γ(X, O))
    (hO : ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O)
    (hf : valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f = 0) :
    ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O' ∧ resG X h f = 0 := by
  set ξ := spMap (algebraMap Ω (FractionRing Ω)) ≫ x with hξ
  set p := ξ (IsLocalRing.closedPoint (FractionRing Ω)) with hp
  obtain ⟨U, hU, hqU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (show x (IsLocalRing.closedPoint Ω) ∈ (⊤ : X.Opens) from trivial)
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := top_le_preimage_of_mem x U hqU
  have hξU : ⊤ ≤ ξ ⁻¹ᵁ U := le_preimage_comp (V := ⊤) _ x hxU (le_preimage_top _)
  have hpU : p ∈ U := hξU (Set.mem_univ _)
  have hpO : p ∈ O := hO (Set.mem_univ _)
  letI : Algebra Γ(X, U) (X.presheaf.stalk p) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨p, hpU⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk p) (hU.primeIdealOf ⟨p, hpU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨p, hpU⟩
  obtain ⟨⟨a, s⟩, hmk⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨p, hpU⟩).asIdeal.primeCompl
    (X.presheaf.germ O p hpO f)
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk p) a s
  have hmk' : IsLocalization.mk' (X.presheaf.stalk p) a s = X.presheaf.germ O p hpO f := hmk
  rw [hmk'] at hspec
  have halg : ∀ r : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk p) r = X.presheaf.germ U p hpU r := fun _ => rfl
  rw [halg, halg] at hspec
  have hsu : IsUnit (X.presheaf.germ U p hpU (s : Γ(X, U))) := by
    rw [← halg]; exact IsLocalization.map_units _ s
  have hps : p ∈ X.basicOpen (s : Γ(X, U)) := (X.mem_basicOpen (s : Γ(X, U)) p hpU).mpr hsu
  have hg : X.presheaf.germ (O ⊓ U) p (show p ∈ O ⊓ U from ⟨hpO, hpU⟩) (resG X inf_le_left f * resG X inf_le_right (s : Γ(X, U))) =
      X.presheaf.germ U p hpU a := by
    rw [map_mul, germ_resG, germ_resG, hspec]
  obtain ⟨W₁, hpW₁, iU, iV, heq⟩ := TopCat.Presheaf.germ_eq X.presheaf p (show p ∈ O ⊓ U from ⟨hpO, hpU⟩) hpU _ _ hg
  have e1 : X.presheaf.map iU.op = X.presheaf.map (homOfLE (leOfHom iU)).op := rfl
  have e2 : X.presheaf.map iV.op = X.presheaf.map (homOfLE (leOfHom iV)).op := rfl
  rw [e1, e2] at heq
  change resG X (leOfHom iU) _ = resG X (leOfHom iV) a at heq
  have hξW₁ : ⊤ ≤ ξ ⁻¹ᵁ W₁ := top_le_preimage_of_mem ξ W₁ hpW₁
  have hval := congrArg (valR ξ W₁) heq
  rw [valR_res ξ _ hξW₁, valR_res ξ _ hξW₁, valR_mul ξ _ (le_preimage_mono ξ (leOfHom iU) hξW₁),
    valR_res ξ _ (le_preimage_mono ξ (leOfHom iU) hξW₁), hf, zero_mul, hξ, valR_spMap_comp _ x U hxU] at hval
  have ha0 : a = 0 := hx U a hxU ((IsFractionRing.injective Ω (FractionRing Ω)) (by rw [← hval, map_zero]))
  rw [ha0, map_zero, map_mul, resG_resG, resG_resG] at heq
  set O₃ : X.Opens := W₁ ⊓ X.basicOpen (s : Γ(X, U)) with hO₃
  have h₃ : O₃ ≤ W₁ := inf_le_left
  have hunit : IsUnit (resG X (h₃.trans ((leOfHom iU).trans inf_le_right)) (s : Γ(X, U))) := by
    have h0 : IsUnit (resG X (X.basicOpen_le (s : Γ(X, U))) (s : Γ(X, U))) :=
      RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace (s : Γ(X, U))
    rw [← resG_resG (X.basicOpen_le (s : Γ(X, U))) (show O₃ ≤ X.basicOpen (s : Γ(X, U)) from inf_le_right)]
    exact h0.map _
  refine ⟨O₃, h₃.trans ((leOfHom iU).trans inf_le_left), top_le_preimage_of_mem ξ O₃ (show p ∈ O₃ from ⟨hpW₁, hps⟩), ?_⟩
  have := congrArg (resG X h₃) heq
  rw [map_mul, resG_resG, resG_resG, map_zero] at this
  exact (hunit.mul_left_eq_zero).mp this

theorem valR_sub {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [valR_eq x U h, map_sub]

theorem top_le_preimage_inf {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) {U V : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun _ hz => ⟨hU hz, hV hz⟩

section Field

variable {X : Scheme.{0}} {K : Type} [Field K] (ξ : Sp K ⟶ X) (W : X.Opens)

def valField (hW : ⊤ ≤ ξ ⁻¹ᵁ W) : Subfield K where
  carrier := {y | ∃ (O : X.Opens) (f : Γ(X, O)), O ≤ W ∧ ⊤ ≤ ξ ⁻¹ᵁ O ∧ valR ξ O f = y}
  zero_mem' := ⟨W, 0, le_rfl, hW, valR_zero ξ W hW⟩
  one_mem' := ⟨W, 1, le_rfl, hW, valR_one ξ W hW⟩
  add_mem' := by
    rintro _ _ ⟨O, f, hOW, hO, rfl⟩ ⟨O', f', -, hO', rfl⟩
    have h2 := top_le_preimage_inf ξ hO hO'
    refine ⟨O ⊓ O', resG X inf_le_left f + resG X inf_le_right f', inf_le_left.trans hOW, h2, ?_⟩
    rw [valR_add ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2]
  mul_mem' := by
    rintro _ _ ⟨O, f, hOW, hO, rfl⟩ ⟨O', f', -, hO', rfl⟩
    have h2 := top_le_preimage_inf ξ hO hO'
    refine ⟨O ⊓ O', resG X inf_le_left f * resG X inf_le_right f', inf_le_left.trans hOW, h2, ?_⟩
    rw [valR_mul ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2]
  neg_mem' := by
    rintro _ ⟨O, f, hOW, hO, rfl⟩
    exact ⟨O, -f, hOW, hO, valR_neg ξ O hO f⟩
  inv_mem' := by
    rintro _ ⟨O, f, hOW, hO, rfl⟩
    by_cases h0 : valR ξ O f = 0
    · rw [h0, inv_zero]; exact ⟨W, 0, le_rfl, hW, valR_zero ξ W hW⟩
    · have hB := (le_preimage_basicOpen_iff ξ hO f).mpr (Ne.isUnit h0)
      have hfu : IsUnit (resG X (X.basicOpen_le f) f) :=
        RingedSpace.isUnit_res_basicOpen X.toLocallyRingedSpace.toRingedSpace f
      obtain ⟨u, hu⟩ := hfu
      refine ⟨X.basicOpen f, ↑u⁻¹, (X.basicOpen_le f).trans hOW, hB, ?_⟩
      have : valR ξ (X.basicOpen f) (↑u⁻¹) * valR ξ O f = 1 := by
        rw [← valR_res ξ (X.basicOpen_le f) hB f, ← valR_mul ξ _ hB]
        change valR ξ (X.basicOpen f) (↑u⁻¹ * resG X (X.basicOpen_le f) f) = 1
        rw [← hu, Units.inv_mul, valR_one ξ _ hB]
      exact eq_inv_of_mul_eq_one_left this

variable {ξ W}

theorem valR_der_eq (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (d : Fld X) (hd : IsField W d) {O O' : X.Opens} (f : Γ(X, O)) (f' : Γ(X, O')) (hOW : O ≤ W) (hO'W : O' ≤ W)
    (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (hO' : ⊤ ≤ ξ ⁻¹ᵁ O') (e : valR ξ O f = valR ξ O' f') :
    valR ξ O (d O f) = valR ξ O' (d O' f') := by
  have h2 := top_le_preimage_inf ξ hO hO'
  obtain ⟨O₃, h₃, hO₃, hz⟩ := H (O ⊓ O') (resG X inf_le_left f - resG X inf_le_right f') h2
    (by rw [valR_sub ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2, e, sub_self])
  rw [map_sub, resG_resG, resG_resG, sub_eq_zero] at hz
  rw [← valR_res ξ (h₃.trans inf_le_left) hO₃, ← valR_res ξ (h₃.trans inf_le_right) hO₃,
    ← hd.2.2 O O₃ _ hOW f, ← hd.2.2 O' O₃ _ hO'W f', hz]

end Field

section Der

variable {X : Scheme.{0}} {K : Type} [Field K] (ξ : Sp K ⟶ X) (W : X.Opens)

theorem mem_valField_iff (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (y : K) :
    y ∈ valField ξ W hW ↔ ∃ (O : X.Opens) (f : Γ(X, O)), O ≤ W ∧ ⊤ ≤ ξ ⁻¹ᵁ O ∧ valR ξ O f = y := Iff.rfl

def valDer (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (y : valField ξ W hW) : K :=
  valR ξ (Classical.choose ((mem_valField_iff ξ W hW y).mp y.2))
    (d _ (Classical.choose (Classical.choose_spec ((mem_valField_iff ξ W hW y).mp y.2))))

variable {ξ W}

theorem valDer_eq (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (y : valField ξ W hW) {O : X.Opens} (f : Γ(X, O))
    (hOW : O ≤ W) (hO : ⊤ ≤ ξ ⁻¹ᵁ O) (e : valR ξ O f = y) : valDer ξ W hW d y = valR ξ O (d O f) := by
  obtain ⟨hOW', hO', e'⟩ := Classical.choose_spec (Classical.choose_spec ((mem_valField_iff ξ W hW y).mp y.2))
  exact valR_der_eq H d hd _ f hOW' hOW hO' hO (e'.trans e.symm)

theorem valDer_add (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (a b : valField ξ W hW) :
    valDer ξ W hW d (a + b) = valDer ξ W hW d a + valDer ξ W hW d b := by
  obtain ⟨O, f, hOW, hO, ea⟩ := (mem_valField_iff ξ W hW a).mp a.2
  obtain ⟨O', f', hO'W, hO', eb⟩ := (mem_valField_iff ξ W hW b).mp b.2
  have h2 := top_le_preimage_inf ξ hO hO'
  have h2W : O ⊓ O' ≤ W := inf_le_left.trans hOW
  rw [valDer_eq H hW d hd (a + b) (resG X inf_le_left f + resG X inf_le_right f') h2W h2
      (by rw [valR_add ξ _ h2, valR_res ξ _ h2, valR_res ξ _ h2, ea, eb]; rfl),
    valDer_eq H hW d hd a (resG X (inf_le_left : O ⊓ O' ≤ O) f) h2W h2 (by rw [valR_res ξ _ h2, ea]),
    valDer_eq H hW d hd b (resG X (inf_le_right : O ⊓ O' ≤ O') f') h2W h2 (by rw [valR_res ξ _ h2, eb]),
    hd.1 _ h2W, valR_add ξ _ h2]

theorem valDer_mul (H : ∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 →
      ∃ (O' : X.Opens) (h : O' ≤ O), ⊤ ≤ ξ ⁻¹ᵁ O' ∧ resG X h f = 0)
    (hW : ⊤ ≤ ξ ⁻¹ᵁ W) (d : Fld X) (hd : IsField W d) (a b : valField ξ W hW) :
    valDer ξ W hW d (a * b) = (a : K) * valDer ξ W hW d b + (b : K) * valDer ξ W hW d a := by
  obtain ⟨O, f, hOW, hO, ea⟩ := (mem_valField_iff ξ W hW a).mp a.2
  obtain ⟨O', f', hO'W, hO', eb⟩ := (mem_valField_iff ξ W hW b).mp b.2
  have h2 := top_le_preimage_inf ξ hO hO'
  have h2W : O ⊓ O' ≤ W := inf_le_left.trans hOW
  have ea' : valR ξ (O ⊓ O') (resG X inf_le_left f) = a := by rw [valR_res ξ _ h2, ea]
  have eb' : valR ξ (O ⊓ O') (resG X inf_le_right f') = b := by rw [valR_res ξ _ h2, eb]
  rw [valDer_eq H hW d hd (a * b) (resG X inf_le_left f * resG X inf_le_right f') h2W h2
      (by rw [valR_mul ξ _ h2, ea', eb']; rfl),
    valDer_eq H hW d hd a (resG X (inf_le_left : O ⊓ O' ≤ O) f) h2W h2 ea',
    valDer_eq H hW d hd b (resG X (inf_le_right : O ⊓ O' ≤ O') f') h2W h2 eb',
    hd.2.1 _ h2W, valR_add ξ _ h2, valR_mul ξ _ h2, valR_mul ξ _ h2, ea', eb']

end Der

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem exists_derivation_fractionRing : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] [CharZero Ω] (x : Sp Ω ⟶ X), (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) → ∀ (W : X.Opens) (d : Fld X), IsField W d → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ W → ∃ dt0 : Derivation ℤ (FractionRing Ω) (FractionRing Ω), ∀ (O : X.Opens) (f : Γ(X, O)), O ≤ W → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (d O f) = dt0 (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  intro X Ω _ _ _ _ x hx W d hd hW
  set K := FractionRing Ω
  set ξ := spMap (algebraMap Ω K) ≫ x with hξ
  have H := eventually_zero x hx
  set F := valField ξ W hW
  haveI : CharZero K := ⟨fun m n h => by
    rw [← map_natCast (algebraMap Ω K) m, ← map_natCast (algebraMap Ω K) n] at h
    exact Nat.cast_injective (IsFractionRing.injective Ω K h)⟩
  haveI : CharZero F := ⟨fun m n h => Nat.cast_injective (R := K) (by simpa using congrArg Subtype.val h)⟩
  haveI : Algebra.FormallySmooth F K := formallySmooth_of_charZero F K
  obtain ⟨d', hadd, hmul, hext⟩ := GlobalTheory.KS.exists_derivation_extend_of_formallySmooth F K K (RingHom.id K)
    (valDer ξ W hW d) (valDer_add H hW d hd) (fun a b => valDer_mul H hW d hd a b)
  refine ⟨{ toFun := d'
            map_add' := hadd
            map_smul' := ?_
            map_one_eq_zero' := ?_
            leibniz' := ?_ }, fun O f hOW hO => ?_⟩
  · intro m y
    have := (AddMonoidHom.mk' d' hadd).map_zsmul m y
    simp only [AddMonoidHom.mk'_apply, zsmul_eq_mul] at this
    simp only [RingHom.id_apply, Algebra.smul_def, algebraMap_int_eq, eq_intCast, smul_eq_mul]
    rw [this]; simp
  · have h1 := hmul 1 1
    simp only [RingHom.id_apply, _root_.one_mul, _root_.mul_one] at h1
    show d' 1 = 0
    linear_combination -h1
  · intro a b
    show d' (a * b) = a • d' b + b • d' a
    simp [hmul, smul_eq_mul]
  have hmem : valR ξ O f ∈ F := ⟨O, f, hOW, hO, rfl⟩
  change _ = d' (algebraMap F K ⟨_, hmem⟩)
  rw [hext]
  exact (valDer_eq H hW d hd ⟨_, hmem⟩ f hOW hO rfl).symm

end GlobalTheory.GenDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationFractionRingOfVectorFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_fractionRing_of_vectorField : ∀ (X : Scheme.{0}) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] [CharZero Ω] (x : Sp Ω ⟶ X), (∀ (O : X.Opens) (f : Γ(X, O)), ⊤ ≤ x ⁻¹ᵁ O → valR x O f = 0 → f = 0) → ∀ (W : X.Opens) (d : Fld X), IsField W d → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ W → ∃ dt0 : Derivation ℤ (FractionRing Ω) (FractionRing Ω), ∀ (O : X.Opens) (f : Γ(X, O)), O ≤ W → ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (d O f) = dt0 (valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O f) := by
  first | exact @GlobalTheory.GenDer.exists_derivation_fractionRing | exact GlobalTheory.GenDer.exists_derivation_fractionRing | (intros; apply GlobalTheory.GenDer.exists_derivation_fractionRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatRingOperatorConjByPowNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatRingOperatorConjByPowNonzero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false


open GlobalTheory.Heat in
theorem GlobalTheory.Heat.ringOp_conj_pow_gen : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  intro Ω _ _ n d δ Θ h2 u p p' c hc
  have hs : ∀ (s : Finset (Fin n)) (D : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
    intro s D x
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]
  refine ⟨d - ∑ a, ∑ b, ((1 / 2) * Θ a b * (δ a c / c)) • δ b - ∑ a, ∑ b, ((1 / 2) * Θ a b * (δ b c / c)) • δ a, u,
    p + d c / c - (1 / 2) * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c),
    p' - (1 / 2) * ∑ a, ∑ b, Θ a b * δ a (δ b c / c) + ∑ a, u a * (δ a c / c), ?_, ?_⟩
  · intro y hy
    rw [Derivation.sub_apply, Derivation.sub_apply, hs, hs, Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero, sub_zero]
    · intro a _
      rw [hs]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Derivation.smul_apply, hy, smul_zero]
    · intro a _
      rw [hs]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Derivation.smul_apply, hy, smul_zero]
  · intro k f
    have e1 : ∀ b, δ b (c ^ k * f) = c ^ k * (δ b f + (k : FractionRing Ω) * (δ b c / c) * f) :=
      fun b => fractionField_derivation_pow_mul_logDeriv (δ b) hc k f
    have e2 : ∀ a b, δ a (δ b (c ^ k * f)) = c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f) := by
      intro a b
      rw [e1, fractionField_derivation_pow_mul_logDeriv (δ a) hc]
      simp only [map_add (f := _), Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
      ring
    have e3 : d (c ^ k * f) = c ^ k * (d f + (k : FractionRing Ω) * (d c / c) * f) := fractionField_derivation_pow_mul_logDeriv d hc k f
    unfold ringOp
    simp only [e2, e3]
    simp only [e1, Derivation.sub_apply, hs, Derivation.smul_apply, smul_eq_mul]
    have hL : ∑ a, ∑ b, Θ a b * (c ^ k * (δ a (δ b f) + (k : FractionRing Ω) * (δ a c / c) * δ b f
        + (k : FractionRing Ω) * (δ b c / c) * δ a f + (k : FractionRing Ω) * δ a (δ b c / c) * f
        + (k : FractionRing Ω) ^ 2 * (δ a c / c) * (δ b c / c) * f)) =
        c ^ k * (∑ a, ∑ b, Θ a b * δ a (δ b f) + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
          + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
          + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c)
          + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hU : ∑ a, u a * (c ^ k * (δ a f + (k : FractionRing Ω) * (δ a c / c) * f)) =
        c ^ k * (∑ a, u a * δ a f + (k : FractionRing Ω) * f * ∑ a, u a * (δ a c / c)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have hD1 : ∑ a, ∑ b, (1 / 2) * Θ a b * (δ a c / c) * δ b f = (1 / 2) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hD2 : ∑ a, ∑ b, (1 / 2) * Θ a b * (δ b c / c) * δ a f = (1 / 2) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have hh : (2 : FractionRing Ω) * (1 / 2) = 1 := mul_one_div_cancel h2
    rw [hL, hU, hD1, hD2]
    linear_combination (c ^ k * ((k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ a c / c) * δ b f)
      + (k : FractionRing Ω) * ∑ a, ∑ b, Θ a b * ((δ b c / c) * δ a f)
      + (k : FractionRing Ω) ^ 2 * f * ∑ a, ∑ b, Θ a b * (δ a c / c) * (δ b c / c)
      + (k : FractionRing Ω) * f * ∑ a, ∑ b, Θ a b * δ a (δ b c / c))) * hh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatRingOperatorConjByPowNonzeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatRingOperator_conj_by_pow_nonzero : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  first | exact @GlobalTheory.Heat.ringOp_conj_pow_gen | exact GlobalTheory.Heat.ringOp_conj_pow_gen | (intros; apply GlobalTheory.Heat.ringOp_conj_pow_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

theorem valR_cst_eq_iota : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  intro R _ G Ω _ _ φ x' hx c iota hiota O h hO θ
  rw [GlobalTheory.CechKSSmul.valR_appLE_comp _ G.hom (GlobalTheory.HeatV.bo R c).1 O h hO θ]
  have hz : (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)) := by
    rw [Category.assoc, hx]
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  have h' : ⊤ ≤ ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom) ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 :=
    fun p hp => h (hO hp)
  set s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c with hs
  set z := (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ≫ G.hom with hzdef
  let F : Γ(Sp R, (Sp R).basicOpen s) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
  have hF : ∀ θ, valR z (GlobalTheory.HeatV.bo R c).1 θ = F θ := fun θ => by
    simp only [valR, dif_pos h']; rfl
  suffices e : F = iota by rw [hF]; exact DFunLike.congr_fun e θ
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (S := Γ(Sp R, (Sp R).basicOpen s)) ?_
  ext y0
  obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r = y0 :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y0, by simp⟩
  have e1 : algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      GlobalTheory.HeatV.resV R c r := rfl
  change F (GlobalTheory.HeatV.resV R c r) = iota (GlobalTheory.HeatV.resV R c r)
  rw [hiota]
  show (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom
    ((z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom (GlobalTheory.HeatV.resV R c r)) = _
  have e2 : (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op ≫ z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h' =
      z.appTop := by
    exact (Scheme.Hom.map_appLE z h' _).trans (Scheme.Hom.appLE_eq_app z)
  have e3 : (z.appLE (GlobalTheory.HeatV.bo R c).1 ⊤ h').hom
      (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      z.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← e2]; rfl
  rw [show (GlobalTheory.HeatV.resV R c r) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) s)).op).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) from rfl, e3]
  rw [hz]
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ((algebraMap Ω (FractionRing Ω)).comp φ)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [n]
  simp

end GlobalTheory.HeatV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueFractionFieldEqBasicOpenExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (c : R) (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* FractionRing Ω), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = algebraMap Ω (FractionRing Ω) (φ r)) → ∀ (O : G.left.Opens) (h : O ≤ G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') ⁻¹ᵁ O → ∀ θ, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') O (GlobalTheory.HeatV.cst G.hom _ h θ) = iota θ := by
  first | exact @GlobalTheory.HeatV.valR_cst_eq_iota | exact GlobalTheory.HeatV.valR_cst_eq_iota | (intros; apply GlobalTheory.HeatV.valR_cst_eq_iota <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeatOperatorValuesRingOperatorFractionField
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatVal

theorem rsT_self {Y : Scheme.{0}} {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  simp [GlobalTheory.KS.rsT]

theorem valR_eq {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE U ⊤ h).hom) f := by
  unfold valR; rw [dite_eq_left h]; rfl

theorem value_opV_ringOp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω)), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ σ' : SecM (𝟙 t.G.left) t.PP.L k) (r a : R) (ω : Ω), (∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i))) → IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ ω' : Ω, IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ (algebraMap Ω (FractionRing Ω)) ω' = (algebraMap Ω (FractionRing Ω)) (φ r) * ((algebraMap Ω (FractionRing Ω)) (φ a) * ringOp ⇑dt (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) u' p p' k ((algebraMap Ω (FractionRing Ω)) ω) - 2 * (k : (FractionRing Ω)) * (algebraMap Ω (FractionRing Ω)) (φ (D a)) * (algebraMap Ω (FractionRing Ω)) ω) := by
  intro E _ _ _ H R _ _ _ _ _ _ t c hc n v' D Ω _ _ _ φ x' δ dd' hadic hx' hinv hδφ hval hinj g hg δL hδL Θ₁ DV hDV iota hiota J W j d u pf pf' hW hcov hWU hfield hlift hglue
  have hφ : Function.Injective φ := GlobalTheory.T.injective_ringMap_of_pointValues_detect_functions R t.G Ω φ x' hx' hinj
  have hφc : φ c ≠ 0 := fun h => hc (hφ (by rw [h, map_zero]))
  haveI : CharZero Ω := charZero_of_injective_ringHom (φ.comp (algebraMap ℚ R)).injective
  haveI : CharZero (FractionRing Ω) :=
    charZero_of_injective_ringHom (IsFractionRing.injective Ω (FractionRing Ω))
  obtain ⟨i0, hi0⟩ := GlobalTheory.T.exists_cover_member_containing_fractionField_point R t.G Ω φ x' hx' c hφc J W hcov
  obtain ⟨dt0, hdt0⟩ := GlobalTheory.T.exists_derivation_fractionRing_of_vectorField t.G.left Ω x' hinj (W i0) (d i0) (hfield i0) hi0
  have hddv := fun a => GlobalTheory.T.pointValue_fractionField_comm_vectorField t.G.left Ω x' (dd' a) (δ a) (δL a) (hinv a).1 (hval a) (hδL a)
  have hcst := GlobalTheory.T.pointValue_fractionField_eq_basicOpen_extension R t.G Ω φ x' hx' c iota hiota (W i0) (hW i0) hi0
  obtain ⟨e₀, he₀⟩ := GlobalTheory.T.chartFunction_eq_value_mul_unit_pow_fractionField t.G.left t.PP.L t.PP.isLB Ω x' g (j i0) (W i0) (hWU i0) hi0
  set ψ : Γ(t.G.left, W i0) →+* FractionRing Ω :=
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing Ω))).hom.hom.comp
      ((spMap (algebraMap Ω (FractionRing Ω)) ≫ x').appLE (W i0) ⊤ hi0).hom with hψ
  have hv : ∀ f, valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x') (W i0) f = ψ f :=
    fun f => valR_eq _ _ hi0 f
  have hd0 : ∀ F, ψ (d i0 (W i0) F) = dt0 (ψ F) := by
    intro F; rw [← hv, ← hv]; exact hdt0 _ _ le_rfl hi0
  have hdd : ∀ a F, ψ (dd' a (W i0) F) = δL a (ψ F) := by
    intro a F; rw [← hv, ← hv]; exact hddv a _ _ hi0
  have hc' : ∀ θ, ψ (GlobalTheory.HeatV.cst t.G.hom _ (hW i0) θ) = iota θ := by
    intro θ; rw [← hv]; exact hcst θ
  obtain ⟨dt, u', p, p', hdt, hgauge⟩ := GlobalTheory.T.heatRingOperator_conj_by_pow_nonzero Ω n dt0 δL (iota.mapMatrix Θ₁) two_ne_zero
    (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) (e₀ : FractionRing Ω) e₀.ne_zero
  have hdtR : ∀ r, dt (algebraMap Ω (FractionRing Ω) (φ r)) = algebraMap Ω (FractionRing Ω) (φ (D r)) := by
    intro r
    rw [hdt _ (fun a => by rw [hδL, hδφ, map_zero]), ← hiota, ← hiota, ← hc', ← hc', ← hd0]
    have := hlift i0 (W i0) le_rfl (GlobalTheory.HeatV.resV R c r)
    rw [this, hDV]
  refine ⟨dt, u', p, p', hdtR, ?_⟩
  intro k hk σ σ' r a ω hσ' hω
  have hop : ∀ F, ψ (GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i0) (pf i0) (pf' i0) k (W i0) (hW i0) F) =
      ringOp ⇑dt0 (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) (fun a => iota (u a)) (ψ (pf i0)) (ψ (pf' i0)) k (ψ F) := by
    intro F
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.HeatV.opV, ringOp, map_add (f := _), map_sub, map_mul, map_sum, map_natCast, map_ofNat, map_pow, hd0, hdd,
      hc', rsT_self, RingHom.mapMatrix_apply, Matrix.map_apply]
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_sectionValue_in_frame_localRing_point t.G.left t.PP.L t.PP.isLB Ω x' g hg k σ'
  refine ⟨ω', hω', ?_⟩
  have h1 := he₀ k σ ω hω
  have h2 := he₀ k σ' ω' hω'
  rw [hv] at h1 h2
  have h3 := congrArg ψ (hσ' i0)
  simp only [map_mul, map_sub, map_natCast, map_ofNat, hop, hc', hiota] at h3
  rw [h1, h2, mul_comm (algebraMap Ω (FractionRing Ω) ω) ((e₀ : FractionRing Ω) ^ k), hgauge] at h3
  apply mul_left_cancel₀ (pow_ne_zero k e₀.ne_zero)
  linear_combination h3

end GlobalTheory.HeatVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalHeatOperatorValuesRingOperatorFractionFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_heat_operator_values_ring_operator_fraction_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω) (dd' : Fin n → Fld t.G.left), IsAdicComplete ((maximalIdeal R).map φ) Ω → x' ≫ t.G.hom = spMap φ → (∀ a, IsInv t.G (v' a) (dd' a)) → (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x' ⁻¹ᵁ O → valR x' O (dd' a O f) = δ a (valR x' O f)) → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∀ (Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (DV : Derivation ℤ Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), (∀ r, DV (GlobalTheory.HeatV.resV R c r) = GlobalTheory.HeatV.resV R c (D r)) → ∀ (iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω)), (∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r)) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → Fld t.G.left) (u : Fin n → Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)) (pf pf' : ∀ i, Γ(t.G.left, W i)) (hW : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1), ⨆ i, W i = t.G.hom ⁻¹ᵁ (GlobalTheory.HeatV.bo R c).1 → (∀ i, W i ≤ t.PP.L.U (j i)) → (∀ i, IsField (W i) (d i)) → (∀ i O (h : O ≤ W i) (a : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1)), d i O (GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) a) = GlobalTheory.HeatV.cst t.G.hom _ (h.trans (hW i)) (DV a)) → (∀ (k : ℕ) i i' O (h : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)), GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k O (h.trans (inf_le_left.trans (hW i))) (pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * f) = pbT (𝟙 t.G.left) (t.PP.L.g (j i) (j i')).val O ^ k * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i') (pf i') (pf' i') k O (h.trans (inf_le_right.trans (hW i'))) f) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ σ' : SecM (𝟙 t.G.left) t.PP.L k) (r a : R) (ω : Ω), (∀ i, rsT (σ'.f fun _ => j i) (W i) = GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c r) * (GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c a) * GlobalTheory.HeatV.opV t.G.hom _ dd' Θ₁ u (d i) (pf i) (pf' i) k (W i) (hW i) (rsT (σ.f fun _ => j i) (W i)) - 2 * (k : Γ(t.G.left, W i)) * GlobalTheory.HeatV.cst t.G.hom _ (hW i) (GlobalTheory.HeatV.resV R c (D a)) * rsT (σ.f fun _ => j i) (W i))) → IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ ω' : Ω, IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ (algebraMap Ω (FractionRing Ω)) ω' = (algebraMap Ω (FractionRing Ω)) (φ r) * ((algebraMap Ω (FractionRing Ω)) (φ a) * ringOp ⇑dt (fun b => ⇑(δL b)) (iota.mapMatrix Θ₁) u' p p' k ((algebraMap Ω (FractionRing Ω)) ω) - 2 * (k : (FractionRing Ω)) * (algebraMap Ω (FractionRing Ω)) (φ (D a)) * (algebraMap Ω (FractionRing Ω)) ω) := by
  first | exact @GlobalTheory.HeatVal.value_opV_ringOp | exact GlobalTheory.HeatVal.value_opV_ringOp | (intros; apply GlobalTheory.HeatVal.value_opV_ringOp <;> assumption)
end
