module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem evO_constO (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R) :
    evO G (constO G r) = r := by
  have hw : (η[G]).left ≫ G.hom = 𝟙 _ := by simpa using Over.w (η[G])
  have h1 := Scheme.germ_stalkClosedPointTo (R := CommRingCat.of R) (η[G]).left ⊤ trivial
  have h2 := congrArg (fun q => q.hom ((G.hom.appLE ⊤ ⊤ (by simp)).hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) h1
  refine h2.trans ?_
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (by simp) ≫
      (η[G]).left.app ⊤ ≫ (Functor.mapIso (Spec (CommRingCat.of R)).presheaf
        (eqToIso (show (η[G]).left ⁻¹ᵁ ⊤ = ⊤ by simp)).op ≪≫ Scheme.ΓSpecIso (CommRingCat.of R)).hom = 𝟙 _ := by
    rw [Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE_assoc]
    simp [hw]
    rw [show Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ (by simp) = 𝟙 _ from
      (Scheme.Hom.appLE_eq_app (𝟙 (Sp R))).trans (Scheme.Hom.id_app ⊤)]
    simp
  exact congrArg (fun q => q.hom r) key

end GlobalTheory.FormalOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstantsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeStalkEvalAtOrigin_originStalkConstants : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (r : R), evO G (constO G r) = r := by
  first | exact @GlobalTheory.FormalOrigin.evO_constO | exact GlobalTheory.FormalOrigin.evO_constO | (intros; apply GlobalTheory.FormalOrigin.evO_constO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem spMap_fromSpecStalk_origin_hom (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type)
    [CommRing Ω] (ψ : G.left.presheaf.stalk (origin G) →+* Ω) :
    spMap ψ ≫ G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (ψ.comp (constO G)) := by
  have e : G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (constO G) := by
    have e' : CommRingCat.ofHom (constO G) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop ≫ G.left.presheaf.germ ⊤ (origin G) trivial := by
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) ≫
        G.left.presheaf.germ ⊤ (origin G) trivial = _
      have h : G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) = G.hom.appTop := Scheme.Hom.appLE_eq_app _
      rw [h]
    simp only [spMap]
    rw [e', Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [e]
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.FormalOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_map_fromSpecStalk_origin_comp_structure_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type) [CommRing Ω] (ψ : G.left.presheaf.stalk (origin G) →+* Ω), spMap ψ ≫ G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (ψ.comp (constO G)) := by
  first | exact @GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom | exact GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom | (intros; apply GlobalTheory.FormalOrigin.spMap_fromSpecStalk_origin_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParameters
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelParamRad

theorem prod_dvd_of_forall_dvd {R : Type} [CommMonoidWithZero R] :
    ∀ (m : ℕ) (t : Fin m → R), (∀ k, Prime (t k)) → (∀ i j, t i ∣ t j → i = j) →
      ∀ x : R, (∀ k, t k ∣ x) → ∏ k, t k ∣ x := by
  intro m
  induction m with
  | zero => intro t _ _ x _; simp
  | succ m ih =>
    intro t hp hd x hx
    obtain ⟨y, rfl⟩ := hx 0
    rw [Fin.prod_univ_succ]
    refine mul_dvd_mul_left _ (ih (fun k => t k.succ) (fun k => hp _) (fun i j h => Fin.succ_injective _ (hd _ _ h)) y
      fun k => ?_)
    refine ((hp k.succ).dvd_or_dvd (hx k.succ)).resolve_left fun h => ?_
    exact Fin.succ_ne_zero k (hd _ _ h)

theorem isRadical_span_prod : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R)
    (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  intro o R _ _ _ _ b m t h
  have hp : ∀ k, Prime (t k) := fun k => prime_of_not_mem_sq (h.1 k) (h.notMem_sq k)
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  exact prod_dvd_of_forall_dvd m t hp (fun i j hij => h.eq_of_dvd hij) x
    fun k => (hp k).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem t (Finset.mem_univ k)).trans hn)

end GlobalTheory.RelParamRad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRadicalSpanProdRelativeRegularParametersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRadical_span_prod_relativeRegularParameters : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R) (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  first | exact @GlobalTheory.RelParamRad.isRadical_span_prod | exact GlobalTheory.RelParamRad.isRadical_span_prod | (intros; apply GlobalTheory.RelParamRad.isRadical_span_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem natCast_prime_not_isUnit_stalk (X : Scheme.{0}) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y (cPt p))) := by
  intro hu
  have h := hu.map (Scheme.stalkClosedPointTo y).hom
  rw [map_natCast] at h
  refine (not_isUnit_OO_iff ((p : ℕ) : OO p)).2 ?_ h
  have e : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_lt_one_iff.2 dvd_rfl

theorem dvd_of_not_isUnit_stalk (X : Scheme.{0}) (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ X) (n : ℕ)
    (h : ¬ IsUnit ((n : ℕ) : X.presheaf.stalk (y (cPt q)))) : q ∣ n := by
  have h1 : ¬ IsUnit ((Scheme.stalkClosedPointTo y).hom (n : X.presheaf.stalk (y (cPt q)))) :=
    fun hu => h ((isUnit_map_iff (Scheme.stalkClosedPointTo y).hom _).1 hu)
  rw [map_natCast, not_isUnit_OO_iff] at h1
  have e : (((n : ℕ) : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((n : ℕ) : ℚ_[q]) := by simp
  rw [e, PadicAlgCl.norm_extends] at h1
  exact Padic.norm_natCast_lt_one_iff.1 h1

theorem eq_of_cPt_eq : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X)
    (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  intro X p q hp hq y y' h
  have h1 := natCast_prime_not_isUnit_stalk X p y
  have h2 : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y' (cPt q))) := by
    rw [← h]; exact h1
  have h3 := dvd_of_not_isUnit_stalk X q y' p h2
  exact ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h3).symm

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_eq_of_classicalPoint_same_centre : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X) (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  first | exact @GlobalTheory.Poinc.eq_of_cPt_eq | exact GlobalTheory.Poinc.eq_of_cPt_eq | (intros; apply GlobalTheory.Poinc.eq_of_cPt_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc

theorem fnOf_app_of_pff : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  intro X Y _ _ m φ hφ V hV hV' a
  have h : gp Y ≫ m = spMap φ ≫ gp X := by
    obtain ⟨l, h1, h2⟩ := hφ
    rw [Category.comp_id] at h1
    rw [← h1, h2]
  have hloc : IsLocalHom φ := inferInstance
  have e1 : Spec.map (m.stalkMap (genericPoint Y)) ≫ X.fromSpecStalk (m (genericPoint Y)) =
      Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) := by
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]; exact h
  have e2 := (SpecToEquivOfLocalRing X (CommRingCat.of Y.functionField)).symm.injective
    (a₁ := ⟨m (genericPoint Y), m.stalkMap (genericPoint Y), inferInstance⟩)
    (a₂ := ⟨genericPoint X, CommRingCat.ofHom φ, hloc⟩)
    (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]; exact e1)
  obtain ⟨h₁, e3⟩ := SpecToEquivOfLocalRing_eq_iff.mp e2
  simp only at e3
  have key : X.presheaf.germ V _ hV' ≫ m.stalkMap (genericPoint Y) =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ := by
    rw [e3, TopCat.Presheaf.stalkCongr_hom]
    exact X.presheaf.germ_stalkSpecializes_assoc hV' _ _
  have key' : m.app V ≫ Y.presheaf.germ (m ⁻¹ᵁ V) (genericPoint Y) hV' =
      X.presheaf.germ V _ hV ≫ CommRingCat.ofHom φ :=
    (Scheme.Hom.germ_stalkMap m V (genericPoint Y) hV').symm.trans key
  exact congrArg (fun q => CommRingCat.Hom.hom q a) key'

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionAppOfPreservesGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFunction_app_of_preservesGenericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (m : Y ⟶ X) (φ : X.functionField →+* Y.functionField), PFF (𝟙 _) m φ → ∀ (V : X.Opens) (hV : genericPoint X ∈ V) (hV' : genericPoint Y ∈ m ⁻¹ᵁ V) (a : Γ(X, V)), fnOf (m ⁻¹ᵁ V) hV' ((m.app V).hom a) = φ (fnOf V hV a) := by
  first | exact @GlobalTheory.Desc.fnOf_app_of_pff | exact GlobalTheory.Desc.fnOf_app_of_pff | (intros; apply GlobalTheory.Desc.fnOf_app_of_pff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpen
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

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ActMatrix

open MonoidalCategory CartesianMonoidalCategory MonObj

theorem isTanAtG_act {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] (x0 : Sp S ⟶ X) (a : 𝓞 E)
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : IsTanAtG t x0 (v ≫ (t.act.act a).left) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, Over.w]; exact hv.1
  · rw [← Category.assoc, hv.2, ← Over.comp_left]
    congr 1
    haveI := t.act.hom a
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom]

theorem actMatrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∃ A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(X, U.1), ∀ a i, IsCombAtG t (GlobalTheory.LogKS.chart U) v (A a i) (v i ≫ (t.act.act a).left) := by
  intro E _ _ _ H X t U n v hv hb
  refine ⟨fun a i => Classical.choose (hb _ (isTanAtG_act t _ a (hv i))), fun a i => ?_⟩
  exact (Classical.choose_spec (hb _ (isTanAtG_act t _ a (hv i)))).1

end GlobalTheory.ActMatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCmOrderActionMatrixOnAffineOpenStatement
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
theorem _root_.GlobalTheory.T.existsUnique_cmOrderActionMatrix_on_affineOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∃ A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(X, U.1), ∀ a i, IsCombAtG t (GlobalTheory.LogKS.chart U) v (A a i) (v i ≫ (t.act.act a).left) := by
  first | exact @GlobalTheory.ActMatrix.actMatrix | exact GlobalTheory.ActMatrix.actMatrix | (intros; apply GlobalTheory.ActMatrix.actMatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKill
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin

theorem foldr_iterate_of_kills {A ι : Type} [Zero A] (ds : ι → A → A) (α : ι → ℕ) (c : A)
    (hc : ∀ i, ds i c = 0) (h0 : ∀ i, ds i 0 = 0) (l : List ι) :
    ((∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = c) ∧
    (¬ (∀ i ∈ l, α i = 0) → l.foldr (fun i g => (ds i)^[α i] g) c = 0) := by
  induction l with
  | nil => exact ⟨fun _ => rfl, fun h => absurd (fun i hi => by simp at hi) h⟩
  | cons j l ih =>
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [List.foldr_cons, h j (by simp), ih.1 (fun i hi => h i (by simp [hi]))]
      rfl
    · rw [List.foldr_cons]
      by_cases hl : ∀ i ∈ l, α i = 0
      · rw [ih.1 hl]
        have hj : α j ≠ 0 := by
          intro hj
          apply h
          intro i hi
          rcases List.mem_cons.1 hi with rfl | hi
          · exact hj
          · exact hl i hi
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
        rw [hk, Function.iterate_succ_apply, hc j]
        exact Function.iterate_fixed (h0 j) k
      · rw [ih.2 hl]
        exact Function.iterate_fixed (h0 j) _

theorem taylor_const :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  intro A B _ _ _ n ev ds c hc
  ext α
  rw [MvPowerSeries.coeff_C]
  change (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp (fun i => ⇑(ds i)) α c) = _
  split_ifs with h
  · subst h
    rw [iterOp_zero]
    simp
  · have : iterOp (fun i => ⇑(ds i)) α c = 0 := by
      refine (foldr_iterate_of_kills (fun i => ⇑(ds i)) α c hc (fun i => map_zero _) _).2 ?_
      intro h'
      apply h
      ext i
      exact h' i (List.mem_finRange i)
    rw [this, map_zero, smul_zero]

end GlobalTheory.FormalOrigin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationTaylorPowerSeriesOfDerivationsKillStatement
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivationTaylorPowerSeries_of_derivations_kill : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A) (c : A), (∀ i, ds i c = 0) → taylor ev (fun i => ⇑(ds i)) c = MvPowerSeries.C (ev c) := by
  first | exact @GlobalTheory.FormalOrigin.taylor_const | exact GlobalTheory.FormalOrigin.taylor_const | (intros; apply GlobalTheory.FormalOrigin.taylor_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.EqNormAt

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem norm_val_eqAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  intro o Ω _ _ _ M D V _ _ _ ϖ a ξ p _ ι j hι hj hid f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set z := ξ (closedPoint V) with hz
  set e : V := (Scheme.stalkClosedPointTo ξ).hom ((M.Z.presheaf.germ _ z hxi).hom (D.f i)) with he
  have key : Ideal.span {e} = Ideal.span {ϖ ^ a} := by
    rw [← hid, idlAlong, D.stalkId_idealSheaf i z hxi, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton).1 key

  have hval : M.val (gPt p ≫ spMap j ≫ ξ) (valF M.pt (D.U i) (D.f i)) = ((j e : OO p) : PadicAlgCl p) := by
    rw [← Category.assoc, show gPt p = spMap (OO p).subtype from rfl, spectrumMap_comp,
      RatModel.val_spMap_comp _ ξ (specializes_rfl : z ⤳ z)
      ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩]
    have hv : M.valLoc ξ z specializes_rfl ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩ = e := by
      simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← RatModel.stalkEquiv_germ hxi, RingEquiv.symm_apply_apply, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp, he]
      rw [Category.id_comp]
    rw [RingHom.comp_apply, hv]
    rfl
  rw [hval, hj]
  have hunit : ∀ w : Vˣ, ‖ι (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
    intro w
    have h1 := (hι _).2 ⟨(w : V), rfl⟩
    have h2 := (hι _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
    have h3 : ‖ι (algebraMap V (FractionRing V) (w : V))‖ * ‖ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (ι (algebraMap V (FractionRing V) (w : V))),
      norm_nonneg (ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V)))]
  have he' : e = ϖ ^ a * ((u⁻¹ : Vˣ) : V) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [he', map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]

end GlobalTheory.Poinc.EqNormAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_localEquation_eq_uniformiser_pow_classicalPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  first | exact @GlobalTheory.Poinc.EqNormAt.norm_val_eqAt | exact GlobalTheory.Poinc.EqNormAt.norm_val_eqAt | (intros; apply GlobalTheory.Poinc.EqNormAt.norm_val_eqAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbas
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbas
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

noncomputable section

theorem GlobalTheory.LogPole.frVec_cell_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N h S _ _ w zw hzw x hx hUx hpt
  have hl : TF.X.F.Lies (zw ≫ inc₀ TF.X Z) w := hpt ▸ TF.X.lies_ptY w
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_map _ h.2.2.1 hzw
  have hxz' : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hxz : zw ≫ toBase TF Z = x := hxz'.symm.trans (hl.1.trans hx)
  subst hxz
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd w) hl.1 k hk
  obtain ⟨t, ht⟩ := hQ.exists_frBor hl
  choose b hb hdiag hsum using fun σ =>
    GlobalTheory.FlagMod.frVec_of_frBor (M := (TF.X.F.M k).toMChart) (TF.X.F.inM hk hxz') (hQ.over.trans hxz') hx ht σ
  refine ⟨fun σ i j => b σ j i, fun σ i j hij => hb σ hij, fun σ i => by show IsUnit (b σ i i); rw [hdiag]; exact Units.isUnit _,
    fun σ i => ?_⟩
  have hv' : ∀ j, IsTanAtG TF.Y.t (zw ≫ toBase TF Z)
      (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v j) := by
    intro j
    have h0 := GlobalTheory.FactorDepth.isTanAtG_map TF.Y.t (ev (zw ≫ toBase TF Z) U.1 hUx) (hv.1 j)
    rwa [LogKS.chart, GlobalTheory.FlagMod.spMap_ev _ U.2 hUx] at h0
  have hcell := h.2.2.2.2.2.2.2 S zw hzw hUx hk hxz' σ
  have h2 : IsCombAtG TF.Y.t (zw ≫ toBase TF Z)
      (fun j => (tv (TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxz' σ j)).left) (fun j => b σ j i)
      (tv (frVec TF.Y w hx σ i)).left := by
    rw [GlobalTheory.LieMet.isComb_iff, hsum σ i, hQ.frVec_eq hxz' (hQ.over.trans hxz') σ]
  have h3 := GlobalTheory.TangentLinear.isCombAtG_mulVec _ (fun j => hv' (e ⟨σ, j⟩)) _
    (Matrix.of fun m j => ev zw W hzw ((L σ * N σ) j m)) (fun j => b σ j i) _ (fun j => hcell j) h2
  convert h3 using 1
  funext m
  show ∑ j, b σ j i * ev zw W hzw ((L σ * N σ) j m) = ∑ j, ev zw W hzw ((L σ * N σ) j m) * b σ j i
  exact Finset.sum_congr rfl fun j _ => _root_.mul_comm _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellFramedPointVectorsLowerTriangularEigenbasStatement
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
theorem _root_.GlobalTheory.T.bigCell_framedPointVectors_lowerTriangular_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1), zw ≫ inc₀ TF.X Z = TF.X.ptY w → ∃ B : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ σ i j, i < j → B σ i j = 0) ∧ (∀ σ i, IsUnit (B σ i i)) ∧ ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (B σ * (L σ * N σ).map (ev zw W hzw)) i j) (tv (frVec TF.Y w hx σ i)).left := by
  first | exact @GlobalTheory.LogPole.frVec_cell_comb | exact GlobalTheory.LogPole.frVec_cell_comb | (intros; apply GlobalTheory.LogPole.frVec_cell_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlat
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CodimOne

theorem mem_preimage_sup_of_ringKrullDim_stalk_le_one :
    ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  intro X S _ f _ _ V U hV hU z hz
  by_contra hzm
  have hzU : f z ∉ U := fun h => hzm (Or.inl h)
  have hzV : z ∉ V := fun h => hzm (Or.inr h)
  set s := f z with hs

  let ξ : X := f.fiberι s (genericPoint (f.fiber s))
  have hfξ : f ξ = s := (f.range_fiberι s).le ⟨_, rfl⟩
  have hrange : ∀ y : X, f y = s → ξ ⤳ y := by
    intro y hy
    obtain ⟨w, rfl⟩ : y ∈ Set.range (f.fiberι s) := (f.range_fiberι s).ge hy
    exact (genericPoint_specializes w).map (f.fiberι s).continuous
  obtain ⟨x, hxV, hxs⟩ := hV s
  have hξV : ξ ∈ V := (hrange x hxs).mem_open V.isOpen hxV
  have hξz : ξ ⤳ z := hrange z rfl
  have hξnez : ξ ≠ z := fun h => hzV (h ▸ hξV)

  obtain ⟨u, huU⟩ := hU
  have hηU : genericPoint S ∈ U := (genericPoint_specializes u).mem_open U.isOpen huU
  have hηs : genericPoint S ⤳ f ξ := hfξ ▸ genericPoint_specializes s
  obtain ⟨ζ, hζξ, hfζ⟩ := (Flat.generalizingMap f) hηs
  have hζneξ : ζ ≠ ξ := by
    intro h
    apply hzU
    rw [← hfξ, ← h, hfζ]
    exact hηU
  have h1 : z < ξ := lt_of_le_not_ge hξz (fun h => hξnez (hξz.antisymm h).eq)
  have h2 : ξ < ζ := lt_of_le_not_ge hζξ (fun h => hζneξ (hζξ.antisymm h).eq)
  have hc : (2 : ℕ∞) ≤ Order.coheight z := by
    have a := Order.coheight_add_one_le h1
    have b := Order.coheight_add_one_le h2
    have : (1 : ℕ∞) + 1 ≤ Order.coheight ζ + 1 + 1 := by gcongr; exact le_add_self
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ Order.coheight ζ + 1 + 1 := this
      _ ≤ Order.coheight ξ + 1 := by gcongr
      _ ≤ Order.coheight z := a
  rw [ringKrullDim_stalk_eq_coheight] at hz
  have : Order.coheight z ≤ 1 := by exact_mod_cast hz
  exact absurd (hc.trans this) (by norm_num)

end GlobalTheory.CodimOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlatStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat : ∀ (X S : Scheme.{0}) [IsIntegral S] (f : X ⟶ S) [Flat f] [GeometricallyIntegral f] (V : X.Opens) (U : S.Opens), (∀ s : S, ∃ x ∈ V, f x = s) → (U : Set S).Nonempty → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ f ⁻¹ᵁ U ⊔ V) := by
  first | exact @GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one | exact GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one | (intros; apply GlobalTheory.CodimOne.mem_preimage_sup_of_ringKrullDim_stalk_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOnEveryFibreLocalFormBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOnEveryFibreLocalFormBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyVals

theorem nzFib_of_isLocSec : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  intro S G _ _ L δ σ i R _ ξ t hξ ht hσ r
  have hP := isGrpPullback_pullback G ξ
  obtain ⟨z, hz, hz'⟩ := hσ (ξ r)
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback hP.1 z r hz
  obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hk : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k := G.left.basicOpen_le _ hb
  have hle : (bL L ξ).L.U (fun _ => k.1) ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := by
    intro x hx
    refine ⟨mem_pull.1 hx, mem_pull.2 ?_⟩
    have e : G.hom (pullback.fst G.hom ξ x) = ξ (pullback.snd G.hom ξ x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    show G.hom (pullback.fst G.hom ξ x) ∈ δ.U i
    rw [e]
    exact hξ (Set.mem_univ _)
  have hy1 : y ∈ (bL L ξ).L.U (fun _ => k.1) := mem_pull.2 hk.1
  have hy2 := hle hy1
  have hb' : pullback.fst G.hom ξ y ∈ G.left.basicOpen (σ.f (k.1, fun _ => i)) := by
    have hm : pullback.fst G.hom ξ y ∈ (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) := ⟨hk, hy2⟩
    have e := congrArg G.left.basicOpen (σ.compat k (k.1, fun _ => i))
    rw [Scheme.basicOpen_mul] at e
    have e1 := G.left.basicOpen_res (σ.f k) (homOfLE (inf_le_left : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have e2 := G.left.basicOpen_res (σ.f (k.1, fun _ => i)) (homOfLE (inf_le_right : (CechPic.tens L.L (δ.pull G.hom)).U k ⊓
      (CechPic.tens L.L (δ.pull G.hom)).U (k.1, fun _ => i) ≤ _)).op
    have h1 := e1.ge ⟨hm, hb⟩
    have h2 := (e.le h1).2
    exact (e2.le h2).2
  refine ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k.1, ?_⟩⟩
  rw [ht (fun _ => k.1) hle]
  exact (Scheme.basicOpen_appLE (pullback.fst G.hom ξ) _ _ hle _).ge ⟨hy1, hb'⟩

end GlobalTheory.KeyVals

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOnEveryFibreLocalFormBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  first | exact @GlobalTheory.KeyVals.nzFib_of_isLocSec | exact GlobalTheory.KeyVals.nzFib_of_isLocSec | (intros; apply GlobalTheory.KeyVals.nzFib_of_isLocSec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem gm_spMap_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (y : Sp B) :
    gm (spMap f) y ⊤ (unitOn u) = gm (𝟙 (Sp B)) y ⊤ (unitOn (Units.map f.toMonoidHom u)) := by
  apply Units.ext
  rw [gm_val _ y ⊤ trivial, gm_val _ y ⊤ trivial]
  have nat := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact congrArg ((Sp B).presheaf.germ ⊤ y trivial).hom nat.symm

theorem evenDefect_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  intro R₁ _ _ R₂ _ _ σ D₁ D₂ β v xe gam hgam gp hv hc _ hψ h hE χ z J₂ hJ₂
  beta_reduce
  have hgam' : spMap gam ≫ jK R₁ = jK R₂ ≫ spMap σ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hgam
  have cx : ∀ a, D₂.xK a ≫ β = spMap gam ≫ D₁.xK (xe a) := fun a => by
    show (jK R₂ ≫ (D₂.c a).left) ≫ β = spMap gam ≫ jK R₁ ≫ (D₁.c (xe a)).left
    rw [Category.assoc, hc, ← Category.assoc, ← hgam', Category.assoc]
  have cn : D₂.xK (-χ) = D₂.xK χ ≫ (ι[D₂.P.A]).left := by
    show (toUnit _ ≫ D₂.c (-χ)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  choose J₁ hJ₀ using fun φ : (TK R₂).left ⟶ D₁.P.A.left => exists_chart D₁.P.isLB (φ z)
  have hJ₁ : Good D₁.P.L z J₁ := hJ₀
  have vψ : ∀ a, val (D₁.psi (xe a)) (spMap gam) z J₁ =
      (gw v (D₂.xK a) z (J₁ (D₂.xK a ≫ β)) (J₂ (D₂.xK a)))⁻¹ * val (D₂.psi a) (𝟙 _) z J₂ := fun a => by
    have := GlobalTheory.CubTransport.val_pmaps (fun _ => cx a) (hψ a) (𝟙 _) hJ₁ hJ₂
    rwa [Fintype.prod_unique, Category.id_comp, Category.id_comp, zpow_neg_one] at this
  have hcorr := corr_of_val D₁.P.isLB (t := LB.mulGen _ _ _ _ _ (D₁.psi (-(xe χ))) (LB.pullGen _ _ _ D₁.sym (D₁.xK (xe χ))))
    (t' := GlobalTheory.UU.scaleGen (unitOn (h (xe χ))) (D₁.psi (xe χ))) fun y J hJ => by
      rw [val_mul hJ, val_pull hJ, GlobalTheory.UU.val_scaleGen _ _ _ hJ, Category.id_comp]
      exact hE (xe χ) y J hJ
  have e := val_corr hJ₁ hcorr (spMap gam)
  have hg : gm (spMap gam) z ⊤ (unitOn (h (xe χ))) =
      gm (𝟙 (TK R₂).left) z ⊤ (unitOn (Units.map gam.toMonoidHom (h (xe χ)))) := gm_spMap_unitOn gam _ z
  rw [val_mul hJ₁, val_pull hJ₁, GlobalTheory.UU.val_scaleGen _ _ _ hJ₁, hg, ← cx, ← map_neg xe χ, vψ, vψ] at e
  have hs := GlobalTheory.PsiRing.val_sym_comp GlobalTheory.globalFns_holds gp hv (D₂.xK χ) z hJ₁ hJ₂
  rw [← cn] at hs
  rw [hs] at e
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDefectDegenerationDataBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenDefect_degenerationData_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  first | exact @GlobalTheory.PolDeg.evenDefect_baseChange | exact GlobalTheory.PolDeg.evenDefect_baseChange | (intros; apply GlobalTheory.PolDeg.evenDefect_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomain
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section
namespace GlobalTheory.BlowAmpleNoeth
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.ProjBlowup

theorem ample_twist_of_blowup : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X X' N : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') (EX : EffCartierData N), IsProjOver s →
    FinalTheorems.Blowup b J → IsFinite ν → EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      IsAmpleLB (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)) := by
  intro R _ _ _ X X' N s J b ν EX hs hb hν hEX L hL
  obtain ⟨L₀, m, σ, hL₀, hσ⟩ := GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf R X s J hs
  obtain ⟨c, hc, hprop, hci⟩ := GlobalTheory.T.exists_closedImmersion_blowup_generatingSections R X X' s J b L₀ m σ hs hb hσ
  have hψ : Proportional σ (ν ≫ b) (ν ≫ c) := hprop.comp ν
  have hiso := GlobalTheory.T.pullback_O1_iso_blowup_twist_dual R X N J L₀ m σ (ν ≫ b) (ν ≫ c) EX hL₀ hσ hψ hEX
  have : IsProper s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (GlobalTheory.AmpleDominates.eventually_isAmpleLB s hL hL₀)
  refine ⟨T₀, fun T hT => ?_⟩
  have hA := hT₀ T hT
  have hO := isAmple_projective_O_one R m
  set A := LB.div (lbPow L T) L₀ with hAdef
  set p := pullback.fst s (PSpace.str R m)
  set q := pullback.snd s (PSpace.str R m)
  set B := tens (A.pull p) ((O1 R m).pull q)
  have hBL : B.IsLB := isLB_tens (LB.isLB_pull hA.isLB _) (LB.isLB_pull hO.isLB _)
  have hB : IsAmpleLB B := by
    refine hA.box hO hBL (IsPullback.of_hasPullback s (PSpace.str R m)) ?_
    have h1 := LB.isLB_div hBL (LB.isLB_pull hA.isLB p)
    refine (cls_eq_zero_iff (LB.isLB_div h1 (LB.isLB_pull hO.isLB q))).1 ?_
    rw [cls_div h1 (LB.isLB_pull hO.isLB q), cls_div hBL (LB.isLB_pull hA.isLB p),
      cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q)]
    abel
  let h : N ⟶ pullback s (PSpace.str R m) := ν ≫ pullback.lift b c hc
  have hp : h ≫ p = ν ≫ b := by
    simp only [h, p, Category.assoc]; rw [pullback.lift_fst]
  have hq : h ≫ q = ν ≫ c := by
    simp only [h, q, Category.assoc]; rw [pullback.lift_snd]
  have h2 := hB.pull_of_isAffineHom h
  have hT : (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)).IsLB :=
    isLB_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb)
  refine h2.of_lbIso hT ((cls_eq_iff hT (LB.isLB_pull hBL h)).1 ?_)
  have hG := (cls_eq_iff (LB.isLB_pull hO.isLB _) (isLB_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb))).2 hiso
  rw [cls_tens (LB.isLB_pull hL₀ _) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb, cls_pull hO.isLB, cls_pull hL₀] at hG
  rw [cls_pull hBL, cls_tens (LB.isLB_pull hA.isLB p) (LB.isLB_pull hO.isLB q), cls_pull hA.isLB, cls_pull hO.isLB,
    cls_div (isLB_lbPow hL.isLB T) hL₀, cls_lbPow hL.isLB,
    cls_tens (isLB_lbPow (LB.isLB_pull hL.isLB _) T) (isLB_dual EX.isLB_lb), cls_dual EX.isLB_lb,
    cls_lbPow (LB.isLB_pull hL.isLB _), cls_pull hL.isLB, map_add, ← pull_comp, ← pull_comp, hp, hq, hG]
  simp only [map_sub, map_nsmul]
  abel

end GlobalTheory.BlowAmpleNoeth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTwistNormalisedBlowupNoetherianDomainStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (X X' N : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') (EX : EffCartierData N), IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν → EX.idealSheaf = J.comap (ν ≫ b) → ∀ L : LB X, IsAmpleLB L → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → IsAmpleLB (CechPic.tens (lbPow (L.pull (ν ≫ b)) T) (CechPic.dual EX.lb)) := by
  first | exact @GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup | exact GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup | (intros; apply GlobalTheory.BlowAmpleNoeth.ample_twist_of_blowup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPieces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPieces
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.Poinc

theorem stalkId_finsetProd {X : Scheme.{0}} {ι : Type} (s : Finset ι) (K : ι → X.IdealSheafData) (x : X) :
    FinalTheorems.stalkId (∏ c ∈ s, K c) x = ∏ c ∈ s, FinalTheorems.stalkId (K c) x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  simp only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]

theorem stalkId_prodPow {X : Scheme.{0}} {ι : Type} [Fintype ι] (K : ι → X.IdealSheafData) (e : ι → ℕ) (x : X) :
    FinalTheorems.stalkId (∏ c, K c ^ e c) x = ∏ c, FinalTheorems.stalkId (K c) x ^ e c := by
  rw [stalkId_finsetProd]
  simp only [GlobalTheory.Vanishing.stalkId_pow]

theorem exists_valOn_of_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  intro o _ ζ g n F S j φ ι _ W J d _ huniq hd hsupp htr
  classical
  have hdvd : ∀ c, d c ∣ ∏ c, d c := fun c => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ c)
  have htop : ∀ c x, x ∉ W c → FinalTheorems.stalkId (J c) x = ⊤ := fun c x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J c) fun hs => hx (hsupp c x hs).1
  refine ⟨∏ c, d c, ∏ c, J c ^ ((∏ c, d c) / d c), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => by have := hd c; omega)
  · intro x hx
    obtain ⟨c, hc, -⟩ := huniq x
    by_cases hs : x ∈ (J c).support
    · exact (hsupp c x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun c' _ => ?_
      by_cases e : c' = c
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J c') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop c' x fun h => e ((huniq x).unique h hc), ← Ideal.one_eq_top, one_pow]
  · intro T ξ hξ
    obtain ⟨c, hc, -⟩ := huniq (ξ (closedPoint T.V))
    obtain ⟨a, ha, hJ⟩ := htr c T ξ hξ hc
    refine ⟨(∏ c, d c) / d c * a, ?_, ?_⟩
    · have hd0 : (d c : ℝ) ≠ 0 := by have := hd c; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd c) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single c, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro c' _ e
        rw [htop c' _ fun h => e ((huniq _).unique h hc), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ c) h

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPiecesStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  first | exact @GlobalTheory.Poinc.exists_valOn_of_pieces | exact GlobalTheory.Poinc.exists_valOn_of_pieces | (intros; apply GlobalTheory.Poinc.exists_valOn_of_pieces <;> assumption)
end
end
