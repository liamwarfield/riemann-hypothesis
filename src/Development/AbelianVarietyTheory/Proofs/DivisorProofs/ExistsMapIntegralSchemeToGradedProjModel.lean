module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.Desc.GenGlue

lemma isDominant_of_spec {K : Type} [Field K] {W : Scheme.{0}} (v : Sp K ⟶ W)
    (h : ∀ (q : Sp K) (z : W), v q ⤳ z) : IsDominant v :=
  ⟨fun z => closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self (IsLocalRing.closedPoint K)))
    (specializes_iff_mem_closure.1 (h _ z))⟩

theorem exists_glue : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) →
    ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P),
    (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) →
    ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  intro Y P _ _ U hU f w hw
  have hgp : ∀ q, gp Y q = genericPoint Y := fun q => by
    obtain rfl : q = IsLocalRing.closedPoint Y.functionField := Subsingleton.elim _ _
    exact Scheme.fromSpecStalk_closedPoint
  have hgen : ∀ (V : Y.Opens) (y : Y), y ∈ V → genericPoint Y ∈ V := fun V y hy =>
    ((genericPoint_spec Y).mem_open_set_iff V.2).2 ⟨y, trivial, hy⟩
  have hlift : ∀ V : Y.Opens, genericPoint Y ∈ V →
      ∃ l : Sp Y.functionField ⟶ V.toScheme, l ≫ V.ι = gp Y := fun V hV =>
    ⟨IsOpenImmersion.lift V.ι (gp Y) (by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨q, rfl⟩; rw [hgp]; exact hV), IsOpenImmersion.lift_fac _ _ _⟩
  have hdom : ∀ (V : Y.Opens) (l : Sp Y.functionField ⟶ V.toScheme), l ≫ V.ι = gp Y → IsDominant l := by
    intro V l hl
    refine isDominant_of_spec l fun q z => ?_
    rw [← V.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e1 : V.ι (l q) = gp Y q := by rw [← hl]; rfl
    rw [e1, hgp]
    exact (genericPoint_spec Y).specializes trivial
  let g : Y → Y.PartialMap P := fun y => ⟨U y, (U y).2.dense ⟨y, hU y⟩, f y⟩
  have heq : ∀ y y', (g y).toRationalMap = (g y').toRationalMap := by
    intro y y'
    rw [Scheme.PartialMap.toRationalMap_eq_iff]
    let V := U y ⊓ U y'
    have hV : genericPoint Y ∈ V := ⟨hgen _ y (hU y), hgen _ y' (hU y')⟩
    obtain ⟨l, hl⟩ := hlift V hV
    haveI := hdom V l hl
    refine ⟨V, V.2.dense ⟨_, hV⟩, inf_le_left, inf_le_right, ?_⟩
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
    refine ext_of_isDominant l ?_
    rw [← Category.assoc, ← Category.assoc,
      hw y _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl]),
      hw y' _ (by rw [Category.assoc, Scheme.homOfLE_ι, hl])]
  let y0 := genericPoint Y
  let F := (g y0).toRationalMap
  have htop : F.domain = ⊤ :=
    top_le_iff.1 fun z _ => Scheme.RationalMap.mem_domain.2 ⟨g z, hU z, heq z y0⟩
  have htop' : F.toPartialMap.domain = ⊤ := htop
  let k : Y ⟶ F.toPartialMap.domain.toScheme := IsOpenImmersion.lift F.toPartialMap.domain.ι (𝟙 Y)
    (by rw [Scheme.Opens.range_ι, htop']; simp)
  have hk : k ≫ F.toPartialMap.domain.ι = 𝟙 Y := IsOpenImmersion.lift_fac _ _ _
  have hgpm : gp Y ≫ k ≫ F.toPartialMap.hom = w := by
    obtain ⟨l, hl⟩ := hlift (U y0) (hU y0)
    have h2 : (g y0).domain.ι ≫ k = Y.homOfLE (g y0).le_domain_toRationalMap := by
      apply (cancel_mono F.toPartialMap.domain.ι).1
      rw [Category.assoc, hk, Category.comp_id]
      exact (Scheme.homOfLE_ι _ _).symm
    rw [← hl]
    rw [Category.assoc, reassoc_of% h2]
    exact (congrArg (l ≫ ·) (g y0).toPartialMap_toRationalMap_restrict).trans (hw y0 l hl)
  refine ⟨k ≫ F.toPartialMap.hom, fun y => ?_, hgpm⟩
  obtain ⟨l, hl⟩ := hlift (U y) (hgen _ y (hU y))
  haveI := hdom _ l hl
  refine ext_of_isDominant l ?_
  rw [reassoc_of% hl, hgpm, hw y l hl]

end GlobalTheory.Desc.GenGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueMorphismsIntegralAgreeAtGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [P.IsSeparated] (U : Y → Y.Opens), (∀ y, y ∈ U y) → ∀ (f : ∀ y, (U y).toScheme ⟶ P) (w : Sp Y.functionField ⟶ P), (∀ y (l : Sp Y.functionField ⟶ (U y).toScheme), l ≫ (U y).ι = gp Y → l ≫ f y = w) → ∃ m : Y ⟶ P, (∀ y, (U y).ι ≫ m = f y) ∧ gp Y ≫ m = w := by
  first | exact @GlobalTheory.Desc.GenGlue.exists_glue | exact GlobalTheory.Desc.GenGlue.exists_glue | (intros; apply GlobalTheory.Desc.GenGlue.exists_glue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstants
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem gp_comp_eq_spMap_cst (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R) :
    gp X ≫ p = spMap (cst p) := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp [← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  conv_lhs => rw [h]
  rw [gp]
  erw [Scheme.fromSpecStalk_toSpecΓ_assoc]
  erw [← Spec.map_comp]
  rfl

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointCompStructureEqSpecMapConstantsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R), gp X ≫ p = spMap (cst p) := by
  first | exact @GlobalTheory.Desc.gp_comp_eq_spMap_cst | exact GlobalTheory.Desc.gp_comp_eq_spMap_cst | (intros; apply GlobalTheory.Desc.gp_comp_eq_spMap_cst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAndUnitPreservedByFunctionFieldCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAndUnitPreservedByFunctionFieldCompatible
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Desc.StalkMap

variable {X : Scheme.{0}}

theorem top_le_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

theorem appLE_fromSpecStalk (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (top_le_fromSpecStalk x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (top_le_fromSpecStalk x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

def val {R : Type} [CommRing R] (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(X, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

theorem val_congr {R : Type} [CommRing R] {g g' : Sp R ⟶ X} (e : g = g') (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(X, V)) : val g V h u = val g' V h' u := by
  subst e; rfl

theorem val_gp [IsIntegral X] (V : X.Opens) (hV : genericPoint X ∈ V) (h : ⊤ ≤ gp X ⁻¹ᵁ V) (u : Γ(X, V)) :
    val (gp X) V h u = GlobalTheory.Cartier.fnOf V hV u := by
  have : (gp X).appLE V ⊤ h = X.presheaf.germ V _ hV ≫ (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv :=
    appLE_fromSpecStalk (genericPoint X) V hV
  unfold val
  rw [RingHom.comp_apply, this]
  exact (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).inv_hom_id_apply _

end GlobalTheory.Desc.StalkMap

namespace GlobalTheory.Desc.StalkMap

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem val_appLE (g : Sp R ⟶ X) (φ : X ⟶ X') (V : X'.Opens) (W : X.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(X', V)) :
    val g W h ((φ.appLE V W e).hom u) = val (g ≫ φ) V h' u :=
  congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u))
    (Scheme.Hom.appLE_comp_appLE g φ V W ⊤ e h)

theorem val_top (g : Sp R ⟶ X) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(X, ⊤)) :
    val g ⊤ h u = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  have : g.appLE ⊤ ⊤ h = g.appTop := Scheme.Hom.appLE_eq_app g
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (CommRingCat.Hom.hom q u)) this

theorem val_spMap (σ : R →+* R') (g : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V)
    (h' : ⊤ ≤ (spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(X, V)) : val (spMap σ ≫ g) V h' u = σ (val g V h u) := by
  refine (val_appLE (spMap σ) g V ⊤ h le_top h' u).symm.trans ((val_top (spMap σ) le_top _).trans ?_)
  exact congrArg (fun q => CommRingCat.Hom.hom q ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

theorem fnOf_app_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField) (hm : gp Y ≫ m = spMap φ ≫ gp P) {W : P.Opens}
    (hY : genericPoint Y ∈ m ⁻¹ᵁ W) (hP : genericPoint P ∈ W) (s : Γ(P, W)) :
    GlobalTheory.Cartier.fnOf (m ⁻¹ᵁ W) hY ((m.app W).hom s) = φ (GlobalTheory.Cartier.fnOf W hP s) := by
  have h1 : ⊤ ≤ gp Y ⁻¹ᵁ (m ⁻¹ᵁ W) := top_le_fromSpecStalk _ _ hY
  have h2 : ⊤ ≤ gp P ⁻¹ᵁ W := top_le_fromSpecStalk _ _ hP
  have h3 : ⊤ ≤ (gp Y ≫ m) ⁻¹ᵁ W := h1
  have h4 : ⊤ ≤ (spMap φ ≫ gp P) ⁻¹ᵁ W := hm ▸ h3
  rw [← val_gp _ hY h1, ← val_gp _ hP h2, ← val_spMap φ (gp P) W h2 h4,
    ← val_congr hm W h3 h4, ← val_appLE (gp Y) m W (m ⁻¹ᵁ W) le_rfl h1 h3, Scheme.Hom.app_eq_appLE]

end GlobalTheory.Desc.StalkMap


open GlobalTheory.Desc.StalkMap in
theorem GlobalTheory.Desc.regAt_map_of_gp : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P)
    (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField),
    RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  intro Y P _ _ m φ hm y v hv
  obtain ⟨W, hW, s, rfl⟩ := hv.exists_fnOf
  have hy : y ∈ m ⁻¹ᵁ W := hW
  have hY : genericPoint Y ∈ m ⁻¹ᵁ W := gen_mem hy
  rw [← fnOf_app_eq m φ hm hY (gen_mem hW) s]
  refine ⟨regAt_fnOf hy hY _, ?_⟩
  rw [unitAt_fnOf_iff hy hY, unitAt_fnOf_iff hW (gen_mem hW), ← Scheme.preimage_basicOpen]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAndUnitPreservedByFunctionFieldCompatibleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (m : Y ⟶ P) (φ : P.functionField →+* Y.functionField), gp Y ≫ m = spMap φ ≫ gp P → ∀ (y : Y) (v : P.functionField), RegAt (m y) v → RegAt y (φ v) ∧ (UnitAt y (φ v) ↔ UnitAt (m y) v) := by
  first | exact @GlobalTheory.Desc.regAt_map_of_gp | exact GlobalTheory.Desc.regAt_map_of_gp | (intros; apply GlobalTheory.Desc.regAt_map_of_gp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToAffineOpenOfFunctionFieldMapRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToAffineOpenOfFunctionFieldMapRegular
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_ringHom_fnOf_eq {Y P : Scheme.{0}} [IsIntegral Y] [IsIntegral P] {U : Y.Opens}
    (hU : genericPoint Y ∈ U) {V : P.Opens} (hVη : genericPoint P ∈ V)
    (φ : P.functionField →+* Y.functionField) (h : ∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) :
    ∃ ψ : Γ(P, V) →+* Γ(Y, U), ∀ s, fnOf U hU (ψ s) = φ (fnOf V hVη s) := by
  choose t ht using fun s => exists_fnOf_eq hU (h s)
  refine ⟨⟨⟨⟨t, ?_⟩, fun a b => ?_⟩, ?_, fun a b => ?_⟩, ht⟩ <;> apply fnOf_injective U hU
  · rw [ht, map_one, map_one, map_one]
  · rw [map_mul, ht, ht, ht, map_mul, map_mul]
  · exact (ht 0).trans (by rw [map_zero, map_zero, map_zero])
  · exact (ht (a + b)).trans (((congrArg φ (map_add _ a b)).trans (map_add φ _ _)).trans
      ((congrArg₂ (· + ·) (ht a) (ht b)).symm.trans (map_add (fnOf U hU) (t a) (t b)).symm))


set_option backward.isDefEq.respectTransparency false in
theorem exists_hom_of_regAt_fnOf : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  intro Y P _ _ U hU V hV hVη φ h
  obtain ⟨ψ, hψ⟩ := exists_ringHom_fnOf_eq hU hVη φ h
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, fun y => ?_, fun l hl => ?_⟩
  · rw [← Category.assoc, Scheme.Hom.comp_apply]
    change _ ∈ (V : Set P)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  · obtain rfl : l = U.fromSpecStalkOfMem (genericPoint Y) hU := by
      rw [← cancel_mono U.ι, hl]
      exact (Scheme.Opens.fromSpecStalkOfMem_ι U _ hU).symm
    have e : CommRingCat.ofHom ψ ≫ Y.presheaf.germ U (genericPoint Y) hU =
        P.presheaf.germ V (genericPoint P) hVη ≫ CommRingCat.ofHom φ := by
      ext s
      exact hψ s
    have e₁ := Scheme.Opens.fromSpecStalkOfMem_toSpecΓ_assoc U (genericPoint Y) hU
      (Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec)
    refine e₁.trans ?_
    rw [← Spec.map_comp_assoc]
    refine (congrArg (fun z => Spec.map z ≫ hV.fromSpec) e).trans ?_
    rw [gp, ← hV.fromSpecStalk_eq_fromSpecStalk hVη, IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc]

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToAffineOpenOfFunctionFieldMapRegularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular : ∀ (Y P : Scheme.{0}) [IsIntegral Y] [IsIntegral P] (U : Y.Opens), genericPoint Y ∈ U → ∀ (V : P.Opens), IsAffineOpen V → ∀ (hVη : genericPoint P ∈ V) (φ : P.functionField →+* Y.functionField), (∀ s : Γ(P, V), ∀ y ∈ U, RegAt y (φ (fnOf V hVη s))) → ∃ f : U.toScheme ⟶ P, (∀ y : U.toScheme, f y ∈ V) ∧ ∀ l : Sp Y.functionField ⟶ U.toScheme, l ≫ U.ι = gp Y → l ≫ f = spMap φ ≫ gp P := by
  first | exact @GlobalTheory.Desc.exists_hom_of_regAt_fnOf | exact GlobalTheory.Desc.exists_hom_of_regAt_fnOf | (intros; apply GlobalTheory.Desc.exists_hom_of_regAt_fnOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapIntegralSchemeToGradedProjModel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ToModel

theorem sep (R : Type) [CommRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) [IsSeparated p] : P.IsSeparated := by
  refine ⟨?_⟩
  rw [terminal.hom_ext (terminal.from P) (p ≫ terminal.from _)]
  infer_instance

theorem gp_dom (Y : Scheme.{0}) [IsIntegral Y] : IsDominant (gp Y) := by
  refine ⟨?_⟩
  have h : genericPoint Y ∈ Set.range (gp Y) := ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  refine Dense.mono (Set.singleton_subset_iff.2 h) ?_
  rw [dense_iff_closure_eq, (genericPoint_spec Y).def]

theorem regAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) (m : ℕ) :
    RegAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact (unitAt_one y).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem reg_div (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k m : ℕ) (u a : Y.functionField) (y : Y)
    (ha : a ∈ Sec D (k * m)) (hu : y ∈ locus D k u) : RegAt y (a / u ^ m) := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h1 := ((hg.nsmul (k * m)).regularAt_iff).1 (ha y)
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have e : a / u ^ m = (a * ((g ^ (k * m) : Y.functionFieldˣ) : Y.functionField)) *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ m := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, ← pow_mul]
    field_simp
  rw [e]
  exact h1.mul (regAt_pow h2.inv.regAt m)

theorem locus_open (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (k : ℕ) (u : Y.functionField) :
    IsOpen (locus D k u) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨g, hg, hu⟩ := hy
  obtain ⟨U, hyU, hU⟩ := hg.exists_nhds
  obtain ⟨V, hyV, hV⟩ := hu.exists_nhds
  exact ⟨(U ⊓ V : Y.Opens), fun z hz => ⟨g, hU z hz.1, hV z hz.2⟩, (U ⊓ V).2, ⟨hyU, hyV⟩⟩

theorem unitAt_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : UnitAt y x) (m : ℕ) :
    UnitAt y (x ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact unitAt_one y
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_of_pow {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {x : Y.functionField} (h : RegAt y x) {n : ℕ}
    (hn : 1 ≤ n) (hu : UnitAt y (x ^ n)) : UnitAt y x := by
  have hx : x ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_pow (by omega)])
  refine (unitAt_iff hx).2 ⟨h, ?_⟩
  have e : x⁻¹ = x ^ (n - 1) * (x ^ n)⁻¹ := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [e]
  exact (regAt_pow h _).mul hu.inv.regAt

theorem locus_iff {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {k k' : ℕ} (hk : 1 ≤ k)
    {u u' : Y.functionField} {y : Y} (hu : y ∈ locus D k u) (hu' : u' ∈ Sec D k') :
    y ∈ locus D k' u' ↔ UnitAt y (u' ^ k / u ^ k') := by
  obtain ⟨g, hg⟩ := D.exists_isEqn y
  have h2 := ((hg.nsmul k).generatesAt_iff).1 hu
  have h1 := ((hg.nsmul k').regularAt_iff).1 (hu' y)
  have e : u' ^ k / u ^ k' = (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
      ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k' := by
    have hg0 : ((g : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
    push_cast
    rw [inv_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k' k]
    field_simp
  show (k' • D).GeneratesAt y u' ↔ _
  rw [(hg.nsmul k').generatesAt_iff, e]
  constructor
  · intro h
    exact (unitAt_pow h k).mul (unitAt_pow h2.inv k')
  · intro h
    refine unitAt_of_pow h1 hk ?_
    have e2 : (u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k =
        ((u' * ((g ^ k' : Y.functionFieldˣ) : Y.functionField)) ^ k *
          ((u * ((g ^ k : Y.functionFieldˣ) : Y.functionField))⁻¹) ^ k') *
        (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ^ k' := by
      have h0 : (u * ((g ^ k : Y.functionFieldˣ) : Y.functionField)) ≠ 0 := h2.ne_zero
      rw [inv_pow, _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.mul_one]
    rw [e2]
    exact h.mul (unitAt_pow h2 k')

theorem pow_mem {R F : Type} [CommRing R] [Field F] {c₀ : R →+* F} {N : ℕ → Set F} (hN : GradedFam c₀ N)
    {k : ℕ} {b : F} (hb : b ∈ N k) (n : ℕ) : b ^ n ∈ N (k * n) := by
  induction n with
  | zero => simpa using hN.one
  | succ n ih => rw [pow_succ, Nat.mul_succ]; exact hN.mul _ _ _ ih _ hb

theorem exists_map_to_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  intro R F _ _ _ c₀ N hN P _ p ψ Dp hM R₁ _ ρ Y _ q θ D₁ hc hsec hcov
  haveI : IsSeparated p := hM.sep
  haveI : P.IsSeparated := sep R P p
  choose k hk b hb hy using hcov
  have hb0 : ∀ y, b y ≠ 0 := fun y h => (hy y).ne_zero (by rw [h, map_zero])
  let U : Y → Y.Opens := fun y => ⟨locus D₁ (k y) (θ (b y)), locus_open Y D₁ _ _⟩
  have hyU : ∀ y, y ∈ U y := hy
  have hgen : ∀ y, genericPoint Y ∈ U y := fun y => gen_mem (hyU y)
  have hPη : ∀ y, genericPoint P ∈ Dp (k y) (b y) := fun y => (hM.gen _ (hk y) _ (hb y)).2 (hb0 y)
  have hreg : ∀ y (s : Γ(P, Dp (k y) (b y))), ∀ z ∈ U y, RegAt z ((θ.comp ψ) (fnOf _ (hPη y) s)) := by
    intro y s z hz
    obtain ⟨m, a, ha, he⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (ψ (fnOf _ (hPη y) s))).1
      ⟨_, fun z' hz' => regAt_fnOf hz' _ s, rfl⟩
    show RegAt z (θ (ψ _))
    rw [he, map_div₀, map_pow]
    exact reg_div Y D₁ (k y) m (θ (b y)) (θ a) z (hsec _ a ha) hz
  choose f hfV hf using fun y => GlobalTheory.T.exists_hom_to_affineOpen_of_functionField_map_regular Y P (U y) (hgen y) (Dp (k y) (b y)) (hM.affine _ (hk y) _ (hb y)) (hPη y)
    (θ.comp ψ) (hreg y)
  obtain ⟨m, hmU, hmg⟩ := GlobalTheory.T.exists_glue_morphisms_integral_agree_at_genericPoint Y P U hyU f (spMap (θ.comp ψ) ≫ gp P) hf
  refine ⟨m, ?_, ⟨gp Y, Category.comp_id _, hmg⟩, ?_⟩
  · haveI := gp_dom Y
    refine ext_of_isDominant (gp Y) ?_
    rw [reassoc_of% hmg, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants P R p, ← Category.assoc, GlobalTheory.T.genericPoint_comp_structure_eq_specMap_constants Y R₁ q, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change θ (ψ (cst p x)) = cst q (ρ x)
    have h1 := congrArg (fun g => g x) hc
    have h2 := congrArg (fun g => g x) hM.const
    simp only [RingHom.comp_apply] at h1 h2
    rw [h2, h1]
  · intro k' hk' b' hb' y
    have hmy : m y ∈ Dp (k y) (b y) := by
      have h1 := hfV y ⟨y, hyU y⟩
      rw [← hmU y] at h1
      exact h1
    rw [hM.mem _ (hk y) _ (hb y) _ hmy k' hk' b' hb']
    obtain ⟨v₀, hv₀, hψ⟩ := (hM.ring _ (hk y) _ (hb y) (hb0 y) (b' ^ (k y) / b y ^ k')).2
      ⟨k', b' ^ (k y), by rw [mul_comm]; exact pow_mem hN hb' _, rfl⟩
    have hst := GlobalTheory.T.regular_and_unit_preserved_by_functionField_compatible Y P m (θ.comp ψ) hmg y v₀ (hv₀ _ hmy)
    have hl := locus_iff D₁ (hk y) (hy y) (hsec _ _ hb')
    have e : (θ.comp ψ) v₀ = θ b' ^ (k y) / θ (b y) ^ k' := by
      rw [RingHom.comp_apply, hψ, map_div₀, map_pow, map_pow]
    rw [hl, ← e]
    constructor
    · rintro ⟨v, hv, hvw⟩
      obtain rfl : v = v₀ := ψ.injective (hvw.trans hψ.symm)
      exact hst.2.2 hv
    · intro h
      exact ⟨v₀, hst.2.1 h, hψ⟩

end GlobalTheory.Desc.ToModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapIntegralSchemeToGradedProjModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_map_integral_scheme_to_graded_proj_model : ∀ (R F : Type) [CommRing R] [IsDomain R] [Field F] (c₀ : R →+* F) (N : ℕ → Set F), GradedFam c₀ N → ∀ (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp R) (ψ : P.functionField →+* F) (Dp : ℕ → F → P.Opens), IsModel c₀ N p ψ Dp → ∀ (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp R₁) (θ : F →+* Y.functionField) (D₁ : CartierDiv Y), θ.comp c₀ = (GlobalTheory.Desc.cst q).comp ρ → (∀ k, ∀ a ∈ N k, θ a ∈ Sec D₁ k) → (∀ y : Y, ∃ k, 1 ≤ k ∧ ∃ b ∈ N k, y ∈ locus D₁ k (θ b)) → ∃ m : Y ⟶ P, m ≫ p = q ≫ spMap ρ ∧ PFF (𝟙 _) m (θ.comp ψ) ∧ ∀ k, 1 ≤ k → ∀ b ∈ N k, ∀ y, m y ∈ Dp k b ↔ y ∈ locus D₁ k (θ b) := by
  first | exact @GlobalTheory.Desc.ToModel.exists_map_to_model | exact GlobalTheory.Desc.ToModel.exists_map_to_model | (intros; apply GlobalTheory.Desc.ToModel.exists_map_to_model <;> assumption)
end
