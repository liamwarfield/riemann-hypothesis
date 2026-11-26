module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralSectionEverywhereOfClosedFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  intro R _ _ _ _ M G Y α t hαt W hWa x hx hxc F _ β V hV h1 hnu
  haveI := hV
  let T := AdicCompletion (maximalIdeal V) V
  let g : V →+* T := algebraMap V T
  have hg : Function.Injective g := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  let f : G.left ⟶ Sp R := G.hom ≫ M.π
  let ρ : R →+* Γ(G.left, W) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top).hom
  let lam : Γ(G.left, W) →+* T := g.comp ((β.comp (α.app W).hom).codRestrict V h1)
  let φ : R →+* T := lam.comp ρ
  let ψ : FractionRing R →+* F :=
    β.comp ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom
  have key : ∀ r, β ((α.app W).hom (ρ r)) = ψ (algebraMap R (FractionRing R) r) := by
    intro r
    have hc : ∀ {a b : Y ⟶ Sp R} (_ : a = b), a.appLE ⊤ (α ⁻¹ᵁ W) le_top = b.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rintro _ _ rfl; rfl
    have e1 : f.appLE ⊤ W le_top ≫ α.app W = (α ≫ f).appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : α ≫ f = t ≫ jK R := by
      simp only [f]; rw [reassoc_of% hαt, M.gp_π]
    have e4 : (t ≫ jK R).appLE ⊤ (α ⁻¹ᵁ W) le_top = (jK R).appTop ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top :=
      Scheme.Hom.comp_appLE t (jK R) ⊤ (α ⁻¹ᵁ W) le_top
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W =
        CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [e1, hc e2, e4, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    change β (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W).hom r) =
      β ((CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom r)
    rw [e3]
  have hφi : Function.Injective φ := by
    intro a b hab
    have h2 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ a) = ((β.comp (α.app W).hom).codRestrict V h1) (ρ b) := hg hab
    have h3 : β ((α.app W).hom (ρ a)) = β ((α.app W).hom (ρ b)) := congrArg Subtype.val h2
    rw [key, key] at h3
    exact IsFractionRing.injective R (FractionRing R) (ψ.injective h3)
  haveI : CharZero T := charZero_of_injective_ringHom hφi
  refine ⟨T, inferInstance, inferInstance, inferInstance, lam, g, φ,
    ⟨inferInstance, inferInstance, inferInstance⟩, hg, inferInstance, fun c => rfl, hφi, ?_, ?_⟩
  · constructor
    intro r hu
    by_contra hr
    have hrm : r ∈ maximalIdeal R := hr
    have hres : (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom (ρ r)) = 0 := by
      have hb : x ∉ G.left.basicOpen (ρ r) := by
        intro hxb
        have e := Scheme.basicOpen_appLE f W ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
        rw [basicOpen_eq_of_affine (R := CommRingCat.of R) r] at e
        have h4 := ((show G.left.basicOpen (ρ r) = _ from e).le hxb).2
        have h7 : r ∉ PrimeSpectrum.asIdeal (f x) := h4
        have h6 : f x = closedPoint R := hxc
        rw [h6] at h7
        exact h7 hrm
      rw [Scheme.mem_basicOpen _ _ _ hx] at hb
      exact (IsLocalRing.residue_eq_zero_iff _).2 hb
    have h5 := hnu (ρ r) hres
    have h6 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ r) ∈ maximalIdeal V :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 (ρ r)⟩)).mp h5
    exact h6 (isUnit_of_map_unit g _ hu)
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Sp R)) hWa le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  first | exact @GlobalTheory.Mum.trait_at_closed_point | exact GlobalTheory.Mum.trait_at_closed_point | (intros; apply GlobalTheory.Mum.trait_at_closed_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem gs_eq_germ_top {Z X : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs f z U a = (Z.presheaf.germ ⊤ z trivial).hom ((f.appLE U ⊤ h).hom a) := by
  rw [gs_eq f z U (h trivial)]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf (homOfLE h) z trivial _).symm

theorem specMap_appLE_top {R Ω : Type} [CommRing R] [CommRing Ω] (f : R →+* Ω) (V : (Sp R).Opens) (hV : ⊤ ≤ V)
    (h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ V) (a : Γ(Sp R, V)) :
    ((Spec.map (CommRingCat.ofHom f)).appLE V ⊤ h).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (((Sp R).presheaf.map (homOfLE hV).op).hom a))) := by
  have e1 := Scheme.Hom.map_appLE (Spec.map (CommRingCat.ofHom f)) (U := ⊤) (U' := V) (V := ⊤) (fun _ _ => trivial) (homOfLE hV).op
  have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  rw [← e1]
  have e3 : (Spec.map (CommRingCat.ofHom f)).appLE ⊤ ⊤ (fun _ _ => trivial) = (Spec.map (CommRingCat.ofHom f)).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have e4 : ∀ x, ((Spec.map (CommRingCat.ofHom f)).appTop).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x)) := fun x => by
    have := congrArg (fun t => t.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← this, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [CommRingCat.hom_comp, RingHom.comp_apply, e3, e4]

theorem fromSpec_appLE_self {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem ΓSpecIso_hom_inv_apply (R : CommRingCat.{0}) (a : R) :
    (Scheme.ΓSpecIso R).hom.hom ((Scheme.ΓSpecIso R).inv.hom a) = a := by
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem gs_specMap_comp {R Ω : Type} [CommRing R] [CommRing Ω] {X : Scheme.{0}} (f : R →+* Ω) (g : Sp R ⟶ X)
    (z : Sp Ω) (U : X.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(X, U)) :
    gs (Spec.map (CommRingCat.ofHom f) ≫ g) z U a = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        ((g.appLE U ⊤ hg).hom a)))) := by
  have h : ⊤ ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ (g ⁻¹ᵁ U) := fun x _ => hg trivial
  rw [← gs_pull (Spec.map (CommRingCat.ofHom f)) g z U (hg trivial) a, gs_eq_germ_top _ z _ h,
    specMap_appLE_top f _ hg h]
  rfl

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem chartVal_mem_range_of_agree : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  intro X S Y gX L hL α k s j W hW hWa hαW T _ lam W' _ io σ hσ Ω _ ψ e hψ
  have hq : (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) ≫ gX =
      𝟙 (Sp W') ≫ (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.id_comp]
    simp only [spMap, Category.assoc]
  let q'' := pullback.lift (Spec.map (CommRingCat.ofHom (io.comp lam)) ≫ hWa.fromSpec) (𝟙 (Sp W')) hq
  let P : Sp Ω ⟶ _ := Spec.map (CommRingCat.ofHom e) ≫ q''
  let pY : Sp Ω ⟶ Y := Spec.map (CommRingCat.ofHom ψ) ≫ hαW.fromSpec
  have hring : α.appLE W (α ⁻¹ᵁ W) le_rfl ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (e.comp (io.comp lam)) := by
    ext c
    rw [Scheme.Hom.appLE_eq_app]
    exact hψ c
  have hA : P ≫ pullback.fst _ _ = pY ≫ α := by
    simp only [P, pY, q'', Category.assoc, pullback.lift_fst]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec α hWa hαW le_rfl, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
      hring, ← CommRingCat.ofHom_comp]
  have hαmem : ∀ x, hαW.fromSpec x ∈ α ⁻¹ᵁ W := fun x => by
    show _ ∈ ((α ⁻¹ᵁ W : Y.Opens) : Set Y)
    rw [← hαW.range_fromSpec]
    exact ⟨x, rfl⟩
  have hWmem : ∀ x, hWa.fromSpec x ∈ W := fun x => by
    show _ ∈ ((W : X.Opens) : Set X)
    rw [← hWa.range_fromSpec]
    exact ⟨x, rfl⟩
  obtain ⟨z⟩ : Nonempty (Sp Ω) := ⟨IsLocalRing.closedPoint Ω⟩
  have hz : (pY ≫ α) z ∈ L.U j := hW (hαmem _)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := Unit) (fun _ => pY ≫ α) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hz)
  have hag := hσ (Sp Ω) P pY hA z J hJ
  have hl : sval s pY z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ (chartVal L α s j W hW))) := by
    rw [sval_of s pY z J (fun _ => j) (fun _ => hJj ()),
      ← gs_res pY z (locInt_le_chart L α j W hW) (hαmem _) (s.f (fun _ => j))]
    rw [gs_specMap_comp ψ hαW.fromSpec z (α ⁻¹ᵁ W) hαW.fromSpec_preimage_self.ge]
    rw [fromSpec_appLE_self hαW]
    exact congrArg (fun t => ((Sp Ω).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (ψ t)))
      (ΓSpecIso_hom_inv_apply _ _)
  have hq'' : ⊤ ≤ q'' ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => pullback.fst _ _) (fun _ => j) := fun x _ =>
    Set.mem_iInter.2 fun _ => hW (by
      show (q'' ≫ pullback.fst _ _) x ∈ W
      rw [pullback.lift_fst]
      exact hWmem _)
  have hr : sval σ P z J = ((Sp Ω).presheaf.germ ⊤ z trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (e ((Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom
        ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j)))))) := by
    rw [sval_of σ P z J (fun _ => j) (fun _ => by rw [hA]; exact hJj ())]
    exact gs_specMap_comp e q'' z _ hq'' _
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of W')).hom.hom ((q''.appLE _ ⊤ hq'').hom (σ.f (fun _ => j))),
    ((((Sp Ω).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom).injective) ?_⟩
  simp only [RingHom.comp_apply]
  rw [← hl, ← hr, hag]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemRangeOfAgreeTraitExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValue_mem_range_of_agree_traitExtension : ∀ (X S Y : Scheme.{0}) (gX : X ⟶ S) (L : LB X), L.IsLB → ∀ (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j) (hWa : IsAffineOpen W), IsAffineOpen (α ⁻¹ᵁ W) → ∀ (T : Type) [CommRing T] (lam : Γ(X, W) →+* T) (W' : Type) [CommRing W'] (io : T →+* W') (σ : SecK L (pullback.fst gX (spMap io ≫ Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ gX)) k), Agree L σ s → ∀ (Ω : Type) [Field Ω] (ψ : Γ(Y, α ⁻¹ᵁ W) →+* Ω) (e : W' →+* Ω), (∀ c, ψ ((α.app W).hom c) = e (io (lam c))) → ∃ w : W', ψ (chartVal L α s j W hW) = e w := by
  first | exact @GlobalTheory.Mum.chartVal_mem_range_of_agree | exact GlobalTheory.Mum.chartVal_mem_range_of_agree | (intros; apply GlobalTheory.Mum.chartVal_mem_range_of_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_valuationSubring_of_image : ∀ (F : Type) [Field F] (V : ValuationSubring F) (T : Type) [CommRing T] [IsLocalRing T] (g : V →+* T), IsLocalHom g → ∀ (W' : Type) [CommRing W'] [IsDomain W'] [IsLocalRing W'] (io : T →+* W'), Function.Injective io → io.Finite → ∀ (Ω : Type) [Field Ω] (iF : F →+* Ω) (e : W' →+* Ω), Function.Injective e → (∀ v : V, iF v = e (io (g v))) → ∀ (y : F) (w : W'), iF y = e w → y ∈ V := by
  intro F _ V T _ _ g hg W' _ _ _ io hioi hiof Ω _ iF e he hi y w hy
  haveI : IsLocalHom io := RingHom.IsIntegral.isLocalHom hiof.to_isIntegral hioi
  by_contra hyV
  have hy0 : y ≠ 0 := fun h => hyV (h ▸ V.zero_mem)
  have hinv : y⁻¹ ∈ V := (V.mem_or_inv_mem y).resolve_left hyV
  let u : V := ⟨y⁻¹, hinv⟩
  have hu : ¬ IsUnit u := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have h' : y⁻¹ * (v : F) = 1 := by simpa [u] using congrArg Subtype.val hv
    have hv' : (v : F) = y := by
      calc (v : F) = y * (y⁻¹ * v) := by rw [← _root_.mul_assoc, mul_inv_cancel₀ hy0, _root_.one_mul]
        _ = y := by rw [h', _root_.mul_one]
    exact hyV (hv' ▸ v.2)
  have hprod : io (g u) * w = 1 := by
    apply he
    rw [map_mul, map_one, ← hi u, ← hy, ← map_mul]
    simp [u, inv_mul_cancel₀ hy0]
  exact hu ((isUnit_map_iff g u).1 ((isUnit_map_iff io (g u)).1 (IsUnit.of_mul_eq_one _ hprod)))

theorem chartVal_mem_of_dominates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hx hcl F _ β V hV h1 h2
  obtain ⟨T, _, _, _, lam, g, φ, hT, hgi', hgl, hgl', hφi, hφl, hξ⟩ :=
    GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait R M G Y α t hpb.w W hWa x hx hcl F β V hV h1 h2
  obtain ⟨W', _, _, _, io, σ, hW', hioi, hiof, hag⟩ := hs T hT φ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) hφi hφl hξ
  let e : W' →+* FractionRing W' := algebraMap W' (FractionRing W')
  have he : Function.Injective e := IsFractionRing.injective W' (FractionRing W')
  have hgg : Function.Injective ((e.comp io).comp g) := he.comp (hioi.comp hgi')
  let iF : F →+* FractionRing W' := IsFractionRing.lift hgg
  have hi : ∀ v : V, iF v = e (io (g v)) := fun v => IsFractionRing.lift_algebraMap hgg v
  have hαW := GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange R M G Y α t hpb W hWa
  obtain ⟨w, hw⟩ := GlobalTheory.T.chartValue_mem_range_of_agree_traitExtension G.left M.S Y G.hom L hL α k s j W hW hWa hαW T lam W' io σ hag (FractionRing W') (iF.comp β) e
    (fun c => (hi ⟨_, h1 c⟩).trans (by rw [hgl' c]))
  have hw' : iF (β (chartVal L α s j W hW)) = e w := hw
  exact mem_valuationSubring_of_image F V T g hgl W' io hioi hiof (FractionRing W') iF e he hi (β (chartVal L α s j W hW)) w hw'

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueMemDominatingValuationSubringStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValue_mem_dominating_valuationSubring : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (hW : W ≤ L.U j), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → ∀ (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β ((α.app W).hom c) ∈ V) → (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → β (chartVal L α s j W hW) ∈ V := by
  first | exact @GlobalTheory.Mum.chartVal_mem_of_dominates | exact GlobalTheory.Mum.chartVal_mem_of_dominates | (intros; apply GlobalTheory.Mum.chartVal_mem_of_dominates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericChartFunctionsFractionsSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericChartFunctionsFractionsSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.Mum

theorem injective_gp_app {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) :
    Function.Injective (M.gp.app U).hom := by
  haveI := M.integral
  haveI := M.dominant
  by_cases hU : (U : Set M.S).Nonempty
  · obtain ⟨x, hx⟩ := M.gp.denseRange.exists_mem_open U.isOpen hU
    have h1 := germ_injective_of_isIntegral (X := M.S) (M.gp x) hx
    have h2 := M.gp.germ_stalkMap U x hx
    have hcl : closure {M.gp x} = (Set.univ : Set M.S) := by
      have hd := M.gp.denseRange
      have hr : Set.range M.gp = {M.gp x} := by
        ext y; constructor
        · rintro ⟨z, rfl⟩
          haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
          rw [Subsingleton.elim z x]; rfl
        · rintro rfl; exact ⟨x, rfl⟩
      rw [← hr]; exact hd.closure_range
    have hF := isField_stalk_of_closure_mem_irreducibleComponents M.S (M.gp x)
      (by rw [hcl]; simp [irreducibleComponents_eq_singleton])
    letI := hF.toField
    have h3 : Function.Injective (M.gp.stalkMap x).hom := RingHom.injective _
    intro a b h
    apply h1
    apply h3
    have ea := congrArg (fun φ => φ.hom a) h2
    have eb := congrArg (fun φ => φ.hom b) h2
    simp only [CommRingCat.comp_apply] at ea eb
    rw [ea, eb, h]
  · have : U = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => hU ⟨y, hy⟩
    subst this
    intro a b _; exact Subsingleton.elim a b

def fracRes (R : Type) [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) : R →+* Γ(Sp (FractionRing R), V) :=
  ((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom).comp (algebraMap R (FractionRing R)))

theorem isUnit_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens) {r : R} (hr : r ≠ 0) :
    IsUnit (fracRes R V r) := by
  have : IsUnit (algebraMap R (FractionRing R) r) :=
    Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
  exact this.map (((Sp (FractionRing R)).presheaf.map (homOfLE le_top).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom)

theorem exists_mul_fracRes {R : Type} [CommRing R] [IsDomain R] (V : (Sp (FractionRing R)).Opens)
    (k : Γ(Sp (FractionRing R), V)) : ∃ a r : R, r ≠ 0 ∧ k * fracRes R V r = fracRes R V a := by
  haveI : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum _))
  by_cases h : (V : Set (Sp (FractionRing R))).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hV : V = ⊤ := by
      ext y
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      exact Subsingleton.elim x y ▸ hx
    subst hV
    obtain ⟨⟨a, r⟩, hr⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k)
    refine ⟨a, r, nonZeroDivisors.ne_zero r.2, ?_⟩
    have hmap : ((Sp (FractionRing R)).presheaf.map (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)).op) = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : (Sp (FractionRing R)).Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      simp
    simp only [fracRes, RingHom.coe_comp, Function.comp_apply, hmap, CommRingCat.hom_id, RingHom.id_apply]
    have hk : k = (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom k) := by
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [hk, ← map_mul, ← hr, IsLocalization.mk'_spec]
  · have hV : V = ⊥ := by
      ext y; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hy => h ⟨y, hy⟩
    subst hV
    exact ⟨0, 1, one_ne_zero, Subsingleton.elim _ _⟩

theorem appLE_jK_eq_fracRes {R : Type} [CommRing R] [IsDomain R] (f : Sp (FractionRing R) ⟶ Sp R) (hf : f = jK R)
    (V : (Sp (FractionRing R)).Opens) (e : V ≤ f ⁻¹ᵁ ⊤) (x : R) :
    (f.appLE ⊤ V e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = fracRes R V x := by
  subst hf
  have h := congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [fracRes, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE, CommRingCat.comp_apply]
  rw [h]
  rfl

theorem gp_app_fracRes {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (U : M.S.Opens) (e : U ≤ M.π ⁻¹ᵁ ⊤) (r : R) :
    (M.gp.app U).hom ((M.π.appLE ⊤ U e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      fracRes R (M.gp ⁻¹ᵁ U) r := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact appLE_jK_eq_fracRes _ M.gp_π _ _ r

theorem injective_and_exists_frac_genericChart : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens) (U : M.S.Opens), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → Function.Injective (α.app W).hom ∧ ∀ b : Γ(Y, α ⁻¹ᵁ W), ∃ c s : Γ(G.left, W), IsUnit ((α.app W).hom s) ∧ b * (α.app W).hom s = (α.app W).hom c := by
  intro R _ _ M G hG Y α t hpb W U hWU hW hU
  have hV : IsAffineOpen (M.gp ⁻¹ᵁ U) := isAffineOpen_Sp_field _ _
  have hle := locInt_le_gen G.hom α t M.gp hpb.w W U hWU
  have hUY : α ⁻¹ᵁ W = α ⁻¹ᵁ W ⊓ t ⁻¹ᵁ (M.gp ⁻¹ᵁ U) := (inf_eq_left.2 hle).symm
  have po := (isIso_pushoutSection_iff hpb (US := U) (UT := M.gp ⁻¹ᵁ U) (UX := W) le_rfl hWU hUY).mp
    (isIso_pushoutSection_of_isAffineOpen hpb le_rfl hWU hUY hU hV hW)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at po
  letI : Algebra Γ(M.S, U) Γ(G.left, W) := (G.hom.appLE U W hWU).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) := (M.gp.app U).hom.toAlgebra
  letI : Algebra Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  letI : Algebra Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    (t.appLE (M.gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) hle).hom.toAlgebra
  letI : Algebra Γ(M.S, U) Γ(Y, α ⁻¹ᵁ W) := (G.hom.appLE U W hWU ≫ α.app W).hom.toAlgebra
  haveI : IsScalarTower Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom po.w)
  haveI : Algebra.IsPushout Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) :=
    CommRingCat.isPushout_iff_isPushout.mp po
  haveI : Algebra.Smooth Γ(M.S, U) Γ(G.left, W) :=
    HasRingHomProperty.appLE @AlgebraicGeometry.Smooth G.hom hG ⟨U, hU⟩ ⟨W, hW⟩ hWU
  haveI : Module.Flat Γ(M.S, U) Γ(G.left, W) := inferInstance
  let e := Algebra.IsPushout.equiv Γ(M.S, U) Γ(G.left, W) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W)
  have he1 : ∀ c : Γ(G.left, W), e (c ⊗ₜ 1) = (α.app W).hom c := fun c => by
    rw [Algebra.IsPushout.equiv_tmul, map_one, _root_.mul_one]; rfl
  have hinc := Algebra.TensorProduct.includeLeft_injective (S := Γ(M.S, U)) (R := Γ(M.S, U))
    (A := Γ(G.left, W)) (B := Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U)) (injective_gp_app M U)
  refine ⟨fun a b h => hinc (e.injective ?_), fun b => ?_⟩
  · change e (a ⊗ₜ 1) = e (b ⊗ₜ 1)
    rw [he1, he1, h]

  have eU : U ≤ M.π ⁻¹ᵁ ⊤ := fun x _ => trivial
  let σ : R →+* Γ(G.left, W) := (algebraMap Γ(M.S, U) Γ(G.left, W)).comp
    ((M.π.appLE ⊤ U eU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  have hσ : ∀ r : R, (α.app W).hom (σ r) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (fracRes R (M.gp ⁻¹ᵁ U) r) := fun r => by
    rw [← gp_app_fracRes M U eU r]
    change algebraMap Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) Γ(G.left, W) _) =
      algebraMap Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) (algebraMap Γ(M.S, U) _ _)
    exact (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) _).symm.trans
      (IsScalarTower.algebraMap_apply Γ(M.S, U) Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U) Γ(Y, α ⁻¹ᵁ W) _)
  have key : ∀ y : Γ(G.left, W) ⊗[Γ(M.S, U)] Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U),
      ∃ (c : Γ(G.left, W)) (r : R), r ≠ 0 ∧ e y * (α.app W).hom (σ r) = (α.app W).hom c := by
    intro y
    induction y with
    | tmul c k =>
      obtain ⟨a, r, hr, hk⟩ := exists_mul_fracRes (M.gp ⁻¹ᵁ U) k
      refine ⟨c * σ a, r, hr, ?_⟩
      rw [Algebra.IsPushout.equiv_tmul, hσ, map_mul, hσ, _root_.mul_assoc, ← map_mul, hk]
      rfl
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨c₁, r₁, hr₁, e₁⟩ := h₁
      obtain ⟨c₂, r₂, hr₂, e₂⟩ := h₂
      refine ⟨c₁ * σ r₂ + c₂ * σ r₁, r₁ * r₂, mul_ne_zero hr₁ hr₂, ?_⟩
      rw [map_add (f := _), add_mul, map_mul σ, map_mul, map_add (f := _), map_mul, map_mul, ← e₁, ← e₂]
      ring
  obtain ⟨c, r, hr, hc⟩ := key (e.symm b)
  refine ⟨c, σ r, ?_, ?_⟩
  · rw [hσ]; exact (isUnit_fracRes _ hr).map _
  · rw [← hc, e.apply_symm_apply]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericChartFunctionsFractionsSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_chart_functions_fractions_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (W : G.left.Opens) (U : M.S.Opens), W ≤ G.hom ⁻¹ᵁ U → IsAffineOpen W → IsAffineOpen U → Function.Injective (α.app W).hom ∧ ∀ b : Γ(Y, α ⁻¹ᵁ W), ∃ c s : Γ(G.left, W), IsUnit ((α.app W).hom s) ∧ b * (α.app W).hom s = (α.app W).hom c := by
  first | exact @GlobalTheory.Mum.injective_and_exists_frac_genericChart | exact GlobalTheory.Mum.injective_and_exists_frac_genericChart | (intros; apply GlobalTheory.Mum.injective_and_exists_frac_genericChart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumInt

theorem isIntegral_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S),
    Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  intro R _ _ M G hsm hgi _
  haveI := M.integral
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  haveI : IrreducibleSpace G.left := GeometricallyIrreducible.irreducibleSpace G.hom G.hom.isOpenMap
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end GlobalTheory.MumInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfSmoothGeomIrreducibleOverModificatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), Smooth G.hom → GeometricallyIrreducible G.hom → Nonempty G.left → IsIntegral G.left := by
  first | exact @GlobalTheory.MumInt.isIntegral_of_smooth | exact GlobalTheory.MumInt.isIntegral_of_smooth | (intros; apply GlobalTheory.MumInt.isIntegral_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isLocallyNoetherian_of_smooth_over_modif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  intro R _ _ _ M G hG
  haveI : IsLocallyNoetherian (Sp R) := inferInstance
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI := hG
  exact LocallyOfFiniteType.isLocallyNoetherian G.hom

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianOfSmoothOverModificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → IsLocallyNoetherian G.left := by
  first | exact @GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | exact GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif | (intros; apply GlobalTheory.Mum.isLocallyNoetherian_of_smooth_over_modif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Mum

theorem intAt_of_integral_mul_basicOpen : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  intro X Y L α k s j W hW hWa x d hx hint
  have hle : X.basicOpen d ≤ W := X.basicOpen_le d
  have hW' : X.basicOpen d ≤ L.U j := hle.trans hW
  refine ⟨j, X.basicOpen d, hW', hx, hWa.basicOpen d, ?_⟩
  set ρX := (X.presheaf.map (homOfLE hle).op).hom with hρX
  set ρY := (Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom with hρY
  have hnat : ∀ r, ρY ((α.app W).hom r) = (α.app (X.basicOpen d)).hom (ρX r) := by
    intro r
    have := congrArg (fun g => g.hom r) (Scheme.Hom.naturality α (homOfLE hle).op)
    simpa [ρX, ρY] using this.symm
  have hcv : chartVal L α s j (X.basicOpen d) hW' = ρY (chartVal L α s j W hW) := by
    simp only [chartVal, ρY]
    change _ = (Y.presheaf.map (homOfLE (locInt_le_chart L α j W hW)).op ≫
      Y.presheaf.map ((TopologicalSpace.Opens.map α.base).map (homOfLE hle)).op).hom _
    rw [← Functor.map_comp]
    rfl

  have hint' : (α.app (X.basicOpen d)).hom.IsIntegralElem (ρY ((α.app W).hom d * chartVal L α s j W hW)) := by
    obtain ⟨p, hp, hp0⟩ := hint
    refine ⟨p.map ρX, hp.map ρX, ?_⟩
    rw [Polynomial.eval₂_map]
    have : ((α.app (X.basicOpen d)).hom.comp ρX) = ρY.comp (α.app W).hom := by
      ext r; exact (hnat r).symm
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  obtain ⟨u, hu⟩ : IsUnit (ρX d) := X.toRingedSpace.isUnit_res_basicOpen d
  have hmul : ρY ((α.app W).hom d * chartVal L α s j W hW) =
      (α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW' := by
    rw [map_mul, hnat, hcv]
    congr 2
    exact hu.symm
  rw [hmul] at hint'
  have key : chartVal L α s j (X.basicOpen d) hW' =
      (α.app (X.basicOpen d)).hom ((u⁻¹ : (Γ(X, X.basicOpen d))ˣ) : Γ(X, X.basicOpen d)) *
        ((α.app (X.basicOpen d)).hom (u : Γ(X, X.basicOpen d)) * chartVal L α s j (X.basicOpen d) hW') := by
    rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
  rw [key]
  exact RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) hint'

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtBasicOpenOfIntegralMulChartValueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAt_basicOpen_of_integral_mul_chartValue : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → ∀ (x : X) (d : Γ(X, W)), x ∈ X.basicOpen d → (α.app W).hom.IsIntegralElem ((α.app W).hom d * chartVal L α s j W hW) → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_of_integral_mul_basicOpen | exact GlobalTheory.Mum.intAt_of_integral_mul_basicOpen | (intros; apply GlobalTheory.Mum.intAt_of_integral_mul_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuation
open IsLocalRing

namespace GlobalTheory

theorem exists_mul_isIntegralElem_of_forall_discreteValuationSubring :
    ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B),
      Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) →
      ∀ (p : Ideal C), p.IsPrime → ∀ f : B,
        (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V →
          (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) →
        ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  intro C B _ _ _ _ e he hloc p hp f hf
  haveI : Nontrivial B := ⟨⟨e 0, e 1, fun h => zero_ne_one (he h)⟩⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab => by
    obtain ⟨c₁, s₁, u₁, h₁⟩ := hloc a
    obtain ⟨c₂, s₂, u₂, h₂⟩ := hloc b
    have hc : c₁ * c₂ = 0 := he (by
      rw [map_mul, ← h₁, ← h₂, map_zero,
        show a * e s₁ * (b * e s₂) = (a * b) * (e s₁ * e s₂) by ring, hab, zero_mul])
    rcases mul_eq_zero.1 hc with h | h
    · left
      rw [h, map_zero] at h₁
      exact u₁.mul_left_eq_zero.1 h₁
    · right
      rw [h, map_zero] at h₂
      exact u₂.mul_left_eq_zero.1 h₂⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  let L := FractionRing B
  let β : B →+* L := algebraMap B L
  have hβ : Function.Injective β := IsFractionRing.injective B L
  letI : Algebra C L := (β.comp e).toAlgebra
  have hCL : ∀ c, algebraMap C L c = β (e c) := fun _ => rfl
  have hinj : Function.Injective (algebraMap C L) := hβ.comp he
  haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).2 hinj
  have hne : ∀ s : C, IsUnit (e s) → β (e s) ≠ 0 := fun s hs => ((hs.map β).ne_zero)
  haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z => by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    obtain ⟨cx, sx, ux, hx⟩ := hloc x
    obtain ⟨cy, sy, uy, hy'⟩ := hloc y
    refine ⟨cx * sy, cy * sx, ?_⟩
    have hy0 : β y ≠ 0 := by
      rw [map_ne_zero_iff _ hβ]; exact nonZeroDivisors.ne_zero hy
    show β x / β y = _
    simp only [hCL, map_mul]
    rw [← hx, ← hy']
    simp only [map_mul]
    rw [div_eq_div_iff hy0 (mul_ne_zero (mul_ne_zero hy0 (hne sy uy)) (hne sx ux))]
    ring
  let Cp := Localization.AtPrime p
  haveI : IsNoetherianRing Cp := IsLocalization.isNoetherianRing p.primeCompl Cp inferInstance
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap C L y) := fun y => by
    refine isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 ?_)
    intro h0
    exact y.2 (h0 ▸ p.zero_mem)
  letI : Algebra Cp L := (IsLocalization.lift (M := p.primeCompl) (S := Cp) hunit).toAlgebra
  haveI : IsScalarTower C Cp L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  haveI : IsFractionRing Cp L := IsFractionRing.isFractionRing_of_isLocalization p.primeCompl Cp L
    p.primeCompl_le_nonZeroDivisors
  haveI : Algebra.EssFiniteType Cp L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors Cp)
  have hint : IsIntegral Cp (β f) := by
    by_contra hn
    obtain ⟨V, hV, hd, hfV⟩ := exists_discreteValuationSubring_dominating_notMem hn
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
    apply hfV
    refine hf L β V hV (fun c => ?_) (fun c hc => ?_)
    · have := h1 (algebraMap C Cp c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · have := h2 (algebraMap C Cp c)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Cp p c).2 hc)
      rwa [← IsScalarTower.algebraMap_apply] at this
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl (β f) hint
  refine ⟨d, hd, ?_⟩
  obtain ⟨q, hq, hq0⟩ := hdi
  refine ⟨q, hq, hβ ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hq0, Submonoid.smul_def, Algebra.smul_def, hCL, map_mul]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulIsIntegralElemOfForallDiscreteValuationStatement
open IsLocalRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr : ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B), Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) → ∀ (p : Ideal C), p.IsPrime → ∀ f : B, (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) → ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  first | exact @GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | exact GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring | (intros; apply GlobalTheory.exists_mul_isIntegralElem_of_forall_discreteValuationSubring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraits
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_chart_affineOpen {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (L : LB G.left)
    (hL : L.IsLB) (x : G.left) : ∃ (j : L.ι) (U : M.S.Opens) (W : G.left.Opens) (_ : W ≤ L.U j) (_ : W ≤ G.hom ⁻¹ᵁ U),
      x ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen U := by
  obtain ⟨j, hj⟩ := exists_chart hL x
  obtain ⟨U, hUa, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hWa, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  exact ⟨j, U, W, fun y hy => (hWle hy).1, fun y hy => (hWle hy).2, hxW, hWa, hUa⟩

theorem intAt_closed_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs x hx
  obtain ⟨j, U, W, hW, hWU, hxW, hWa, hUa⟩ := exists_chart_affineOpen M G L hL x
  obtain ⟨hinj, hloc⟩ := GlobalTheory.T.generic_chart_functions_fractions_smooth R M G hsm Y α t hpb W U hWU hWa hUa
  haveI : IsIntegral G.left := GlobalTheory.T.isIntegral_of_smooth_geomIrreducible_over_modification R M G hsm hgi ⟨x⟩
  haveI : IsLocallyNoetherian G.left := GlobalTheory.T.isLocallyNoetherian_of_smooth_over_modification R M G hsm
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  haveI : IsNoetherianRing Γ(G.left, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
  let p : Ideal Γ(G.left, W) := RingHom.ker ((G.left.residue x).hom.comp (G.left.presheaf.germ W x hxW).hom)
  obtain ⟨d, hd, hi⟩ := GlobalTheory.T.exists_mul_isIntegralElem_of_forall_dvr Γ(G.left, W) Γ(Y, α ⁻¹ᵁ W) (α.app W).hom hinj hloc p (RingHom.ker_isPrime _)
    (chartVal L α s j W hW) (fun F _ β V hV h1 h2 =>
      GlobalTheory.T.chartValue_mem_dominating_valuationSubring R M G hsm hqc hgi L hL Y α t hpb k s hs j U W hW hWU hWa hUa x hxW hx F β V hV h1
        (fun c hc => h2 c (RingHom.mem_ker.2 hc)))
  refine GlobalTheory.T.integralAt_basicOpen_of_integral_mul_chartValue L α k s j W hW hWa x d ?_ hi
  rw [Scheme.mem_basicOpen _ _ _ hxW]
  have : (G.left.residue x).hom ((G.left.presheaf.germ W x hxW).hom d) ≠ 0 := fun h => hd (RingHom.mem_ker.2 h)
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 this

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_closed_of_traitReg | exact GlobalTheory.Mum.intAt_closed_of_traitReg | (intros; apply GlobalTheory.Mum.intAt_closed_of_traitReg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraits
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs
  have h4 := GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb k s hs
  have h5 := GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre R M G hsm hqc hgi L hL Y α t hpb k s h4
  intro j W U hW hWU hWa hUa
  exact GlobalTheory.T.integral_element_affine_section_generated R M G hsm Y α t hpb W U hWU hWa hUa _
    (GlobalTheory.T.chartValue_isIntegral_of_integral_at_points L α k s j W hW hWa (GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification R M G Y α t hpb W hWa) (fun x _ => h5 x))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyIntegral_of_regular_at_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  first | exact @GlobalTheory.Mum.locInt_of_traitReg | exact GlobalTheory.Mum.locInt_of_traitReg | (intros; apply GlobalTheory.Mum.locInt_of_traitReg <;> assumption)
end
