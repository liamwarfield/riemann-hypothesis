module

public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatLocallyFreeAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancel

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatible
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.FinFlatNorm

open TopologicalSpace GlobalTheory.FiniteAmple GlobalTheory.LB ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LBGerm
open GlobalTheory.FlatNorm (nm nm_of_isPushout isUnit_of_nm exists_preimage_le)

variable {X Y : Scheme.{0}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]

theorem exists_finFree_app_of_finitePresentation {x : X} {U : X.Opens} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ FinFree (π.app V).hom := by
  obtain ⟨V0, hV0, hxV0, hV0U⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  have hfin : (π.app V0).hom.Finite := IsFinite.finite_app π V0 hV0
  have hfl : (π.app V0).hom.Flat := by
    have := HasRingHomProperty.appLE @Flat π inferInstance ⟨V0, hV0⟩ ⟨π ⁻¹ᵁ V0, hV0.preimage π⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hfp : (π.app V0).hom.FinitePresentation := by
    have := HasRingHomProperty.appLE @LocallyOfFinitePresentation π inferInstance ⟨V0, hV0⟩
      ⟨π ⁻¹ᵁ V0, hV0.preimage π⟩ le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  obtain ⟨r, hr, H⟩ := GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd.exists_finFree_away_of_finitePresentation hfin hfl hfp
    (hV0.primeIdealOf ⟨x, hxV0⟩)
  refine ⟨X.basicOpen r, hV0.basicOpen r, ?_, (X.basicOpen_le r).trans hV0U, ?_⟩
  · have h1 : hV0.primeIdealOf ⟨x, hxV0⟩ ∈
        (TopologicalSpace.Opens.map hV0.fromSpec.base).obj (X.basicOpen r) := by
      rw [hV0.fromSpec_preimage_basicOpen]
      exact hr
    have h2 : hV0.fromSpec (hV0.primeIdealOf ⟨x, hxV0⟩) ∈ X.basicOpen r := h1
    rwa [hV0.fromSpec_primeIdealOf] at h2
  · exact H (isPushout_app π hV0 (hV0.basicOpen r) (X.basicOpen_le r))
      (RingedSpace.isUnit_res_basicOpen _ r)

abbrev FreeOpen (V : X.Opens) : Type := {W : X.Opens // IsAffineOpen W ∧ W ≤ V ∧ FinFree (π.app W).hom}

theorem le_iSup_freeOpen (V : X.Opens) : V ≤ ⨆ W : FreeOpen π V, W.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWV, hF⟩, hxW⟩

theorem ext_freeOpen {V : X.Opens} {a b : Γ(X, V)}
    (h : ∀ W : FreeOpen π V, resG X W.2.2.1 a = resG X W.2.2.1 b) : a = b := by
  refine TopCat.Presheaf.section_ext X.sheaf V a b fun x hx => ?_
  obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp (le_iSup_freeOpen π V hx)
  have e := congrArg (X.presheaf.germ W.1 x hxW).hom (h W)
  simp [resG] at e
  exact e

omit [Flat π] [LocallyOfFinitePresentation π] in
theorem resG_nm {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W) (h : W ≤ V)
    (hF : FinFree (π.app V).hom) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (nm (π.app V).hom b) = nm (π.app W).hom (resG Y (π.preimage_mono h) b) := by
  exact (nm_of_isPushout (isPushout_app π hV hW h) hF b).symm

private theorem resG_nm_app_eq_nm_app_of_le_freeOpen {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (k : FreeOpen π V) {W' : X.Opens}
    (hW' : IsAffineOpen W') (h : W' ≤ k.1) :
    resG X h (nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) =
      nm (π.app W').hom (resG Y (π.preimage_mono (h.trans k.2.2.1)) b) := by
  rw [resG_nm π k.2.1 hW' h k.2.2.2, resG_resG]

theorem exists_normFun (V : X.Opens) (b : Γ(Y, π ⁻¹ᵁ V)) : ∃ a : Γ(X, V), ∀ W : FreeOpen π V,
    resG X W.2.2.1 a = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  refine exists_fun_of_cover (fun k : FreeOpen π V => k.1) (fun k => k.2.2.1) (le_iSup_freeOpen π V)
    (fun k => nm (π.app k.1).hom (resG Y (π.preimage_mono k.2.2.1) b)) fun k l => ?_
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_resG, resG_nm_app_eq_nm_app_of_le_freeOpen π b k W'.2.1, resG_nm_app_eq_nm_app_of_le_freeOpen π b l W'.2.1]

def normFun (V : X.Opens) : Γ(Y, π ⁻¹ᵁ V) →* Γ(X, V) where
  toFun b := (exists_normFun π V b).choose
  map_one' := ext_freeOpen π fun W => by
    rw [(exists_normFun π V 1).choose_spec W, map_one, map_one, map_one]
  map_mul' a b := ext_freeOpen π fun W => by
    rw [(exists_normFun π V _).choose_spec W, map_mul, map_mul, map_mul,
      (exists_normFun π V a).choose_spec W, (exists_normFun π V b).choose_spec W]

theorem resG_normFun_free {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) (W : FreeOpen π V) :
    resG X W.2.2.1 (normFun π V b) = nm (π.app W.1).hom (resG Y (π.preimage_mono W.2.2.1) b) := by
  exact (exists_normFun π V b).choose_spec W

theorem resG_normFun {V W : X.Opens} (h : W ≤ V) (b : Γ(Y, π ⁻¹ᵁ V)) :
    resG X h (normFun π V b) = normFun π W (resG Y (π.preimage_mono h) b) := by
  refine ext_freeOpen π fun W' => ?_
  rw [resG_resG, resG_normFun_free π b ⟨W'.1, W'.2.1, W'.2.2.1.trans h, W'.2.2.2⟩,
    resG_normFun_free π _ W', resG_resG]

private theorem basicOpen_resG_eq_inf_basicOpen {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U)) :
    Z.basicOpen (resG Z h f) = V ⊓ Z.basicOpen f :=
  Z.basicOpen_res f (homOfLE h).op

private theorem isUnit_resG_of_le_basicOpen' {Z : Scheme.{0}} {U V : Z.Opens} (h : V ≤ U) (f : Γ(Z, U))
    (hV : V ≤ Z.basicOpen f) : IsUnit (resG Z h f) := by
  rw [← resG_resG (Z.basicOpen_le f) hV f]
  exact (RingedSpace.isUnit_res_basicOpen _ f).map (resG Z hV)

theorem mem_basicOpen_normFun {V : X.Opens} (b : Γ(Y, π ⁻¹ᵁ V)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (normFun π V b) ↔ ∀ y, π y = x → y ∈ Y.basicOpen b := by
  obtain ⟨W, hW, hxW, hWV, hF⟩ := exists_finFree_app_of_finitePresentation π hx
  have e0 := resG_normFun_free π b ⟨W, hW, hWV, hF⟩
  have key : x ∈ X.basicOpen (normFun π V b) ↔
      x ∈ X.basicOpen (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b)) := by
    rw [← e0, basicOpen_resG_eq_inf_basicOpen]
    exact ⟨fun h => ⟨hxW, h⟩, fun h => h.2⟩
  rw [key]
  constructor
  · intro hx' y hy
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ := exists_finFree_app_of_finitePresentation π hx'
    have hW''W : W'' ≤ W := hle.trans (X.basicOpen_le _)
    have hu := isUnit_resG_of_le_basicOpen' hW''W _ hle
    rw [resG_nm π hW hW'' hW''W hF, resG_resG] at hu
    have hu' := isUnit_of_nm hF'' hu
    have hy'' : y ∈ Y.basicOpen (resG Y (π.preimage_mono (hW''W.trans hWV)) b) := by
      rw [Y.basicOpen_of_isUnit hu']
      show π y ∈ W''
      rw [hy]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at hy''
    exact hy''.2
  · intro hall
    have hall' : ∀ y, π y = x → y ∈ Y.basicOpen (resG Y (π.preimage_mono hWV) b) := by
      intro y hy
      rw [basicOpen_resG_eq_inf_basicOpen]
      refine ⟨?_, hall y hy⟩
      show π y ∈ W
      rw [hy]
      exact hxW
    obtain ⟨V', hxV', hV'⟩ := exists_preimage_le π hall'
    obtain ⟨W'', hW'', hxW'', hle, hF''⟩ :=
      exists_finFree_app_of_finitePresentation π (U := W ⊓ V') ⟨hxW, hxV'⟩
    have hW''W : W'' ≤ W := hle.trans inf_le_left
    have hu := isUnit_resG_of_le_basicOpen' (π.preimage_mono hW''W) (resG Y (π.preimage_mono hWV) b)
      ((π.preimage_mono (hle.trans inf_le_right)).trans hV')
    have hu2 := hu.map (nm (π.app W'').hom)
    rw [← resG_nm π hW hW'' hW''W hF] at hu2
    have h3 : x ∈ X.basicOpen (resG X hW''W (nm (π.app W).hom (resG Y (π.preimage_mono hWV) b))) := by
      rw [X.basicOpen_of_isUnit hu2]
      exact hxW''
    rw [basicOpen_resG_eq_inf_basicOpen] at h3
    exact h3.2

end GlobalTheory.CompanionTheory.FinFlatNorm


open GlobalTheory.CompanionTheory.FinFlatNorm in
theorem GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  intro X Y q h1 h2 h3
  exact ⟨normFun q, fun V W h a => resG_normFun q h a, fun V a y hy => mem_basicOpen_normFun q a hy⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_restriction_compatible : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  first | exact @GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | exact GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | (intros; apply GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescent
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescent
noncomputable section

namespace GlobalTheory.CompanionTheory.NormLB

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm

variable {X Y : Scheme.{0}} {L : LB X} {W W' : X.Opens}

structure Frame (L : LB X) (W : X.Opens) where

  e : ∀ i, Γ(X, W ⊓ L.U i)ˣ

  rel : ∀ (x : X) (i j : L.ι), x ∈ W ⊓ L.U i → x ∈ W ⊓ L.U j →
    gm (𝟙 X) x _ (e i) = gm (𝟙 X) x (L.U i ⊓ L.U j) (L.g i j) * gm (𝟙 X) x _ (e j)

def Frame.res (e : Frame L W) (h : W' ≤ W) : Frame L W' where
  e i := Semi.res (inf_le_inf_right _ h) (e.e i)
  rel x i j hi hj := by
    rw [gm_res (𝟙 X) x _ hi, gm_res (𝟙 X) x _ hj]
    exact e.rel x i j ⟨h hi.1, hi.2⟩ ⟨h hj.1, hj.2⟩

theorem gs_appIso_inv (W : X.Opens) (A : W.toScheme.Opens) (z : W.toScheme) (hz : z ∈ A) (a : Γ(W.toScheme, A)) :
    gs W.ι z (W.ι ''ᵁ A) ((W.ι.appIso A).inv.hom a) = gs (𝟙 _) z A a := by
  have hz' : W.ι z ∈ W.ι ''ᵁ A := ⟨z, hz, rfl⟩
  have e := gs_pull (𝟙 _) W.ι z (W.ι ''ᵁ A) hz' ((W.ι.appIso A).inv.hom a)
  rw [Category.id_comp] at e
  rw [← e]
  have e2 : (W.ι.app (W.ι ''ᵁ A)).hom ((W.ι.appIso A).inv.hom a) =
      resG W.toScheme (W.ι.preimage_image_eq A).le a := by
    have := congrArg (fun f => f.hom a) (Scheme.Hom.appIso_inv_app W.ι A)
    exact this
  rw [e2]
  exact gs_res (𝟙 _) z _ (by simpa using hz) a

theorem gm_stalk {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)ˣ) :
    (gm r z U a).val = (r.stalkMap z).hom (gm (𝟙 X) (r z) U a).val := by
  rw [← gs_unit r z U h, ← gs_unit (𝟙 X) (r z) U h]
  exact gs_stalkMap r z U h a.val

def genUnit (W : X.Opens) (t : (L.pull W.ι).Gen) (i : L.ι) : Γ(X, W ⊓ L.U i)ˣ :=
  Semi.res (U := W.ι ''ᵁ (L.pull W.ι).U fun _ => i) (V := W ⊓ L.U i)
    (fun x hx => ⟨⟨x, hx.1⟩, mem_pull.2 hx.2, rfl⟩)
    (Units.map (W.ι.appIso ((L.pull W.ι).U fun _ => i)).inv.hom (t.s fun _ => i))

theorem gm_genUnit (W : X.Opens) (t : (L.pull W.ι).Gen) (i : L.ι) (z : W.toScheme) (hz : W.ι z ∈ L.U i) :
    gm W.ι z _ (genUnit W t i) = gm (𝟙 _) z _ (t.s fun _ => i) := by
  have hA : z ∈ (L.pull W.ι).U fun _ => i := mem_pull.2 hz
  have h1 : W.ι z ∈ W ⊓ L.U i := ⟨z.2, hz⟩
  apply Units.ext
  rw [← gs_unit W.ι z _ h1, ← gs_unit (𝟙 _) z _ hA]
  exact (gs_res W.ι z _ h1 _).trans (gs_appIso_inv W _ z hA _)

def Frame.ofGen (W : X.Opens) (t : (L.pull W.ι).Gen) (ht : t.IsGen) : Frame L W where
  e := genUnit W t
  rel x i j hi hj := by
    obtain ⟨z, rfl⟩ : ∃ z : W.toScheme, W.ι z = x := ⟨⟨x, hi.1⟩, rfl⟩
    have hiz : z ∈ (L.pull W.ι).U fun _ => i := mem_pull.2 hi.2
    have hjz : z ∈ (L.pull W.ι).U fun _ => j := mem_pull.2 hj.2
    have hm : z ∈ (L.pull W.ι).U (fun _ => i) ⊓ (L.pull W.ι).U fun _ => j := ⟨hiz, hjz⟩
    have e1 := congrArg (gm (𝟙 _) z _) (ht (fun _ => i) (fun _ => j))
    rw [map_mul, gm_res (𝟙 _) z _ hm, gm_res (𝟙 _) z _ hm, (chartPullPull L W.ι).g z _ _ hiz hjz,
      ← gm_genUnit W t i z hi.2, ← gm_genUnit W t j z hj.2] at e1
    have inj : Function.Injective (W.ι.stalkMap z).hom :=
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap z)).1
    have hij : W.ι z ∈ L.U i ⊓ L.U j := ⟨hi.2, hj.2⟩
    apply Units.ext
    apply inj
    rw [Units.val_mul, map_mul, ← gm_stalk W.ι z _ hi, ← gm_stalk W.ι z _ hij, ← gm_stalk W.ι z _ hj]
    exact congrArg Units.val e1

theorem exists_div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') (T : X.Opens) (hT : T ≤ W) (hT' : T ≤ W') :
    ∃ u : Γ(X, T)ˣ, ∀ (x : X) (i : L.ι), x ∈ T → (hi : x ∈ L.U i) →
      gm (𝟙 X) x T u = gm (𝟙 X) x _ (e'.e i) * (gm (𝟙 X) x _ (e.e i))⁻¹ := by
  have h1 : ∀ i, T ⊓ L.U i ≤ W ⊓ L.U i := fun i => inf_le_inf_right _ hT
  have h2 : ∀ i, T ⊓ L.U i ≤ W' ⊓ L.U i := fun i => inf_le_inf_right _ hT'
  obtain ⟨u, hu⟩ := glue_unit T (fun i => T ⊓ L.U i) (fun _ => inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hx, hi⟩)
    (fun i => Semi.res (h2 i) (e'.e i) * (Semi.res (h1 i) (e.e i))⁻¹)
    (fun i j x hx => by
      have a := e.rel x i j (h1 i hx.1) (h1 j hx.2)
      have b := e'.rel x i j (h2 i hx.1) (h2 j hx.2)
      rw [map_mul, map_mul, map_inv, map_inv, gm_res _ x _ hx.1, gm_res _ x _ hx.1, gm_res _ x _ hx.2,
        gm_res _ x _ hx.2, a, b, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul])
  refine ⟨u, fun x i hx hi => ?_⟩
  have hm : x ∈ T ⊓ L.U i := ⟨hx, hi⟩
  have := congrArg (gm (𝟙 X) x _) (hu i)
  rwa [gm_res _ x _ hm, map_mul, map_inv, gm_res _ x _ hm, gm_res _ x _ hm] at this

def Frame.div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') (T : X.Opens) (hT : T ≤ W) (hT' : T ≤ W') : Γ(X, T)ˣ :=
  (exists_div hL e e' T hT hT').choose

theorem Frame.gm_div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') {T : X.Opens} (hT : T ≤ W) (hT' : T ≤ W')
    {x : X} (i : L.ι) (hx : x ∈ T) (hi : x ∈ L.U i) :
    gm (𝟙 X) x T (e.div hL e' T hT hT') = gm (𝟙 X) x _ (e'.e i) * (gm (𝟙 X) x _ (e.e i))⁻¹ :=
  (exists_div hL e e' T hT hT').choose_spec x i hx hi

theorem Frame.res_div (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') {T T' : X.Opens} (hT : T ≤ W) (hT' : T ≤ W')
    (h : T' ≤ T) : Semi.res h (e.div hL e' T hT hT') = e.div hL e' T' (h.trans hT) (h.trans hT') :=
  unit_ext fun x hx => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    rw [gm_res _ x _ hx, e.gm_div hL e' hT hT' i (h hx) hi, e.gm_div hL e' _ _ i hx hi]

theorem Frame.div_self (hL : L.IsLB) (e : Frame L W) {T : X.Opens} (hT : T ≤ W) (hT' : T ≤ W) :
    e.div hL e T hT hT' = 1 :=
  unit_ext fun x hx => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    rw [e.gm_div hL e hT hT' i hx hi, mul_inv_cancel, map_one]

theorem Frame.div_mul_div (hL : L.IsLB) {W'' : X.Opens} (e : Frame L W) (e' : Frame L W') (e'' : Frame L W'')
    {T : X.Opens} (h : T ≤ W) (h' : T ≤ W') (h'' : T ≤ W'') :
    e.div hL e' T h h' * e'.div hL e'' T h' h'' = e.div hL e'' T h h'' :=
  unit_ext fun x hx => by
    obtain ⟨i, hi⟩ := exists_chart hL x
    rw [map_mul, e.gm_div hL e' h h' i hx hi, e'.gm_div hL e'' h' h'' i hx hi, e.gm_div hL e'' h h'' i hx hi]
    simp only [← div_eq_mul_inv]
    rw [mul_comm]
    exact div_mul_div_cancel _ _ _

theorem exists_fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) :
    ∃ a : Γ(X, W), ∀ (x : X) (i : L.ι), x ∈ W → (hi : x ∈ L.U i) →
      gs (𝟙 X) x W a * (gm (𝟙 X) x _ (e.e i)).val ^ n = gs (𝟙 X) x _ (powFn s fun _ => i) := by
  have hc : ∀ i, W ⊓ L.U i ≤ powChart L fun _ => i := fun i x hx => mem_powChart.2 hx.2
  let a : ∀ i, Γ(X, W ⊓ L.U i) := fun i => resG X (hc i) (powFn s fun _ => i) * (((e.e i)⁻¹ ^ n : Γ(X, W ⊓ L.U i)ˣ) : Γ(X, W ⊓ L.U i))
  have ga : ∀ (x : X) (i : L.ι) (hx : x ∈ W ⊓ L.U i), gs (𝟙 X) x _ (a i) =
      gs (𝟙 X) x _ (powFn s fun _ => i) * (((gm (𝟙 X) x _ (e.e i))⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := by
    intro x i hx
    rw [gs_mul _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx, map_pow, map_inv]
  have inv1 : ∀ (x : X) (u : (X.presheaf.stalk x)ˣ), (u.val) ^ n * ((u⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) = 1 := by
    intro x u
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel, one_pow, Units.val_one]
  have hh : ∀ i j, resG X (inf_le_left : (W ⊓ L.U i) ⊓ (W ⊓ L.U j) ≤ W ⊓ L.U i) (a i) =
      resG X (inf_le_right : (W ⊓ L.U i) ⊓ (W ⊓ L.U j) ≤ W ⊓ L.U j) (a j) := fun i j => fn_ext fun x hx => by
    have h1 := inv1 x (gm (𝟙 X) x _ (L.g i j))
    rw [gs_res _ x _ hx, gs_res _ x _ hx, ga x i hx.1, ga x j hx.2,
      gs_powFn_compat s (𝟙 X) x (fun _ => i) (fun _ => j) (mem_powChart.2 hx.1.2) (mem_powChart.2 hx.2.2),
      e.rel x i j hx.1 hx.2, mul_inv, mul_pow, Units.val_mul]
    linear_combination (gs (𝟙 X) x _ (powFn s fun _ => j) *
      (((gm (𝟙 X) x _ (e.e j))⁻¹ ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x)) * h1
  obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun i => W ⊓ L.U i) W (fun i => homOfLE inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      exact Opens.mem_iSup.2 ⟨i, hx, hi⟩) a hh
  refine ⟨b, fun x i hxW hi => ?_⟩
  have hx : x ∈ W ⊓ L.U i := ⟨hxW, hi⟩
  have e1 : gs (𝟙 X) x _ (a i) = gs (𝟙 X) x W b := by
    rw [← hb i]
    exact gs_res _ x inf_le_left hx b
  have h1 := inv1 x (gm (𝟙 X) x _ (e.e i))
  rw [← e1, ga x i hx]
  linear_combination (gs (𝟙 X) x _ (powFn s fun _ => i)) * h1

def Frame.fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) : Γ(X, W) := (exists_fn hL e s).choose

theorem Frame.gs_fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) {x : X} (i : L.ι) (hx : x ∈ W)
    (hi : x ∈ L.U i) : gs (𝟙 X) x W (e.fn hL s) * (gm (𝟙 X) x _ (e.e i)).val ^ n =
      gs (𝟙 X) x _ (powFn s fun _ => i) :=
  (exists_fn hL e s).choose_spec x i hx hi

theorem Frame.res_fn (hL : L.IsLB) (e : Frame L W) (e' : Frame L W') {n : ℕ} (s : (lbPow L n).Sec) {T : X.Opens}
    (hT : T ≤ W) (hT' : T ≤ W') :
    resG X hT (e.fn hL s) = ((e.div hL e' T hT hT') ^ n).val * resG X hT' (e'.fn hL s) := fn_ext fun x hx => by
  obtain ⟨i, hi⟩ := exists_chart hL x
  have a := e.gs_fn hL s i (hT hx) hi
  have b := e'.gs_fn hL s i (hT' hx) hi
  rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx, map_pow, e.gm_div hL e' hT hT' i hx hi]
  have u : (((gm (𝟙 X) x _ (e'.e i) * (gm (𝟙 X) x _ (e.e i))⁻¹) ^ n : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) *
      (gm (𝟙 X) x _ (e.e i)).val ^ n = (gm (𝟙 X) x _ (e'.e i)).val ^ n := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, inv_mul_cancel_right, Units.val_pow_eq_pow_val]
  apply ((gm (𝟙 X) x _ (e.e i) ^ n).isUnit).mul_right_cancel
  rw [Units.val_pow_eq_pow_val]
  linear_combination a - b - gs (𝟙 X) x W' (e'.fn hL s) * u

theorem Frame.mem_basicOpen_fn (hL : L.IsLB) (e : Frame L W) {n : ℕ} (s : (lbPow L n).Sec) {x : X} (hx : x ∈ W) :
    x ∈ X.basicOpen (e.fn hL s) ↔ x ∈ nonzeroLocus s := by
  obtain ⟨i, hi⟩ := exists_chart hL x
  refine (isUnit_gs_iff (𝟙 X) x W hx _).symm.trans ?_
  rw [mem_nonzeroLocus_iff_powFn s (J := fun _ => i) (mem_powChart.2 hi),
    ← e.gs_fn hL s i hx hi, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]

section Norm

variable (q : X ⟶ Y) (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V))

def NormRes : Prop := ∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)),
  (Y.presheaf.map (homOfLE h).op).hom (N V a) =
    N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)

def normLB (hL : L.IsLB) : LB Y where
  ι := Σ V : Y.Opens, Frame L (q ⁻¹ᵁ V)
  U c := c.1
  g c c' := Units.map (N (c.1 ⊓ c'.1))
    (c.2.div hL c'.2 _ (q.preimage_mono inf_le_left) (q.preimage_mono inf_le_right))

variable {q N}

theorem normLB_res_g (hN : NormRes q N) (hL : L.IsLB) (c c' : (normLB q N hL).ι) {T : Y.Opens}
    (h : T ≤ c.1 ⊓ c'.1) :
    Semi.res h ((normLB q N hL).g c c') = Units.map (N T)
      (c.2.div hL c'.2 (q ⁻¹ᵁ T) (q.preimage_mono (h.trans inf_le_left)) (q.preimage_mono (h.trans inf_le_right))) :=
  Units.ext ((hN _ _ h _).trans (congrArg (N T) (congrArg Units.val (Frame.res_div hL c.2 c'.2 _ _ _))))

theorem isLB_normLB (hN : NormRes q N) (hL : L.IsLB) (hc : ∀ y : Y, ∃ c : (normLB q N hL).ι, y ∈ c.1) :
    (normLB q N hL).IsLB := {
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self c := (normLB_res_g hN hL c c _).trans (by rw [Frame.div_self, map_one])
  cocycle c₁ c₂ c₃ := (congrArg₂ (· * ·) (normLB_res_g hN hL c₁ c₂ _) (normLB_res_g hN hL c₂ c₃ _)).trans
    (((map_mul _ _ _).symm.trans (congrArg _ (Frame.div_mul_div hL _ _ _ _ _ _))).trans
      (normLB_res_g hN hL c₁ c₃ _).symm) }

theorem gs_norm_compat (hN : NormRes q N) (hL : L.IsLB) {n : ℕ} (s : (lbPow L n).Sec) (c c' : (normLB q N hL).ι)
    {y : Y} (hy : y ∈ c.1) (hy' : y ∈ c'.1) :
    gs (𝟙 Y) y c.1 (N c.1 (c.2.fn hL s)) = (gm (𝟙 Y) y (c.1 ⊓ c'.1) ((normLB q N hL).g c c')).val ^ n *
      gs (𝟙 Y) y c'.1 (N c'.1 (c'.2.fn hL s)) := by
  have hm : y ∈ c.1 ⊓ c'.1 := ⟨hy, hy'⟩
  have e := Frame.res_fn hL c.2 c'.2 s (T := q ⁻¹ᵁ (c.1 ⊓ c'.1)) (q.preimage_mono inf_le_left)
    (q.preimage_mono inf_le_right)
  have e1 := hN c.1 (c.1 ⊓ c'.1) inf_le_left (c.2.fn hL s)
  have e2 := hN c'.1 (c.1 ⊓ c'.1) inf_le_right (c'.2.fn hL s)
  let gu : Γ(Y, c.1 ⊓ c'.1)ˣ := (normLB q N hL).g c c'
  have e3 : resG Y (inf_le_left : c.1 ⊓ c'.1 ≤ c.1) (N c.1 (c.2.fn hL s)) =
      (gu ^ n).val * resG Y (inf_le_right : c.1 ⊓ c'.1 ≤ c'.1) (N c'.1 (c'.2.fn hL s)) := by
    refine e1.trans (Eq.trans (congrArg _ e) ?_)
    rw [map_mul]
    exact congrArg₂ (· * ·) (congrArg Units.val (map_pow (Units.map (N (c.1 ⊓ c'.1))) _ n)) e2.symm
  rw [← gs_res _ y (inf_le_left : c.1 ⊓ c'.1 ≤ c.1) hm, e3, gs_mul _ y _ hm, gs_res _ y inf_le_right hm,
    gs_unit _ y _ hm, map_pow, Units.val_pow_eq_pow_val]

def normSec (hN : NormRes q N) (hL : L.IsLB) {n : ℕ} (s : (lbPow L n).Sec) : (lbPow (normLB q N hL) n).Sec :=
  powSecOfGerm n
    (fun J => resG Y (show powChart (normLB q N hL) J ≤ (J PUnit.unit).1 from fun _ hy => mem_powChart.1 hy)
      (N (J PUnit.unit).1 ((J PUnit.unit).2.fn hL s)))
    fun y J J' hJ hJ' => by
      rw [gs_res _ y _ hJ, gs_res _ y _ hJ']
      exact gs_norm_compat hN hL s _ _ (mem_powChart.1 hJ) (mem_powChart.1 hJ')

theorem mem_nonzeroLocus_normSec (hN : NormRes q N)
    (hB : ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V →
      (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a))
    (hL : L.IsLB) (hc : ∀ y : Y, ∃ c : (normLB q N hL).ι, y ∈ c.1) {n : ℕ} (s : (lbPow L n).Sec) (y : Y) :
    y ∈ nonzeroLocus (normSec hN hL s) ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  obtain ⟨c, hy⟩ := hc y
  have hJ : y ∈ powChart (normLB q N hL) fun _ => c := mem_powChart.2 hy
  rw [mem_nonzeroLocus_iff_powFn _ hJ]
  have e : gs (𝟙 Y) y _ (powFn (normSec hN hL s) fun _ => c) = gs (𝟙 Y) y c.1 (N c.1 (c.2.fn hL s)) :=
    gs_res _ y _ hJ _
  rw [e, isUnit_gs_iff (𝟙 Y) y c.1 hy, show (𝟙 Y) y = y from rfl, hB c.1 _ y hy]
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  exact c.2.mem_basicOpen_fn hL s (show q x ∈ c.1 from hx ▸ hy)

end Norm

theorem exists_chart_of_gen {q : X ⟶ Y} (hq : IsClosedMap q) {y : Y} {W : X.Opens} (hW : ∀ x : X, q x = y → x ∈ W)
    (e : Frame L W) : ∃ c : Σ V : Y.Opens, Frame L (q ⁻¹ᵁ V), y ∈ c.1 := by
  let V : Y.Opens := ⟨(q '' (W : Set X)ᶜ)ᶜ, (hq _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hle : q ⁻¹ᵁ V ≤ W := fun x hx => by_contra fun h => hx ⟨x, h, rfl⟩
  exact ⟨⟨V, e.res hle⟩, fun ⟨x, hx, h⟩ => hx (hW x h)⟩

end GlobalTheory.CompanionTheory.NormLB

section Main

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.NormLB.exists_normLB : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → ∀ (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V)), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) → (∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a)) → ∀ L : LB X, L.IsLB → (∀ y : Y, ∃ W : X.Opens, (∀ x : X, q x = y → x ∈ W) ∧ ∃ t : (L.pull W.ι).Gen, t.IsGen) → ∃ L' : LB Y, L'.IsLB ∧ ∀ (n : ℕ) (s : (lbPow L n).Sec), ∃ σ : (lbPow L' n).Sec, ∀ y : Y, y ∈ nonzeroLocus σ ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  intro X Y q hq N hN hB L hL hgen
  have hcl : IsClosedMap q := q.isClosedMap
  have hc : ∀ y : Y, ∃ c : (normLB q N hL).ι, y ∈ c.1 := fun y => by
    obtain ⟨W, hW, t, ht⟩ := hgen y
    exact exists_chart_of_gen hcl hW (Frame.ofGen W t ht)
  exact ⟨normLB q N hL, isLB_normLB hN hL hc, fun n s => ⟨normSec hN hL s, mem_nonzeroLocus_normSec hN hB hL hc s⟩⟩

end Main
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescentStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_line_bundle_descent : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → ∀ (N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V)), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) → (∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a)) → ∀ L : LB X, L.IsLB → (∀ y : Y, ∃ W : X.Opens, (∀ x : X, q x = y → x ∈ W) ∧ ∃ t : (L.pull W.ι).Gen, t.IsGen) → ∃ L' : LB Y, L'.IsLB ∧ ∀ (n : ℕ) (s : (lbPow L n).Sec), ∃ σ : (lbPow L' n).Sec, ∀ y : Y, y ∈ nonzeroLocus σ ↔ ∀ x : X, q x = y → x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.CompanionTheory.NormLB.exists_normLB | exact GlobalTheory.CompanionTheory.NormLB.exists_normLB | (intros; apply GlobalTheory.CompanionTheory.NormLB.exists_normLB <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupScheme
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupScheme
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

section Abstract

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def ptSub {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1)
    (T : C) : Subgroup (T ⟶ A) where
  carrier := {f | ∃ a : T ⟶ X, a ≫ h = f}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨lift a b ≫ m, ?_⟩
    rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a ≫ i, ?_⟩
    rw [eq_inv_iff_mul_eq_one, Category.assoc, ← MonObj.comp_mul, hi, MonObj.comp_one]

def ptFunctor {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (ptSub h m e i hm he hi (unop T))
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨f.unop ≫ a, by rw [Category.assoc, ha]⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.id_comp x.1))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.assoc _ _ x.1))

def ptRep {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    (ptFunctor h m e i hm he hi ⋙ forget _).RepresentableBy X where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (⟨a ≫ h, a, rfl⟩ : ptSub h m e i hm he hi T))
    ⟨fun a b hab => (cancel_mono h).1 (congrArg Subtype.val hab),
      fun x => by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨a, Subtype.ext ha⟩⟩
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

theorem exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp

end Abstract

section Scheme

variable {R : Type} [CommRing R]

theorem exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

theorem affine_mono (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) (hab : a ≫ h = b ≫ h) : a = b := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  have := H.mono S φ φ' (by rw [← hφ, ← hφ', Category.assoc, Category.assoc, hab])
  rw [← cancel_epi j, hφ, hφ', this]

theorem affine_mul (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a b : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = (a ≫ h) * (b ≫ h) := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨φ', hφ'⟩ := exists_eq_spMap (j ≫ b)
  obtain ⟨χ, hχ⟩ := H.mul S φ φ'
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [Category.assoc, hχ, ← hφ, ← hφ', MonObj.comp_mul, Category.assoc, Category.assoc,
    IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

theorem affine_one (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] :
    ∃ c : T ⟶ sp (R₀ := R) B, c ≫ h = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨χ, hχ⟩ := H.one S
  exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩

theorem affine_inv (H : IsFinFlatSub A B h) {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
    (a : T ⟶ sp (R₀ := R) B) : ∃ c : T ⟶ sp (R₀ := R) B, (c ≫ h) * (a ≫ h) = 1 := by
  obtain ⟨S, _, _, j, _⟩ := exists_sp_iso T
  obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ a)
  obtain ⟨χ, hχ⟩ := H.inv S φ
  refine ⟨inv j ≫ spMap χ, ?_⟩
  rw [← hφ] at hχ
  have := congrArg (inv j ≫ ·) hχ
  simp only [MonObj.comp_mul, MonObj.comp_one, Category.assoc, IsIso.inv_hom_id_assoc] at this
  simpa [Category.assoc] using this

theorem mono_of_isFinFlatSub (H : IsFinFlatSub A B h) : Mono h := by
  constructor
  intro T a b hab
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext T.left.affineCover _ _ fun i => ?_
  let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f i ≫ T.hom)
  let j : T' ⟶ T := Over.homMk (T.left.affineCover.f i) rfl
  haveI : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X i))
  have := affine_mono H (j ≫ a) (j ≫ b) (by rw [Category.assoc, Category.assoc, hab])
  exact congrArg (·.left) this

theorem grpObj_of_isFinFlatSub (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (B : Type)
    [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A) (H : IsFinFlatSub A B h) :
    ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  have hmono := mono_of_isFinFlatSub H
  haveI : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
    inferInstanceAs (IsAffine (pullback (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom))
  obtain ⟨m, hm⟩ := affine_mul H (fst _ _) (snd _ _)
  obtain ⟨e, he⟩ := affine_one H (T := 𝟙_ _)
  obtain ⟨i, hi⟩ := affine_inv H (𝟙 _)
  rw [Category.id_comp] at hi
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e i hm he hi
  exact ⟨G, hG, hmono⟩

end Scheme

end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupSchemeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
open GlobalTheory.CompanionTheory.Ar.GR.SubGrp (exists_eq_spMap exists_sp_iso exists_grpObj_of_mono) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_subgroup_scheme :
    ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
      (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A),
      IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  intro R _ A _ B _ _ h H
  have hmono : Mono h := by
    constructor
    intro T a b hab
    apply Over.OverMorphism.ext
    refine T.left.affineCover.hom_ext _ _ fun k => ?_
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f k ≫ T.hom)
    let j : T' ⟶ T := Over.homMk (T.left.affineCover.f k) rfl
    have : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X k))
    obtain ⟨S, _, _, i, _⟩ := exists_sp_iso T'
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (i ≫ j ≫ a)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (i ≫ j ≫ b)
    have hφψ := H.mono S φ ψ (by simp only [← hφ, ← hψ, Category.assoc, hab])
    have hj : j ≫ a = j ≫ b := by rw [← cancel_epi i, hφ, hψ, hφψ]
    exact congrArg (·.left) hj
  have hmul : ∃ m : sp (R₀ := R) B ⊗ sp (R₀ := R) B ⟶ sp (R₀ := R) B,
      m ≫ h = (fst _ _ ≫ h) * (snd _ _ ≫ h) := by
    have : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
    have : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
      Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
        (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (sp (R₀ := R) B ⊗ sp (R₀ := R) B)
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ fst _ _)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (j ≫ snd _ _)
    obtain ⟨χ, hχ⟩ := H.mul S φ ψ
    refine ⟨inv j ≫ spMap χ, ?_⟩
    rw [Category.assoc, hχ, ← hφ, ← hψ, MonObj.comp_mul, Category.assoc, Category.assoc,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
  have hone : ∃ e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ sp (R₀ := R) B, e ≫ h = 1 := by
    have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (IsAffine (Spec _))
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (𝟙_ (Over (Spec (CommRingCat.of R))))
    obtain ⟨χ, hχ⟩ := H.one S
    exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩
  obtain ⟨i, hi⟩ := H.inv B (AlgHom.id R B)
  have hid : spMap (AlgHom.id R B) = 𝟙 (sp (R₀ := R) B) := by
    apply Over.OverMorphism.ext
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, Over.id_left]
    exact Spec.map_id _
  rw [hid, Category.id_comp] at hi
  obtain ⟨m, hm⟩ := hmul
  obtain ⟨e, he⟩ := hone
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e (spMap i) hm he hi
  exact ⟨G, hG, hmono⟩
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotient
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.QuotientSide

theorem isSeparated_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (r : X ⟶ Y) (w : r ≫ g = f) [IsSeparated f] [IsFinite r] [Surjective r] : IsSeparated g := by
  subst w
  let m : pullback (r ≫ g) (r ≫ g) ⟶ pullback g g :=
    pullback.map _ _ _ _ r r (𝟙 S) (by simp) (by simp)
  have hm : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) (i₁ := r) (i₂ := r) inferInstance inferInstance
      rfl rfl
  have comm : pullback.diagonal (r ≫ g) ≫ m = r ≫ pullback.diagonal g := by
    have h₁ : m ≫ pullback.fst g g = pullback.fst (r ≫ g) (r ≫ g) ≫ r := pullback.lift_fst _ _ _
    have h₂ : m ≫ pullback.snd g g = pullback.snd (r ≫ g) (r ≫ g) ≫ r := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, pullback.diagonal_fst,
        pullback.diagonal_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, pullback.diagonal_snd,
        pullback.diagonal_snd, Category.id_comp, Category.comp_id]
  have hrange : Set.range (pullback.diagonal g) =
      m '' Set.range (pullback.diagonal (r ≫ g)) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, comm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr r.surjective, Set.image_univ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact m.isClosedMap _ (pullback.diagonal (r ≫ g)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem isSeparated_target_of_finite_surjective :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by
  intro S X Y K q p₁ p₂ _ _ hX hq hs
  exact isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)

end GlobalTheory.CompanionTheory.QuotientSide
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotientStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separated_of_finite_surjective_quotient : ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q → IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left → IsSeparated Y.hom := by
  first | exact @GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | exact GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective <;> assumption)
end
end

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.QuotSide

section Act
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] (h : G ⟶ A) [IsMonHom h]

abbrev act : ModObj G A :=
  letI := ModObj.regular A
  Mod.scalarRestriction h A

lemma act_smul : (act h).smul = (fst G A ≫ h) * snd G A := by
  rw [Hom.mul_def]
  change h ▷ A ≫ μ[A] = _
  congr 1

end Act

theorem quotientByFiniteFlat_of_freeQuotient (hF : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme) :
    QuotientByFiniteFlatStatement := by
  intro R _ A _ L hA hL hamp B _ _ h hsub
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, hmon, hmono⟩ := GlobalTheory.T.finite_flat_subgroup_scheme R A B h hsub
  letI := act h
  have hgam : (γ[sp (R₀ := R) B, A] : sp (R₀ := R) B ⊗ A ⟶ A) = (fst _ A ≫ h) * snd _ A := act_smul h
  have hsmul : ∀ {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ sp (R₀ := R) B) (x : T ⟶ A),
      g • x = (g ≫ h) * x := by
    intro T g x
    rw [Hom.smul_def, hgam, comp_mul]
    simp
  have hample : GlobalTheory.IsAmpleLB L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hG : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFiniteLocallyFree (sp (R₀ := R) B).hom := by
    have e : (sp (R₀ := R) B).hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := rfl
    have := hsub.proj
    have := hsub.fin
    have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
    have hfp : (algebraMap R B).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation R B)
    rw [e]
    refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance),
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance), ?_⟩
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp
  have hfree : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFreeAction (sp (R₀ := R) B) A := by
    intro T g x hx
    rw [hsmul] at hx
    have h1 : g ≫ h = 1 := mul_eq_right.mp hx
    rw [← cancel_mono h, h1, MonObj.one_comp]
  have horb : ∀ x : A.left, ∃ U : A.left.Opens, IsAffineOpen U ∧
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x ⊆ U := by
    intro x
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    have hs : IsFinite (snd (sp (R₀ := R) B) A).left := by
      rw [Over.snd_left]; infer_instance
    have hfin : (GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x).Finite :=
      (Scheme.Hom.finite_preimage_singleton _ x).image _
    obtain ⟨n, -, s, h₁, -, h₂⟩ := hample.exists_affine_finite_subset hfin
      (U := ⊤) (fun _ _ => trivial)
    exact ⟨_, h₂, h₁⟩
  obtain ⟨Y, q, -, hT⟩ := hF _ (sp (R₀ := R) B) A hG hfree horb
  obtain ⟨hq1, hq2, hq3⟩ := hT.isFiniteLocallyFree hG
  have hq4 := hT.surjective
  have hq : IsPullback ((fst _ A ≫ h) * snd _ A) (snd _ A) q q := hgam ▸ hT.1
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨inst, hcomm, hhom, hker⟩ := GlobalTheory.AbelianQuotient.exists_grpObj h q hq
  have hw : q.left ≫ Y.hom = A.hom := Over.w q
  have hsnd : IsFinite (snd (sp (R₀ := R) B) A).left := by
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    rw [Over.snd_left]; infer_instance
  have hab : IsAbelianScheme Y := by
    have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated Y.hom := GlobalTheory.T.separated_of_finite_surjective_quotient q _ _ hq hsnd inferInstance hq1 hq4
    have : Flat (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyReduced (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyConnected (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Y.hom
    have := UniversallyClosed.of_comp_surjective q.left Y.hom
    have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Y.hom
    have : LocallyOfFinitePresentation Y.hom :=
      GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Y.hom hq1 hq2 hq3 hq4 (by rw [hw]; infer_instance)
    exact ⟨hcomm, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Y, ⟨⟩,
      GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Y.hom⟩
  have := hab.proper
  obtain ⟨N, hN₁, hN₂⟩ := GlobalTheory.T.norm_map_restriction_compatible q.left hq1 hq2 hq3
  obtain ⟨L', hL', hN⟩ := GlobalTheory.T.norm_line_bundle_descent q.left hq1 N hN₁ hN₂ L hL (by
    intro y
    obtain ⟨W, -, h₁, -, t⟩ := hample.exists_affine_finite_subset_trivial hL
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := ⊤) (fun _ _ => trivial)
    exact ⟨W, fun x hx => h₁ hx, t⟩)
  refine ⟨Y, inst, L', q, hab, hL', ?_, hhom, hq1, hq2, hq4, ?_⟩
  · have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have : CompactSpace Y.left := q.left.surjective.compactSpace q.left.continuous
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine Y hL').2
      (GlobalTheory.isAmpleLB_of_forall_le hL' fun y U hy => ?_)
    obtain ⟨n, hn, s, h₁, h₂, -⟩ := hample.exists_affine_finite_subset
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := q.left ⁻¹ᵁ U)
      (fun x hx => show q.left x ∈ U from (show q.left x = y from hx) ▸ hy)
    obtain ⟨σ, hσ⟩ := hN n s
    refine ⟨n, hn, σ, (hσ y).2 fun x hx => h₁ hx, fun y' hy' => ?_⟩
    obtain ⟨x, rfl⟩ := q.left.surjective y'
    exact h₂ ((hσ _).1 hy' x rfl)
  · intro S _ _ z
    have hhq : h ≫ q = 1 := hker.w.trans Hom.one_def.symm
    constructor
    · intro hz
      let y : sp (R₀ := R) S ⟶ sp (R₀ := R) B :=
        hker.lift z (toUnit _) (by rw [hz, Hom.one_def])
      have hy : y ≫ h = z := hker.lift_fst _ _ _
      obtain ⟨ψ, hψ⟩ := Spec.map_surjective y.left
      have hc : CommRingCat.ofHom (algebraMap R B) ≫ ψ = CommRingCat.ofHom (algebraMap R S) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ]
        exact Over.w y
      let φ : B →ₐ[R] S := { ψ.hom with
        commutes' := fun r => congr($hc r) }
      have hφ : spMap φ = y := Over.OverMorphism.ext hψ
      exact ⟨φ, by rw [hφ, hy]⟩
    · rintro ⟨φ, rfl⟩
      rw [Category.assoc, hhq, comp_one]

end GlobalTheory.CompanionTheory.Ar.GR.QuotSide
