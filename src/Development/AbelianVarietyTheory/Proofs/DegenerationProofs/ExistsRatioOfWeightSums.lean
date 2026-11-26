module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsUnitEv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}

def ev (g : Sp R ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(Y, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom

theorem _root_.GlobalTheory.SS.WtRat.ev_congr {g g' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y} (e : g = g') (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ g' ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g V h u = _root_.GlobalTheory.SS.WtRat.ev g' V h' u := by
  subst e
  rfl

theorem _root_.GlobalTheory.SS.WtRat.ev_appLE (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (φ : Y ⟶ Y') (V : Y'.Opens)
    (W : Y.Opens) (e : W ≤ φ ⁻¹ᵁ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ (g ≫ φ) ⁻¹ᵁ V) (u : Γ(Y', V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((φ.appLE V W e).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev (g ≫ φ) V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]

theorem _root_.GlobalTheory.SS.WtRat.ev_res (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) {V W : Y.Opens} (e : W ≤ V)
    (h : ⊤ ≤ g ⁻¹ᵁ W) (h' : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev g W h ((Y.presheaf.map (homOfLE e).op).hom u) =
      _root_.GlobalTheory.SS.WtRat.ev g V h' u := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE]

theorem _root_.GlobalTheory.SS.WtRat.ev_top (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (h : ⊤ ≤ g ⁻¹ᵁ ⊤) (u : Γ(Y, ⊤)) :
    _root_.GlobalTheory.SS.WtRat.ev g ⊤ h u =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (g.appTop.hom u) := by
  simp only [_root_.GlobalTheory.SS.WtRat.ev, RingHom.comp_apply, Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE]
  rfl

theorem _root_.GlobalTheory.SS.WtRat.ev_spMap (σ : R →+* R') (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (h' : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) ⁻¹ᵁ V) (u : Γ(Y, V)) :
    _root_.GlobalTheory.SS.WtRat.ev (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ ≫ g) V h' u =
      σ (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  rw [← _root_.GlobalTheory.SS.WtRat.ev_appLE (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) g V ⊤ h le_top h' u]
  erw [_root_.GlobalTheory.SS.WtRat.ev_top]
  exact congrArg (fun f => CommRingCat.Hom.hom f ((g.appLE V ⊤ h).hom u))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ))

private theorem isUnit_of_basicOpen_covers_scheme (X : Scheme) (s : Γ(X, ⊤))
    (hb : ⊤ ≤ X.basicOpen s) : IsUnit s := by
  have := (RingedSpace.isUnit_res_basicOpen _ s).map
    (ConcreteCategory.hom (X.presheaf.map (homOfLE hb).op))
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at this
  erw [Subsingleton.elim (_ ≫ _) (𝟙 (Opposite.op (⊤ : X.Opens))),
    CategoryTheory.Functor.map_id] at this
  simpa using this

theorem _root_.GlobalTheory.SS.WtRat.isUnit_ev (g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ Y) (V : Y.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ V) (u : Γ(Y, V)) (hu : ⊤ ≤ g ⁻¹ᵁ Y.basicOpen u) :
    IsUnit (_root_.GlobalTheory.SS.WtRat.ev g V h u) := by
  have hb : ⊤ ≤ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R).basicOpen ((g.appLE V ⊤ h).hom u) := by
    have := Scheme.basicOpen_appLE g ⊤ V h u
    erw [this]
    exact le_inf le_rfl hu
  exact (isUnit_of_basicOpen_covers_scheme _ _ hb).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

end GlobalTheory.SS.WtRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPoints
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

def wtDefect {P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens) (u : Γ(G, V))
    (e : Γ(T, ⊤)) : Γ(P, a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V) :=
  (a.appLE V _ inf_le_left).hom u - (c.appLE ⊤ _ le_top).hom e * (b.appLE V _ inf_le_right).hom u

theorem appLE_wtDefect {Z P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens)
    (u : Γ(G, V)) (e : Γ(T, ⊤)) (p : Z ⟶ P) {a' b' : Z ⟶ G} {c' : Z ⟶ T} (ha : p ≫ a = a')
    (hb : p ≫ b = b') (hc : p ≫ c = c') (h : ⊤ ≤ p ⁻¹ᵁ (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V))
    (h₁ : ⊤ ≤ a' ⁻¹ᵁ V) (h₂ : ⊤ ≤ b' ⁻¹ᵁ V) :
    (p.appLE _ ⊤ h).hom (wtDefect a b c V u e) =
      (a'.appLE V ⊤ h₁).hom u - c'.appTop.hom e * (b'.appLE V ⊤ h₂).hom u := by
  subst ha hb hc
  have e₁ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p a V _ ⊤ inf_le_left h)
  have e₂ := congrArg (fun q => CommRingCat.Hom.hom q u)
    (Scheme.Hom.appLE_comp_appLE p b V _ ⊤ inf_le_right h)
  have e₃ := congrArg (fun q => CommRingCat.Hom.hom q e)
    ((Scheme.Hom.appLE_comp_appLE p c ⊤ _ ⊤ le_top h).trans (Scheme.Hom.appLE_eq_app (p ≫ c)))
  rw [wtDefect, map_sub, map_mul]
  exact congrArg₂ (· - ·) e₁ (congrArg₂ (· * ·) e₃ e₂)

theorem eq_zero_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {P : Over (Sp k)}
    [Smooth P.hom] {W : P.left.Opens} (d : Γ(P.left, W))
    (h : ∀ (z : 𝟙_ (Over (Sp k)) ⟶ P) (x : (𝟙_ (Over (Sp k))).left),
      z.left x ∉ P.left.basicOpen d) : d = 0 := by
  have : IsReduced P.left := GlobalTheory.isReduced_of_smooth_of_isReduced (S := Spec (.of k)) P.hom
  have : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace (Y := Spec (.of k)) P.hom
  refine eq_zero_of_basicOpen_eq_bot d ?_
  by_contra hne
  have hne' : ((P.left.basicOpen d : P.left.Opens) : Set P.left).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h' => hne (TopologicalSpace.Opens.ext h')
  obtain ⟨x, hxd, hx⟩ := nonempty_inter_closedPoints hne' (P.left.basicOpen d).isOpen.isLocallyClosed
  refine h (Over.homMk (pointOfClosedPoint (K := k) P.hom x hx)
    (pointOfClosedPoint_comp (K := k) P.hom x hx)) (IsLocalRing.closedPoint k) ?_
  have e := pointOfClosedPoint_apply (K := k) P.hom x hx (IsLocalRing.closedPoint k)
  exact e.symm ▸ hxd

theorem wt_of_genericPoint :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  intro k _ _ G _ hG X _ _ _ i F _ s g hg V u χ H
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp k)).1 X
  have : Smooth (splitTorus (Sp k) X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ X) _
  have : Smooth (splitTorus (Sp k) X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp k) X).hom G.hom ≫
      (splitTorus (Sp k) X).hom))
  have hact : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left = ((t ≫ i) * y).left := by
    intro Z t y
    rw [← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have hsnd : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (snd (splitTorus (Sp k) X) G).left = y.left := by
    intro Z t y
    rw [← Over.comp_left, lift_snd]
  have hfst : ∀ {Z : Over (Sp k)} (t : Z ⟶ splitTorus (Sp k) X) (y : Z ⟶ G),
      (lift t y).left ≫ (fst (splitTorus (Sp k) X) G).left = t.left := by
    intro Z t y
    rw [← Over.comp_left, lift_fst]
  have hd : wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val = 0 := by
    refine eq_zero_of_rationalPoints _ fun z x hx => ?_
    set d := wtDefect ((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left (snd _ G).left
      (fst (splitTorus (Sp k) X) G).left V u (charUnit (Sp k) X χ).val with hdd
    let t := z ≫ fst _ _
    let m : G ⟶ splitTorus (Sp k) X ⊗ G := lift (toUnit G ≫ t) (𝟙 G)
    have hz : (z ≫ snd _ _) ≫ m = z := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, t, Category.assoc, lift_fst]
        rw [← Category.assoc (snd _ _), ← Category.assoc z, toUnit_unique (z ≫ _) (𝟙 _),
          Category.id_comp]
      · simp [m]
    have hgm : g ≫ m = lift (toUnit (Over.mk s) ≫ t) g := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · simp only [m, Category.assoc, lift_fst]
        rw [← Category.assoc, toUnit_unique (g ≫ _) (toUnit _)]
      · simp [m]
    have h0 := hg (m.left ⁻¹ᵁ (splitTorus (Sp k) X ⊗ G).left.basicOpen d)
      ⟨(z ≫ snd _ _).left x, by
        have : m.left ((z ≫ snd _ _).left x) = z.left x := congrArg (fun q => q.left x) hz
        show m.left ((z ≫ snd _ _).left x) ∈ (splitTorus (Sp k) X ⊗ G).left.basicOpen d
        rw [this]; exact hx⟩
    have h1 : ⊤ ≤ (lift (toUnit (Over.mk s) ≫ t) g).left ⁻¹ᵁ
        (splitTorus (Sp k) X ⊗ G).left.basicOpen d := by
      rw [← hgm]; exact h0
    have h2 := h1.trans ((lift (toUnit (Over.mk s) ≫ t) g).left.preimage_mono
      ((splitTorus (Sp k) X ⊗ G).left.basicOpen_le d))
    have h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V := by
      rw [← hact]; exact fun y hy => (h2 hy).1
    have h₂ : ⊤ ≤ g.left ⁻¹ᵁ V := by
      rw [← hsnd (toUnit (Over.mk s) ≫ t)]; exact fun y hy => (h2 hy).2
    have hu := isUnit_ev (R := F) _ _ h2 d h1
    have hv := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact _ _) (hsnd _ _) (hfst _ _) h2 h₁ h₂)
    have hH := (H t h₁ h₂).trans (congrArg (· * ev (R := F) g.left V h₂ u)
      (ev_top (R := F) (toUnit (Over.mk s) ≫ t).left le_top (charUnit (Sp k) X χ).val))
    refine hu.ne_zero (hv.trans ?_)
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hH.trans (map_mul _ _ _).symm))
  intro Z t y h₁ h₂
  have h : ⊤ ≤ (lift t y).left ⁻¹ᵁ (((fst (splitTorus (Sp k) X) G ≫ i) * snd _ G).left ⁻¹ᵁ V ⊓
      (snd (splitTorus (Sp k) X) G).left ⁻¹ᵁ V) := by
    rw [← hact] at h₁
    rw [← hsnd t] at h₂
    exact fun w hw => ⟨h₁ hw, h₂ hw⟩
  have hv := appLE_wtDefect _ _ _ V u (charUnit (Sp k) X χ).val _ (hact t y) (hsnd t y) (hfst t y)
    h h₁ h₂
  rw [hd, map_zero] at hv
  exact sub_eq_zero.1 hv.symm

end GlobalTheory.SS.WtRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusWeightTestGenericPointRationalPointsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  first | exact @GlobalTheory.SS.WtRat.wt_of_genericPoint | exact GlobalTheory.SS.WtRat.wt_of_genericPoint | (intros; apply GlobalTheory.SS.WtRat.wt_of_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFunctionFieldPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFunctionFieldPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

variable {Y : Scheme.{0}}

theorem top_le_fromSpecStalk_preimage (x : Y) {V : Y.Opens} (hx : x ∈ V) :
    ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V := by
  intro y _
  have : Y.fromSpecStalk x y ∈ Set.range (Y.fromSpecStalk x) := ⟨y, rfl⟩
  rw [Scheme.range_fromSpecStalk] at this
  exact this.mem_open V.isOpen hx

theorem ev_fromSpecStalk (x : Y) {V : Y.Opens} (hx : x ∈ V)
    (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V) (u : Γ(Y, V)) :
    ev (R := Y.presheaf.stalk x) (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

theorem genericPoint_mem [IsIntegral Y] {V : Y.Opens} (hV : (V : Set Y).Nonempty) :
    genericPoint Y ∈ V :=
  ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr (by simpa using hV)

theorem exists_generic_field_point : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by
  intro Y _
  have hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ Y.fromSpecStalk (genericPoint Y) ⁻¹ᵁ V :=
    fun V hV => top_le_fromSpecStalk_preimage _ (genericPoint_mem hV)
  refine ⟨Y.functionField, inferInstance, Y.fromSpecStalk (genericPoint Y), hg, ?_, ?_, ?_⟩
  · intro V hV a b hab
    have ha := ev_fromSpecStalk _ (genericPoint_mem hV) (hg V hV) a
    have hb := ev_fromSpecStalk _ (genericPoint_mem hV) (hg V hV) b
    exact germ_injective_of_isIntegral Y (genericPoint Y) (genericPoint_mem hV)
      (ha.symm.trans (hab.trans hb))
  · intro τ
    have e : τ.hom (genericPoint Y) = genericPoint Y := genericPoint_eq_of_isOpenImmersion τ.hom
    have sp : τ.hom (genericPoint Y) ⤳ genericPoint Y := specializes_of_eq e
    refine ⟨(Y.presheaf.stalkSpecializes sp ≫ τ.hom.stalkMap (genericPoint Y)).hom, ?_⟩
    change Spec.map (Y.presheaf.stalkSpecializes sp ≫ τ.hom.stalkMap (genericPoint Y)) ≫
      Y.fromSpecStalk (genericPoint Y) = Y.fromSpecStalk (genericPoint Y) ≫ τ.hom
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro U hU I _ x
    have key : ∀ a : Y.functionField, ∃ (V : Y.Opens) (hV : genericPoint Y ∈ V) (s : Γ(Y, V)),
        (Y.presheaf.germ V _ hV).hom s = a ∧ (a ≠ 0 → IsUnit s) := by
      intro a
      obtain ⟨V, hV, s, hs⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) a
      by_cases ha : a = 0
      · exact ⟨V, hV, s, hs, fun h => (h ha).elim⟩
      · have hm : genericPoint Y ∈ Y.basicOpen s := by
          rw [Scheme.mem_basicOpen Y s _ hV]
          have : IsUnit a := isUnit_iff_ne_zero.mpr ha
          rw [← hs] at this
          exact this
        refine ⟨Y.basicOpen s, hm, (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom s, ?_,
          fun _ => Y.toRingedSpace.isUnit_res_basicOpen s⟩
        rw [← hs]
        exact Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le s)) _ hm s
    choose V hV s hs hu using fun j => key (x j)
    have hle : ∀ j, U ⊓ Finset.univ.inf V ≤ V j := fun j =>
      inf_le_right.trans (Finset.inf_le (Finset.mem_univ j))
    have hm : genericPoint Y ∈ U ⊓ Finset.univ.inf V := by
      refine ⟨genericPoint_mem hU, ?_⟩
      change genericPoint Y ∈ ((Finset.univ.inf V : Y.Opens) : Set Y)
      rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
      simp only [Set.mem_iInter]
      exact fun j _ => hV j
    refine ⟨U ⊓ Finset.univ.inf V, ⟨_, hm⟩,
      fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom (s j), inf_le_left, fun j => ⟨?_, fun h => (hu j h).map _⟩⟩
    refine (ev_fromSpecStalk _ hm _ _).trans ?_
    rw [← hs j]
    exact Y.presheaf.germ_res_apply (homOfLE (hle j)) _ hm (s j)

end GlobalTheory.SS.WtRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFunctionFieldPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_functionField_point : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by
  first | exact @GlobalTheory.SS.WtRat.exists_generic_field_point | exact GlobalTheory.SS.WtRat.exists_generic_field_point | (intros; apply GlobalTheory.SS.WtRat.exists_generic_field_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFractionEvalSectionAffineNearPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFractionEvalSectionAffineNearPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.WtRat

theorem ev_spMap_top {R F : Type} [CommRing R] [CommRing F] (e : R →+* F)
    (h : ⊤ ≤ spMap e ⁻¹ᵁ ⊤) (u : Γ(Sp R, ⊤)) :
    ev (spMap e) ⊤ h u = e ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u) :=
  (ev_top (spMap e) h u).trans
    (congrArg (fun q => CommRingCat.Hom.hom q u)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom e)))

theorem exists_frac_ev (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W))
    (x : PrimeSpectrum R) (hx : x ∈ W) :
    ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W),
      WtRat.ev (spMap e) W h s * e β = e α := by
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  obtain ⟨f, hfW, hxf⟩ := hT.exists_basicOpen_le (V := W) ⟨x, hx⟩ trivial
  have hb : (Sp R).basicOpen f =
      PrimeSpectrum.basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom f) :=
    basicOpen_eq_of_affine' f
  haveI := hT.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f)
    (((Sp R).presheaf.map (homOfLE hfW).op).hom s)
  set φ : Γ(Sp R, ⊤) →+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom with hφ
  refine ⟨φ a * φ f, φ f ^ (n + 1), ?_, ?_⟩
  · intro hm
    rw [hb] at hxf
    exact hxf (x.isPrime.mem_of_pow_mem _ hm)
  · intro F _ e h
    by_cases h0 : e (φ f) = 0
    · simp [h0]
    have hD : ⊤ ≤ spMap e ⁻¹ᵁ (Sp R).basicOpen f := by
      intro y _
      rw [hb]
      change e (φ f) ∉ y.asIdeal
      intro hy
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (Ne.isUnit h0))
    have key := congrArg (ev (spMap e) _ hD) ha
    rw [map_mul, ev_res (spMap e) hfW hD h s] at key
    have hv : ∀ u : Γ(Sp R, ⊤),
        ev (spMap e) _ hD (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen f) u) = e (φ u) :=
      fun u => (ev_res (spMap e) ((Sp R).basicOpen_le f) hD le_top u).trans
        (ev_spMap_top e le_top u)
    rw [hv, hv] at key
    simp only [map_pow] at key
    rw [map_pow, map_mul, pow_succ, ← _root_.mul_assoc, key]

end GlobalTheory.SS.WtRat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFractionEvalSectionAffineNearPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fraction_evalSection_affine_near_point : ∀ (R : Type) [CommRing R] (W : (Sp R).Opens) (s : Γ(Sp R, W)) (x : PrimeSpectrum R), x ∈ W → ∃ α β : R, β ∉ x.asIdeal ∧ ∀ (F : Type) [Field F] (e : R →+* F) (h : ⊤ ≤ spMap e ⁻¹ᵁ W), WtRat.ev (spMap e) W h s * e β = e α := by
  first | exact @GlobalTheory.SS.WtRat.exists_frac_ev | exact GlobalTheory.SS.WtRat.exists_frac_ev | (intros; apply GlobalTheory.SS.WtRat.exists_frac_ev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightedRelationOfMinimalSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightedRelationOfMinimalSupport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_minimal_support {F J : Type} [Field F] (A : Finset J) (M : (J → F) → Prop)
    (L : (J → F) → F) (hM : ∀ v w (a : F), M v → M w → M (fun i => v i - a * w i))
    (hL : ∀ v w (a : F), L (fun i => v i - a * w i) = L v - a * L w)
    (v : J → F) (hv : M v) (hLv : L v ≠ 0) :
    ∃ v', M v' ∧ L v' ≠ 0 ∧ ∀ w, M w → (∀ i ∈ A, v' i = 0 → w i = 0) →
      ∀ i₀ ∈ A, v' i₀ ≠ 0 → w i₀ = 0 → ∀ i ∈ A, w i = 0 := by
  classical
  let s : (J → F) → Finset J := fun u => A.filter (fun i => u i ≠ 0)
  have hex : ∃ n, ∃ u, M u ∧ L u ≠ 0 ∧ (s u).card = n := ⟨_, v, hv, hLv, rfl⟩
  obtain ⟨v', hMv', hLv', hcard⟩ := Nat.find_spec hex
  refine ⟨v', hMv', hLv', ?_⟩
  have hmin : ∀ u, M u → L u ≠ 0 → s u ⊆ s v' → s u ≠ s v' → False := by
    intro u hMu hLu hsub hne
    have hlt : (s u).card < (s v').card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    rw [hcard] at hlt
    exact Nat.find_min hex hlt ⟨u, hMu, hLu, rfl⟩
  intro w hMw hsupp i₀ hi₀ hv'i₀ hwi₀ j hj
  by_contra hwj
  have hv'j : v' j ≠ 0 := fun h => hwj (hsupp j hj h)
  by_cases hLw : L w = 0
  · have hMu : M (fun i => v' i - v' j / w j * w i) := hM v' w _ hMv' hMw
    have hLu : L (fun i => v' i - v' j / w j * w i) ≠ 0 := by
      rw [hL v' w, hLw, mul_zero, sub_zero]
      exact hLv'
    apply hmin _ hMu hLu
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      refine ⟨hi.1, fun h => hi.2 ?_⟩
      rw [h, hsupp i hi.1 h, mul_zero, sub_zero]
    · intro heq
      have hjs : j ∈ s v' := by simp [s, hj, hv'j]
      rw [← heq] at hjs
      simp only [s, Finset.mem_filter] at hjs
      exact hjs.2 (by rw [div_mul_cancel₀ _ hwj, sub_self])
  · apply hmin w hMw hLw
    · intro i hi
      simp only [s, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, fun h => hi.2 (hsupp i hi.1 h)⟩
    · intro heq
      have hi₀s : i₀ ∈ s v' := by simp [s, hi₀, hv'i₀]
      rw [← heq] at hi₀s
      simp [s, hwi₀] at hi₀s

theorem exists_weighted_relation :
    ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by
  intro F T X _ _ c σ φ S p q hmul hone hσc hσφ hrel hsum
  classical
  have hcinv : ∀ t χ, c t χ * c t⁻¹ χ = 1 := by
    intro t χ
    rw [← hmul, mul_inv_cancel, hone]
  obtain ⟨v', hMv', hLv', hmin⟩ := exists_minimal_support (S.disjSum S)
    (fun v : X ⊕ X → F => ∀ t, φ t * ∑ χ ∈ S, c t χ * v (Sum.inl χ) = ∑ χ ∈ S, c t χ * v (Sum.inr χ))
    (fun v => ∑ χ ∈ S, v (Sum.inl χ))
    (by
      intro v w a hv hw t
      have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t χ * (g χ - a * h χ)
          = ∑ χ ∈ S, c t χ * g χ - a * ∑ χ ∈ S, c t χ * h χ := by
        intro g h
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun χ _ => by ring
      rw [e1 (fun χ => v (Sum.inl χ)) (fun χ => w (Sum.inl χ)),
        e1 (fun χ => v (Sum.inr χ)) (fun χ => w (Sum.inr χ))]
      linear_combination hv t - a * hw t)
    (by
      intro v w a
      rw [Finset.sum_sub_distrib, Finset.mul_sum])
    (Sum.elim p q) (fun t => hrel t) hsum
  obtain ⟨χ₀, hχ₀S, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hLv'
  set r := v' (Sum.inl χ₀) with hrdef
  have htw : ∀ t, ∀ t', φ t' * ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inl χ)))
      = ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * σ t (v' (Sum.inr χ))) := by
    intro t t'
    have h := congrArg (σ t) (hMv' (t' * t⁻¹))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, hσc, hσφ, inv_mul_cancel_right, hmul] at h
    have e : ∀ g : X → F, ∑ χ ∈ S, c t' χ * (c t⁻¹ χ * g χ) = ∑ χ ∈ S, c t' χ * c t⁻¹ χ * g χ :=
      fun g => Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
    rw [e (fun χ => σ t (v' (Sum.inl χ))), e (fun χ => σ t (v' (Sum.inr χ)))]
    exact h
  have hfin : ∀ t, ∀ i ∈ S.disjSum S,
      σ t (r⁻¹ * v' i) * c t χ₀ = c t (Sum.elim id id i) * (r⁻¹ * v' i) := by
    intro t i hi
    have hsr : σ t r ≠ 0 := (map_ne_zero (σ t)).mpr hr
    have hz := hmin (fun j => c t⁻¹ (Sum.elim id id j) * σ t (v' j) - c t⁻¹ χ₀ * σ t r / r * v' j)
      (fun t' => by
        have e1 : ∀ g h : X → F, ∑ χ ∈ S, c t' χ * (g χ - c t⁻¹ χ₀ * σ t r / r * h χ)
            = ∑ χ ∈ S, c t' χ * g χ - c t⁻¹ χ₀ * σ t r / r * ∑ χ ∈ S, c t' χ * h χ := by
          intro g h
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun χ _ => by ring
        simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
        rw [e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inl χ))) (fun χ => v' (Sum.inl χ)),
          e1 (fun χ => c t⁻¹ χ * σ t (v' (Sum.inr χ))) (fun χ => v' (Sum.inr χ))]
        linear_combination htw t t' - c t⁻¹ χ₀ * σ t r / r * hMv' t')
      (by
        intro j _ hj
        simp [hj])
      (Sum.inl χ₀) (Finset.inl_mem_disjSum.mpr hχ₀S) hr
      (by
        show c t⁻¹ χ₀ * σ t r - c t⁻¹ χ₀ * σ t r / r * r = 0
        rw [div_mul_cancel₀ _ hr, sub_self])
      i hi
    have e' : r * (c t⁻¹ (Sum.elim id id i) * σ t (v' i)) = c t⁻¹ χ₀ * σ t r * v' i := by
      have hz' : c t⁻¹ (Sum.elim id id i) * σ t (v' i) = c t⁻¹ χ₀ * σ t r / r * v' i :=
        sub_eq_zero.mp hz
      rw [hz']
      field_simp
    have hc := hcinv t (Sum.elim id id i)
    have hc0 := hcinv t χ₀
    have h1 : σ t r * (σ t r)⁻¹ = 1 := mul_inv_cancel₀ hsr
    have h2 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
    rw [map_mul, map_inv₀]
    linear_combination ((σ t r)⁻¹ * r⁻¹ * c t (Sum.elim id id i) * c t χ₀) * e'
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀ * c t (Sum.elim id id i) * c t⁻¹ (Sum.elim id id i)) * h2
      - ((σ t r)⁻¹ * σ t (v' i) * c t χ₀) * hc
      + (r⁻¹ * c t (Sum.elim id id i) * v' i * c t χ₀ * c t⁻¹ χ₀) * h1
      + (r⁻¹ * c t (Sum.elim id id i) * v' i) * hc0
  refine ⟨χ₀, fun χ => r⁻¹ * v' (Sum.inl χ), fun χ => r⁻¹ * v' (Sum.inr χ), ?_, ?_, ?_⟩
  · rw [← Finset.mul_sum]
    exact mul_ne_zero (inv_ne_zero hr) hLv'
  · have h1 := hMv' 1
    simp only [hone, _root_.one_mul] at h1
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← h1]
    ring
  · intro t χ hχ
    exact ⟨by simpa only [Sum.elim_inl, id_eq] using hfin t (Sum.inl χ) (Finset.inl_mem_disjSum.mpr hχ),
      by simpa only [Sum.elim_inr, id_eq] using hfin t (Sum.inr χ) (Finset.inr_mem_disjSum.mpr hχ)⟩

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightedRelationOfMinimalSupportStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weighted_relation_of_minimal_support : ∀ (F T X : Type) [Field F] [Group T] (c : T → X → F) (σ : T → F →+* F) (φ : T → F) (S : Finset X) (p q : X → F), (∀ t t' χ, c (t * t') χ = c t χ * c t' χ) → (∀ χ, c 1 χ = 1) → (∀ t t' χ, σ t (c t' χ) = c t' χ) → (∀ t t', σ t (φ t') = φ (t' * t)) → (∀ t, φ t * ∑ χ ∈ S, c t χ * p χ = ∑ χ ∈ S, c t χ * q χ) → ∑ χ ∈ S, p χ ≠ 0 → ∃ (χ₀ : X) (p' q' : X → F), ∑ χ ∈ S, p' χ ≠ 0 ∧ φ 1 * ∑ χ ∈ S, p' χ = ∑ χ ∈ S, q' χ ∧ ∀ t, ∀ χ ∈ S, σ t (p' χ) * c t χ₀ = c t χ * p' χ ∧ σ t (q' χ) * c t χ₀ = c t χ * q' χ := by
  first | exact @GlobalTheory.SS.exists_weighted_relation | exact GlobalTheory.SS.exists_weighted_relation | (intros; apply GlobalTheory.SS.exists_weighted_relation <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.WtRat

section
variable {k : Type} [Field k] {X : Type} [AddCommGroup X] {R : Type} [CommRing R] {s : Sp R ⟶ Sp k}

def chr (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) : R :=
  ev (R := R) t.left ⊤ le_top (charUnit (Sp k) X χ).val

theorem chr_eq (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr t χ = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (splitTorusPointsEquiv (Sp k) X (Over.mk s) t (Multiplicative.ofAdd χ)).val := by
  rw [splitTorusPointsEquiv_val]
  exact ev_top (R := R) t.left le_top _

theorem chr_mul (t t' : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr (t * t') χ = chr t χ * chr t' χ := by
  rw [chr_eq, chr_eq, chr_eq, map_mul, MonoidHom.mul_apply, Units.val_mul]
  exact map_mul _ _ _

theorem chr_one (χ : X) : chr (1 : Over.mk s ⟶ splitTorus (Sp k) X) χ = 1 := by
  rw [chr_eq, map_one, MonoidHom.one_apply, Units.val_one]
  exact map_one _

theorem chr_add (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ χ' : X) :
    chr t (χ + χ') = chr t χ * chr t χ' := by
  rw [chr_eq, chr_eq, chr_eq, ofAdd_add, map_mul, Units.val_mul]
  exact map_mul _ _ _

theorem chr_zero (t : Over.mk s ⟶ splitTorus (Sp k) X) : chr t 0 = 1 := by
  rw [chr_eq, ofAdd_zero, map_one, Units.val_one]
  exact map_one _

theorem chr_ext {t t' : Over.mk s ⟶ splitTorus (Sp k) X} (h : ∀ χ, chr t χ = chr t' χ) : t = t' := by
  refine (splitTorusPointsEquiv (Sp k) X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1 ?_
  exact (chr_eq t χ.toAdd).symm.trans ((h _).trans (chr_eq t' χ.toAdd))

theorem chr_comp {R' : Type} [CommRing R'] {s' : Sp R' ⟶ Sp k} (e : R →+* R') (he : spMap e ≫ s = s')
    (t : Over.mk s ⟶ splitTorus (Sp k) X) (χ : X) :
    chr ((Over.homMk (spMap e) he : Over.mk s' ⟶ Over.mk s) ≫ t) χ = e (chr t χ) :=
  ev_spMap e t.left ⊤ le_top le_top _

theorem exists_chr (s : Sp R ⟶ Sp k) (u : Multiplicative X →* R) :
    ∃ t : Over.mk s ⟶ splitTorus (Sp k) X, ∀ χ, chr t χ = u (Multiplicative.ofAdd χ) := by
  refine ⟨(splitTorusPointsEquiv (Sp k) X (Over.mk s)).symm
    (MonoidHom.toHomUnits ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom.comp u)), fun χ => ?_⟩
  rw [chr_eq, MulEquiv.apply_symm_apply]
  exact congrArg (fun q => CommRingCat.Hom.hom q (u (Multiplicative.ofAdd χ)))
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
end

theorem exists_rel {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp k) X ⟶ G) {F : Type} [Field F] {s : Sp F ⟶ Sp k} (g : Over.mk s ⟶ G)
    (U : G.left.Opens) (f : Γ(G.left, U)) (h₁ : ⊤ ≤ (((1 : Over.mk s ⟶ splitTorus (Sp k) X) ≫ i) * g).left ⁻¹ᵁ U) :
    ∃ (S : Finset X) (p q : X → F), ∑ χ ∈ S, p χ ≠ 0 ∧
      ∀ (t : Over.mk s ⟶ splitTorus (Sp k) X) (h : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U),
        ev (R := F) ((t ≫ i) * g).left U h f * ∑ χ ∈ S, chr t χ * p χ = ∑ χ ∈ S, chr t χ * q χ := by
  classical
  let R := AddMonoidAlgebra F X
  let sR : Sp R ⟶ Sp k := spMap (algebraMap F R) ≫ s
  let π : Over.mk sR ⟶ Over.mk s := Over.homMk (spMap (algebraMap F R)) rfl
  obtain ⟨tR, htR⟩ := exists_chr (X := X) sR (AddMonoidAlgebra.of F X)
  let a : Over.mk sR ⟶ G := (tR ≫ i) * (π ≫ g)
  let cH (t : Over.mk s ⟶ splitTorus (Sp k) X) : Multiplicative X →* F :=
    { toFun := fun χ => chr t χ.toAdd, map_one' := chr_zero t, map_mul' := fun x y => chr_add t _ _ }
  let e (t : Over.mk s ⟶ splitTorus (Sp k) X) : R →+* F := (AddMonoidAlgebra.lift F F X (cH t)).toRingHom
  have hid (t) : spMap (e t) ≫ spMap (algebraMap F R) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact (AddMonoidAlgebra.lift F F X (cH t)).commutes x
  have he (t) : spMap (e t) ≫ sR = s := by
    rw [← Category.assoc, hid, Category.id_comp]
  have ha (t) : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ a = (t ≫ i) * g := by
    have h1 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ tR = t := by
      refine chr_ext fun χ => ?_
      rw [chr_comp, htR]
      exact AddMonoidAlgebra.lift_of (cH t) (Multiplicative.ofAdd χ)
    have h2 : (Over.homMk (spMap (e t)) (he t) : Over.mk s ⟶ Over.mk sR) ≫ π = 𝟙 _ :=
      Over.OverMorphism.ext (hid t)
    rw [MonObj.comp_mul, ← Category.assoc, h1, ← Category.assoc, h2, Category.id_comp]
  have ha' (t) : spMap (e t) ≫ a.left = ((t ≫ i) * g).left := congrArg CommaMorphism.left (ha t)
  have hx : spMap (e 1) (IsLocalRing.closedPoint F) ∈ a.left ⁻¹ᵁ U := by
    have := h₁ (show IsLocalRing.closedPoint F ∈ (⊤ : (Sp F).Opens) from trivial)
    rw [← ha'] at this
    exact this
  obtain ⟨α, β, hβ, hαβ⟩ := GlobalTheory.T.exists_fraction_evalSection_affine_near_point R (a.left ⁻¹ᵁ U) ((a.left.appLE U _ le_rfl).hom f) _ hx
  have hsum (t) (w : R) (S : Finset X) (hS : w.coeff.support ⊆ S) : e t w = ∑ χ ∈ S, chr t χ * w.coeff χ := by
    show AddMonoidAlgebra.lift F F X (cH t) w = _
    rw [AddMonoidAlgebra.lift_apply, Finsupp.sum_of_support_subset _ hS _ (by simp)]
    exact Finset.sum_congr rfl fun χ _ => mul_comm _ _
  refine ⟨α.coeff.support ∪ β.coeff.support, β.coeff, α.coeff, ?_, fun t h => ?_⟩
  · have h2 := hsum 1 β _ (Finset.subset_union_right (s₁ := α.coeff.support))
    simp only [chr_one, _root_.one_mul] at h2
    rw [← h2]
    intro h0
    refine hβ ?_
    show e 1 β ∈ IsLocalRing.maximalIdeal F
    rw [h0]; exact zero_mem _
  · rw [← hsum t β _ Finset.subset_union_right, ← hsum t α _ Finset.subset_union_left]
    have h' : ⊤ ≤ (spMap (e t) ≫ a.left) ⁻¹ᵁ U := by rw [ha']; exact h
    refine Eq.trans ?_ (hαβ F (e t) h')
    congr 1
    exact (ev_congr (ha' t).symm U h h' f).trans (ev_appLE (spMap (e t)) a.left U _ le_rfl h' h' f).symm

theorem exists_ratio_of_weight_sums : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by
  intro k _ _ G _ hG X _ _ _ i hi U f hU
  obtain ⟨hc, hs, -, -, hgc⟩ := hG
  have : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  obtain ⟨F, _, g₀, hg, hinj, hσ, hsec⟩ := GlobalTheory.T.exists_generic_functionField_point G.left
  let s : Sp F ⟶ Sp k := g₀ ≫ G.hom
  let g : Over.mk s ⟶ G := Over.homMk g₀ rfl
  let pt (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) : Over.mk s ⟶ splitTorus (Sp k) X := toUnit _ ≫ t
  have pt_mul (t t') : pt (t * t') = pt t * pt t' := MonObj.comp_mul _ _ _
  have pt_one : pt 1 = 1 := MonObj.comp_one _
  have hτ (t) : g₀ ≫ (transl (t ≫ i)).hom.left = ((pt t ≫ i) * g).left := by
    have : g ≫ (transl (t ≫ i)).hom = (pt t ≫ i) * g := by
      show g ≫ ((toUnit G ≫ t ≫ i) * 𝟙 G) = _
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, ← Category.assoc]
    exact congrArg CommaMorphism.left this
  choose σ hσ' using fun t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X =>
    hσ ((Over.forget _).mapIso (transl (t ≫ i)))
  replace hσ' (t) : spMap (σ t) ≫ g₀ = ((pt t ≫ i) * g).left := (hσ' t).trans (hτ t)
  have hσs (t) : spMap (σ t) ≫ s = s := by
    show spMap (σ t) ≫ g₀ ≫ G.hom = s
    rw [← Category.assoc, hσ']
    exact Over.w _
  have hσpt (t t') : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ pt t' = pt t' := by
    show _ ≫ toUnit _ ≫ t' = _
    rw [← Category.assoc, comp_toUnit]
  have hσg (t t') : spMap (σ t) ≫ ((pt t' ≫ i) * g).left = ((pt (t' * t) ≫ i) * g).left := by
    have h1 : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ g = (pt t ≫ i) * g :=
      Over.OverMorphism.ext (hσ' t)
    have : (Over.homMk (spMap (σ t)) (hσs t) : Over.mk s ⟶ Over.mk s) ≫ ((pt t' ≫ i) * g) =
        (pt (t' * t) ≫ i) * g := by
      rw [MonObj.comp_mul, ← Category.assoc, hσpt, h1, pt_mul, MonObj.mul_comp, _root_.mul_assoc]
    exact congrArg CommaMorphism.left this
  have hgt (t) (V : G.left.Opens) (hV : (V : Set G.left).Nonempty) : ⊤ ≤ ((pt t ≫ i) * g).left ⁻¹ᵁ V := by
    rw [← hτ]
    obtain ⟨x, hx⟩ := hV
    obtain ⟨y, rfl⟩ := ((Over.forget _).mapIso (transl (t ≫ i))).hom.surjective x
    exact hg ((transl (t ≫ i)).hom.left ⁻¹ᵁ V) ⟨y, hx⟩
  have hone : ((pt 1 ≫ i) * g).left = g₀ := by
    rw [pt_one, MonObj.one_comp, _root_.one_mul]; rfl
  obtain ⟨S, p, q, hp, hrel⟩ := exists_rel i g U f (pt_one ▸ hgt 1 U hU)
  obtain ⟨χ₀, p', q', hp', hφ, hw⟩ := GlobalTheory.T.exists_weighted_relation_of_minimal_support F _ X (fun t χ => chr (pt t) χ) σ
    (fun t => ev (R := F) ((pt t ≫ i) * g).left U (hgt t U hU) f) S p q
    (fun t t' χ => by rw [pt_mul, chr_mul]) (fun χ => by rw [pt_one, chr_one])
    (fun t t' χ => by rw [← chr_comp (σ t) (hσs t), hσpt])
    (fun t t' => (ev_spMap (σ t) _ U _ (hσg t t' ▸ hgt (t' * t) U hU) f).symm.trans
      (ev_congr (hσg t t') U _ _ f))
    (fun t => hrel (pt t) _) hp
  let ε := S.equivFin.symm
  have hε (r : X → F) : ∑ j, r (ε j) = ∑ χ ∈ S, r χ := by
    rw [← Finset.sum_coe_sort S r]
    exact Equiv.sum_comp ε fun x : S => r x
  obtain ⟨U', hU', u, hle, hu⟩ := hsec U hU (Option (Fin S.card ⊕ Fin S.card))
    (fun o => o.elim (∑ χ ∈ S, p' χ) (Sum.elim (fun j => q' (ε j)) fun j => p' (ε j)))
  have hwt (v : Γ(G.left, U')) (χ : X) (r : F) (hv : ev g₀ U' (hg U' hU') v = r)
      (hr : ∀ t, σ t r * chr (pt t) χ₀ = chr (pt t) χ * r) : Wt i U' v (χ - χ₀) := by
    refine GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints k G hs X i F s g hg U' v _ fun t h₁ h₂ => ?_
    have h3 : ev (R := F) ((pt t ≫ i) * g).left U' h₁ v = σ t r :=
      (ev_congr (hσ' t).symm U' h₁ (hσ' t ▸ h₁) v).trans
        ((ev_spMap (σ t) g₀ U' (hg U' hU') _ v).trans (congrArg (σ t) hv))
    have h4 : chr (pt t) χ₀ * chr (pt t) (-χ₀) = 1 := by rw [← chr_add, add_neg_cancel, chr_zero]
    refine h3.trans (Eq.trans ?_ (congrArg (chr (pt t) (χ - χ₀) * ·) hv.symm))
    rw [sub_eq_add_neg, chr_add]
    linear_combination chr (pt t) (-χ₀) * hr t - σ t r * h4
  have hun (o) : u o = 0 ∨ IsUnit (u o) := by
    refine (eq_or_ne _ 0).imp (fun h => hinj U' hU' ?_) (hu o).2
    rw [(hu o).1, h, map_zero]
  have hb : ev g₀ U' (hg U' hU') (∑ j, u (some (Sum.inr j))) = ∑ χ ∈ S, p' χ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu _).1
  refine ⟨U', hle, S.card, fun j => u (some (Sum.inl j)), fun j => u (some (Sum.inr j)), fun j => ε j - χ₀, hU',
    fun j => ⟨hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).2, hwt _ _ _ (hu _).1 fun t => (hw t _ (ε j).2).1,
      hun _, hun _⟩, ?_, hinj U' hU' ?_⟩
  · rw [hinj U' hU' (hb.trans (hu none).1.symm)]
    exact (hu none).2 hp'
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hb, ev_res g₀ hle _ (hg U hU), ← ev_congr hone U (hgt 1 U hU), hφ, map_sum, ← hε]
    exact Finset.sum_congr rfl fun j _ => (hu (some (Sum.inl j))).1.symm

end GlobalTheory.SS.WtRat
end
