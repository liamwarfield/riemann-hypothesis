module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLIPreimageMono
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extLI_preimage_le {X X' Y : Scheme.{0}} (a : Y ⟶ X') (f : X' ⟶ X) (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X.Opens) : a ⁻¹ᵁ (f ⁻¹ᵁ W) ≤ α ⁻¹ᵁ W := by
  intro y hy
  show α y ∈ W
  rw [← e, Scheme.Hom.comp_apply]
  exact hy

theorem extLI_le_chart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (W : X'.Opens) (j : L.ι) (hW : W ≤ f ⁻¹ᵁ L.U j) :
    a ⁻¹ᵁ W ≤ LB.wchart L (K := Fin 1) (fun _ => α) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => extLI_preimage_le a f α e (L.U j) (hW hy)

theorem extLI_le_wchart {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α)
    (j : Fin 1 → L.ι) :
    a ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j ≤ LB.wchart L (K := Fin 1) (fun _ => α) j :=
  fun _ hy => Set.mem_iInter.2 fun k => extLI_preimage_le a f α e (L.U (j k)) (Set.mem_iInter.1 hy k)

theorem extLI_preimage_mono {X Y : Scheme.{0}} (a : Y ⟶ X) {V V' : X.Opens} (hV : V ≤ V') : a ⁻¹ᵁ V ≤ a ⁻¹ᵁ V' :=
  fun _ hz => hV hz

theorem extLI_res_res {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (h3 : W ≤ U) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE h3).op).hom x := by
  change (Y.presheaf.map (homOfLE h1).op ≫ Y.presheaf.map (homOfLE h2).op).hom x = _
  rw [← Functor.map_comp]
  rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem imgLoc_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U U' : X.Opens} (i : U' ⟶ U)
    (j : a ⁻¹ᵁ U' ⟶ a ⁻¹ᵁ U) (y : Γ(X, U)) :
    (Y.presheaf.map j.op).hom ((a.app U).hom y) = (a.app U').hom ((X.presheaf.map i.op).hom y) := by
  have hj : j = (TopologicalSpace.Opens.map a.base).map i := Subsingleton.elim _ _
  subst hj
  have e := a.naturality i.op
  have := congrArg (fun f => f.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

theorem imgLoc_exists {X Y : Scheme.{0}} (a : Y ⟶ X) (hinj : ∀ U : X.Opens, Function.Injective (a.app U).hom)
    (V : X.Opens) {B : Type} (W : B → X.Opens) (hV : V ≤ ⨆ b, W b) (x : Γ(Y, a ⁻¹ᵁ V))
    (hx : ∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) :
    ∃ y : Γ(X, V), (a.app V).hom y = x := by
  choose y hy using hx
  have hcov : V ≤ ⨆ b, V ⊓ W b := by
    calc V ≤ V ⊓ ⨆ b, W b := le_inf le_rfl hV
      _ = ⨆ b, V ⊓ W b := inf_iSup_eq _ _
  have key : ∀ b (U' : X.Opens) (i : U' ⟶ V ⊓ W b), (a.app U').hom ((X.presheaf.map i.op).hom (y b)) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a (i.le.trans inf_le_left))).op).hom x := by
    intro b U' i
    rw [← imgLoc_app_res a i (homOfLE (extLI_preimage_mono a i.le)), hy b, extLI_res_res]
  have compat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun b => V ⊓ W b) y := by
    intro b c
    apply hinj
    exact (key b _ _).trans (key c _ _).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun b => V ⊓ W b) V
    (fun b => homOfLE inf_le_left) hcov y compat
  have hcovY : a ⁻¹ᵁ V ≤ ⨆ b, a ⁻¹ᵁ (V ⊓ W b) := by
    intro z hz
    obtain ⟨b, hb⟩ := (TopologicalSpace.Opens.mem_iSup).1 (hcov hz)
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨b, hb⟩
  have hs' : ∀ b, (X.presheaf.map (homOfLE inf_le_left : V ⊓ W b ⟶ V).op).hom s = y b := hs
  refine ⟨s, ?_⟩
  refine Y.sheaf.eq_of_locally_eq' (fun b => a ⁻¹ᵁ (V ⊓ W b)) (a ⁻¹ᵁ V)
    (fun b => homOfLE (extLI_preimage_mono a inf_le_left)) hcovY _ _ (fun b => ?_)
  have h2 := imgLoc_app_res a (homOfLE inf_le_left : V ⊓ W b ⟶ V)
    (homOfLE (extLI_preimage_mono a inf_le_left)) s
  rw [hs' b, hy b] at h2
  exact h2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreimageOfLocalPreimagesInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_of_local_preimages_injective : ∀ {X Y : Scheme.{0}} (a : Y ⟶ X), (∀ U : X.Opens, Function.Injective (a.app U).hom) → ∀ (V : X.Opens) {B : Type} (W : B → X.Opens), V ≤ ⨆ b, W b → ∀ (x : Γ(Y, a ⁻¹ᵁ V)), (∀ b, ∃ y : Γ(X, V ⊓ W b), (a.app (V ⊓ W b)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_mono a (inf_le_left : V ⊓ W b ≤ V))).op).hom x) → ∃ y : Γ(X, V), (a.app V).hom y = x := by
  first | exact @GlobalTheory.Mum.imgLoc_exists | exact GlobalTheory.Mum.imgLoc_exists | (intros; apply GlobalTheory.Mum.imgLoc_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralSectionsExtendOverFiniteModificat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLifts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLifts
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
theorem secLift_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (a.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a h)).op).hom ((a.app U).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem secLift_comp_app {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)) :
    ((a ≫ f).app U).hom x = (a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x) := by
  simp [Scheme.Hom.comp_app]
  rfl

theorem secLift_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (k : ℤ))).g i j).val =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) j 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (j 0))).hom (L.g (i 0) (j 0)))) ^ k := by
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl
theorem secLift_rr {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem secLift_res_comp {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Z.Opens}
    (h : V ≤ (a ≫ f) ⁻¹ᵁ U) (h' : V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U)) (x : Γ(X, U)) :
    (Z.presheaf.map (homOfLE h).op).hom (((a ≫ f).app U).hom x) =
      (Z.presheaf.map (homOfLE h').op).hom ((a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x)) := by
  rw [secLift_comp_app]
  rfl
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secLift_compat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (s : SecK L φ k) (i i' : Fin 1 → L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (s.f i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (s.f i') := by
  have h := s.compat i i'
  rw [secLift_g] at h
  exact h

def secLift_ofCompat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (σf : ∀ i : Fin 1 → L.ι, Γ(Y, LB.wchart L (K := Fin 1) (fun _ => φ) i))
    (h : ∀ i i' : Fin 1 → L.ι, (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (σf i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (σf i')) :
    SecK L φ k where
  f := σf
  compat i i' := (h i i').trans (congrArg (· * _) (secLift_g L φ k i i').symm)

set_option maxHeartbeats 1000000 in
theorem secK_lift_of_local_lift : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  intro X X' Y L f a α e k hinj s n j W hWtop hW hloc
  subst e
  have step1 : ∀ j' : Fin 1 → L.ι, ∃ y : Γ(X', LB.wchart L (K := Fin 1) (fun _ => f) j'),
      (a.app _).hom y = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a (a ≫ f) rfl j')).op).hom (s.f j') := by
    intro j'
    refine GlobalTheory.T.exists_preimage_of_local_preimages_injective a hinj _ W (by rw [hWtop]; exact le_top) _ ?_
    intro b
    obtain ⟨y, hy⟩ := hloc b
    have h1 : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ f ⁻¹ᵁ (L.U (j' 0) ⊓ L.U (j b)) :=
      fun x hx => ⟨LB.wchart_le L (K := Fin 1) (fun _ => f) j' 0 hx.1, hW b hx.2⟩
    refine ⟨(X'.presheaf.map (homOfLE h1).op).hom ((f.app _).hom (L.g (j' 0) (j b))) ^ k *
      (X'.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ W b)).op).hom y, ?_⟩
    have hc2 := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b) ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) j' ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) (fun _ => j b) from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl j' hx.1, extLI_le_chart L f a (a ≫ f) rfl (W b) (j b) (hW b) hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s j' (fun _ => j b))
    rw [map_mul, map_pow] at hc2
    erw [secLift_rr, secLift_rr, secLift_rr] at hc2
    rw [map_mul, map_pow, secLift_app_res, secLift_app_res, hy]
    erw [secLift_rr, secLift_rr]
    rw [hc2]
    exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f _ _ _ _).symm
  choose σf hσ using step1
  refine ⟨secLift_ofCompat L f k σf fun i i' => ?_, hσ⟩
  apply hinj (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i')
  have hG : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i 0))
      (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i' 0))
  have e1 := secLift_app_res a (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i) (σf i)
  have e2 := secLift_app_res a hG ((f.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))
  have e3 := secLift_app_res a (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i') (σf i')
  rw [map_mul, map_pow, e1]
  erw [e2, e3]
  rw [hσ, hσ]
  erw [secLift_rr, secLift_rr]
  have hc := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i') ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i' from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl i hx.1, extLI_le_wchart L f a (a ≫ f) rfl i' hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s i i')
  rw [map_mul, map_pow] at hc
  erw [secLift_rr, secLift_rr, secLift_rr] at hc
  rw [hc]
  exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f (L.U (i 0) ⊓ L.U (i' 0)) _ _ _)
end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPulledBackPowerSectionOfLocalLiftsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pulledBackPowerSection_of_local_lifts : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  first | exact @GlobalTheory.Mum.secK_lift_of_local_lift | exact GlobalTheory.Mum.secK_lift_of_local_lift | (intros; apply GlobalTheory.Mum.secK_lift_of_local_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSectionsInjectiveFlatIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSectionsInjectiveFlatIntegral
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genFib_preimage_eq_top {S : Scheme.{0}} (F : Type) [Field F] (gp : Sp F ⟶ S) [IsDominant gp]
    (W : S.Opens) (hW : (W : Set S).Nonempty) : gp ⁻¹ᵁ W = ⊤ := by
  obtain ⟨q, hq⟩ := gp.denseRange.exists_mem_open W.isOpen hW
  refine top_unique fun z _ => ?_
  have : z = q := Subsingleton.elim (α := PrimeSpectrum F) z q
  subst this
  exact hq

theorem genFib_appLE_injective {S : Scheme.{0}} [IsIntegral S] (F : Type) [Field F] (gp : Sp F ⟶ S)
    [IsDominant gp] (W : S.Opens) (e : (⊤ : (Sp F).Opens) ≤ gp ⁻¹ᵁ W) :
    Function.Injective (gp.appLE W ⊤ e).hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have h1 : (Sp F).basicOpen (gp.appLE W ⊤ e r) = ⊥ := by rw [hr]; simp
  have h2 : S.basicOpen r = ⊥ := by
    by_contra hne
    have hne' : (S.basicOpen r : Set S).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hne (by ext1; simpa using h)
    have h3 := genFib_preimage_eq_top F gp _ hne'
    have h4 : (Sp F).basicOpen (gp.appLE W ⊤ e r) = ⊤ := by
      rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen, h3]
      simp
    rw [h4] at h1
    have : (⊤ : (Sp F).Opens) ≠ ⊥ := by
      intro h
      have hm : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F) ∈ ((⊤ : (Sp F).Opens) : Set (Sp F)) := trivial
      rw [h] at hm
      exact hm
    exact this h1
  exact (basicOpen_eq_bot_iff r).mp h2

theorem genFib_pushout_inl_injective {A B C : CommRingCat.{0}} (φ : A ⟶ B) (ψ : A ⟶ C) (hφ : φ.hom.Flat)
    (hψ : Function.Injective ψ.hom) : Function.Injective (pushout.inl φ ψ).hom := by
  algebraize [φ.hom, ψ.hom]
  have h' : IsPushout φ ψ (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  have e := h'.inl_isoPushout_inv
  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := C)) :=
    Algebra.TensorProduct.includeLeft_injective hψ
  intro x y hxy
  apply hinj
  have := congrArg (fun z => h'.isoPushout.inv.hom z) hxy
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e] at this
  exact this

theorem genFib_affine_injective {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S)
    (a : Y ⟶ X) (t : Y ⟶ Sp F) (H : IsPullback a t f gp) [Flat f] [IsIntegral S] [IsDominant gp]
    {W : S.Opens} (hW : IsAffineOpen W) (hWne : (W : Set S).Nonempty) {V : X.Opens} (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ W) : Function.Injective (a.appLE V (a ⁻¹ᵁ V) le_rfl).hom := by
  have hT : (⊤ : (Sp F).Opens) ≤ gp ⁻¹ᵁ W := (genFib_preimage_eq_top F gp W hWne).ge
  have hUY : a ⁻¹ᵁ V = a ⁻¹ᵁ V ⊓ t ⁻¹ᵁ ⊤ := by simp
  have hiso := isIso_pushoutSection_of_isAffineOpen H hT e hUY hW (isAffineOpen_top _) hV
  have hfac : a.appLE V (a ⁻¹ᵁ V) le_rfl = pushout.inl _ _ ≫ pushoutSection H hT e hUY := by
    exact (pushout.inl_desc _ _ _).symm
  rw [hfac, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (pushoutSection H hT e hUY)).1.comp
    (genFib_pushout_inl_injective _ _ (f.flat_appLE hW hV e) (genFib_appLE_injective F gp W hT))

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genFib_app_injective : ∀ {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S)
    (a : Y ⟶ X) (t : Y ⟶ Sp F), IsPullback a t f gp → Flat f → IsIntegral S → IsDominant gp →
    ∀ U : X.Opens, Function.Injective (a.app U).hom := by
  intro S X Y F _ f gp a t H hf hS hd U
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  refine X.IsSheaf.section_ext (s := x) (t := 0) fun z hz => ?_
  obtain ⟨W, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show f z ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hzV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show z ∈ U ⊓ f ⁻¹ᵁ W from ⟨hz, hzW⟩)
  have hVU : V ≤ U := hVle.trans inf_le_left
  have e : V ≤ f ⁻¹ᵁ W := hVle.trans inf_le_right
  refine ⟨V, hVU, hzV, ?_⟩
  rw [map_zero]
  apply genFib_affine_injective F f gp a t H hW ⟨f z, hzW⟩ hV e
  rw [map_zero, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE, CommRingCat.comp_apply,
    hx, map_zero]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreSectionsInjectiveFlatIntegralStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibre_sections_injective_flat_integral : ∀ {S X Y : Scheme.{0}} (F : Type) [Field F] (f : X ⟶ S) (gp : Sp F ⟶ S) (a : Y ⟶ X) (t : Y ⟶ Sp F), IsPullback a t f gp → Flat f → IsIntegral S → IsDominant gp → ∀ U : X.Opens, Function.Injective (a.app U).hom := by
  first | exact @GlobalTheory.Mum.genFib_app_injective | exact GlobalTheory.Mum.genFib_app_injective | (intros; apply GlobalTheory.Mum.genFib_app_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_app_eq_sum_mul_of_comm : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  intro X Y S S' T X' g h gp gp' hgp fst snd hsq α t hpb l h1 h2 W U hWU n c b b' hb
  subst h1
  have le : fst ⁻¹ᵁ W ≤ snd ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hsq, Scheme.Hom.comp_preimage]
    exact fun x hx => hWU hx
  refine ⟨∑ m, (fst.app W).hom (c m) * (snd.appLE (h ⁻¹ᵁ U) (fst ⁻¹ᵁ W) le).hom (b' m), ?_⟩
  have hid : ∀ z : Γ(Y, (l ≫ fst) ⁻¹ᵁ W), (Y.presheaf.map (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op).hom z = z := by
    intro z
    have : (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op = 𝟙 (Opposite.op ((l ≫ fst) ⁻¹ᵁ W)) := rfl
    erw [this, Y.presheaf.map_id]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hid, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  rw [← hb m]
  have key : ∀ (f₁ f₂ : Y ⟶ S') (e : f₁ = f₂) (V : Y.Opens) (e₁ e₂), f₁.appLE (h ⁻¹ᵁ U) V e₁ = f₂.appLE (h ⁻¹ᵁ U) V e₂ := by
    intro f₁ f₂ e V e₁ e₂; subst e; rfl
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (b' m)) (key _ _ h2 _ _ _)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_mul_pulledBack_functions_genericFibre_eq : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  first | exact @GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm | exact GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm | (intros; apply GlobalTheory.Mum.exists_app_eq_sum_mul_of_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineChartCoverOverModification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineChartCoverOverModification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finite_affine_chart_cover : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), QuasiCompact G.hom → ∀ (L : LB G.left), L.IsLB → ∃ (n : ℕ) (j : Fin n → L.ι) (W : Fin n → G.left.Opens) (U : Fin n → M.S.Opens), (⨆ b, W b = ⊤) ∧ (∀ b, W b ≤ L.U (j b)) ∧ (∀ b, W b ≤ G.hom ⁻¹ᵁ U b) ∧ (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (U b)) := by
  intro R _ _ M G hG L hL
  haveI := M.proper
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hx : ∀ x : G.left, ∃ (j : L.ι) (W : G.left.Opens) (U : M.S.Opens),
      x ∈ W ∧ W ≤ L.U j ∧ W ≤ G.hom ⁻¹ᵁ U ∧ IsAffineOpen W ∧ IsAffineOpen U := by
    intro x
    have hxt : x ∈ (⊤ : G.left.Opens) := trivial
    rw [← hL.cover] at hxt
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxt
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 M.S.isBasis_affineOpens)
      (show G.hom x ∈ (⊤ : M.S.Opens) from trivial)
    obtain ⟨W, hW, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.left.isBasis_affineOpens)
      (show x ∈ L.U j ⊓ G.hom ⁻¹ᵁ U from ⟨hj, hxU⟩)
    exact ⟨j, W, U, hxW, hWle.trans inf_le_left, hWle.trans inf_le_right, hW, hU⟩
  choose j W U hxW hWj hWU hWa hUa using hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set G.left)) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let e := t.equivFin
  refine ⟨t.card, fun b => j (e.symm b), fun b => W (e.symm b), fun b => U (e.symm b), ?_,
    fun b => hWj _, fun b => hWU _, fun b => hWa _, fun b => hUa _⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨e ⟨y, hy⟩, by simpa using hxy⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAffineChartCoverOverModificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_affine_chart_cover_over_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S), QuasiCompact G.hom → ∀ (L : LB G.left), L.IsLB → ∃ (n : ℕ) (j : Fin n → L.ι) (W : Fin n → G.left.Opens) (U : Fin n → M.S.Opens), (⨆ b, W b = ⊤) ∧ (∀ b, W b ≤ L.U (j b)) ∧ (∀ b, W b ≤ G.hom ⁻¹ᵁ U b) ∧ (∀ b, IsAffineOpen (W b)) ∧ (∀ b, IsAffineOpen (U b)) := by
  first | exact @GlobalTheory.Mum.exists_finite_affine_chart_cover | exact GlobalTheory.Mum.exists_finite_affine_chart_cover | (intros; apply GlobalTheory.Mum.exists_finite_affine_chart_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finite_modif_eq_gp : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h →
    M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp →
    a = c ≫ M'.gp := by
  intro R _ _ M M' h hh e Z a c hac
  haveI := M'.integral
  have cA : ∀ {X Y W : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ W) (x : Γ(W, ⊤)),
      (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  have hsub : Subsingleton (Sp (FractionRing R)) := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let pt : Sp (FractionRing R) := (default : PrimeSpectrum (FractionRing R))
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.S) (U := ⊤) (x := M.gp pt) trivial
  have hgU : ∀ y : Sp (FractionRing R), M.gp y ∈ U := fun y => by rwa [Subsingleton.elim y pt]
  have hV : IsAffineOpen (h ⁻¹ᵁ U) := hU.preimage h
  have ha : Set.range a ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (a z) ∈ U
    rw [← Scheme.Hom.comp_apply, hac, Scheme.Hom.comp_apply]; exact hgU _
  have hg : Set.range M'.gp ⊆ Set.range (h ⁻¹ᵁ U).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    show h (M'.gp z) ∈ U
    rw [← Scheme.Hom.comp_apply, e]; exact hgU _
  obtain ⟨a₀, fa⟩ : ∃ a₀, a₀ ≫ (h ⁻¹ᵁ U).ι = a := ⟨_, IsOpenImmersion.lift_fac _ _ ha⟩
  obtain ⟨g₀, fg⟩ : ∃ g₀, g₀ ≫ (h ⁻¹ᵁ U).ι = M'.gp := ⟨_, IsOpenImmersion.lift_fac _ _ hg⟩
  suffices key : a₀ = c ≫ g₀ by rw [← fa, key, Category.assoc, fg]
  haveI : IsAffine (h ⁻¹ᵁ U) := hV
  have hq1 : a₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = c ≫ jK R := by
    rw [reassoc_of% fa, reassoc_of% hac, M.gp_π]
  have hq2 : g₀ ≫ ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π) = jK R := by
    rw [reassoc_of% fg, reassoc_of% e, M.gp_π]
  have hinj : Function.Injective g₀.appTop.hom := by
    haveI : IsDominant (g₀ ≫ (h ⁻¹ᵁ U).ι) := by rw [fg]; exact M'.dominant
    haveI : IsDominant g₀ := IsDominant.of_comp_of_isOpenImmersion g₀ (h ⁻¹ᵁ U).ι
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx0
    apply eq_zero_of_basicOpen_eq_bot
    by_contra hne
    obtain ⟨y, hy⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    obtain ⟨z, hz⟩ := g₀.denseRange.exists_mem_open (Scheme.basicOpen _ x).isOpen ⟨y, hy⟩
    have hz' : z ∈ g₀ ⁻¹ᵁ Scheme.basicOpen _ x := hz
    have hx0' : (ConcreteCategory.hom (g₀.app ⊤)) x = 0 := hx0
    rw [Scheme.preimage_basicOpen, hx0', Scheme.basicOpen_zero] at hz'
    exact hz'
  have hfrac : ∀ x : Γ(Sp (FractionRing R), ⊤), ∃ r t : Γ(Sp R, ⊤),
      IsUnit ((jK R).appTop.hom t) ∧ x * (jK R).appTop.hom t = (jK R).appTop.hom r := by
    intro x
    have nat : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((jK R).appTop.hom s) =
        algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s) := fun s =>
      congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    have inj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom :=
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.injective
    obtain ⟨r', t', ht', hx'⟩ := IsFractionRing.div_surjective (A := R)
      ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom x)
    have ht0 : algebraMap R (FractionRing R) t' ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht'
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r', (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t', ?_, ?_⟩
    · have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom
          ((jK R).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t'))) := by
        rw [nat]; simpa using ht0
      have := hu.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
      simpa using this
    · apply inj
      rw [map_mul, nat, nat]
      have hi : ∀ s, (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom s) = s :=
        fun s => congrArg (fun φ => φ.hom s) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
      rw [hi, hi, ← hx']
      exact div_mul_cancel₀ _ ht0
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop]
  ext b
  obtain ⟨r, t, ht, hx⟩ := hfrac (g₀.appTop.hom b)
  have e1 : b * ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom t = ((h ⁻¹ᵁ U).ι ≫ h ≫ M.π).appTop.hom r := by
    apply hinj
    rw [map_mul, ← cA, ← cA, hq2, hx]
  have e2 := congrArg a₀.appTop.hom e1
  rw [map_mul, ← cA, ← cA, hq1, cA, cA, ← hx, map_mul] at e2
  exact (IsUnit.mul_left_inj (ht.map c.appTop.hom)).1 e2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorizationThroughFiniteModificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorization_through_finite_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h → M'.gp ≫ h = M.gp → ∀ (Z : Scheme.{0}) (a : Z ⟶ M'.S) (c : Z ⟶ Sp (FractionRing R)), a ≫ h = c ≫ M.gp → a = c ≫ M'.gp := by
  first | exact @GlobalTheory.Mum.finite_modif_eq_gp | exact GlobalTheory.Mum.finite_modif_eq_gp | (intros; apply GlobalTheory.Mum.finite_modif_eq_gp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralSectionsExtendOverFiniteModificat
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

private theorem secK_extend_locInt {X X' Y Z : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (l : Y ⟶ X')
    (α : Y ⟶ X) (e : l ≫ f = α) {k : ℕ} (σ : SecK L f k) (s : SecK L α k) (j' : Fin 1 → L.ι)
    (hσ : (l.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') =
      (Y.presheaf.map (homOfLE (extLI_le_wchart L f l α e j')).op).hom (s.f j'))
    (p' : Z ⟶ Y) (z : Z) (hz : (p' ≫ l) z ∈ LB.wchart L (K := Fin 1) (fun _ => f) j') :
    gs (p' ≫ l) z (LB.wchart L (K := Fin 1) (fun _ => f) j') (σ.f j') =
      gs p' z (LB.wchart L (K := Fin 1) (fun _ => α) j') (s.f j') := by
  have hz' : p' z ∈ LB.wchart L (K := Fin 1) (fun _ => α) j' := extLI_le_wchart L f l α e j' hz
  unfold gs
  rw [dite_eq_left hz, dite_eq_left hz']
  calc _ = (p'.stalkMap z).hom (Y.presheaf.germ (l ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j') (p' z) hz
          ((l.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j'))) :=
        (Scheme.Hom.germ_stalkMap_apply p' _ z hz _).symm
    _ = (p'.stalkMap z).hom (Y.presheaf.germ (l ⁻¹ᵁ LB.wchart L (K := Fin 1) (fun _ => f) j') (p' z) hz
          ((Y.presheaf.map (homOfLE (extLI_le_wchart L f l α e j')).op).hom (s.f j'))) := by rw [hσ]
    _ = (p'.stalkMap z).hom (Y.presheaf.germ (LB.wchart L (K := Fin 1) (fun _ => α) j') (p' z) hz' (s.f j')) := by
        congr 1
        exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
    _ = _ := Scheme.Hom.germ_stalkMap_apply p' _ z hz' _

theorem extend_locInt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, LocInt M G L α t hpb.w (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  obtain ⟨n, j, W, U, hcov, hWj, hWU, hWaff, hUaff⟩ := GlobalTheory.T.exists_finite_affine_chart_cover_over_modification R M G hqc L hL
  have key : ∀ (i : I) (b : Fin n), ∃ (nn : ℕ) (c : Fin nn → Γ(G.left, W b))
      (bb : Fin nn → Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U b)),
      (∀ m, (M.gp.app (U b)).hom.IsIntegralElem (bb m)) ∧
      (Y.presheaf.map (homOfLE (locInt_le_chart L α (j b) (W b) (hWj b))).op).hom ((s i).f (fun _ => j b)) =
        ∑ m, (α.app (W b)).hom (c m) *
          (t.appLE (M.gp ⁻¹ᵁ U b) (α ⁻¹ᵁ W b) (locInt_le_gen G.hom α t M.gp hpb.w (W b) (U b) (hWU b))).hom (bb m) :=
    fun i b => hs i (j b) (W b) (U b) (hWj b) (hWU b) (hWaff b) (hUaff b)
  choose nn c bb hint heq using key
  let Ix := Σ (p : I × Fin n), Fin (nn p.1 p.2)
  let e : Ix ≃ Fin (Nat.card Ix) := Finite.equivFin Ix
  obtain ⟨M', h, hgp, hfin, hπ, hlift⟩ := GlobalTheory.T.exists_finiteModification_integral_elements_regular R M (Nat.card Ix) (fun q => U (e.symm q).1.2)
    (fun q => bb (e.symm q).1.1 (e.symm q).1.2 (e.symm q).2) (fun q => hUaff _) (fun q => hint _ _ _)
  have hlift' : ∀ x : Ix, ∃ cc : Γ(M'.S, h ⁻¹ᵁ U x.1.2),
      (M'.gp.appLE (h ⁻¹ᵁ U x.1.2) (M.gp ⁻¹ᵁ U x.1.2) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U x.1.2))).hom cc =
        bb x.1.1 x.1.2 x.2 := by
    intro x
    have hx := hlift (e x)
    rw [Equiv.symm_apply_apply] at hx
    exact hx
  choose cc hcc using hlift'
  refine ⟨M', h, hfin, hgp, hπ, fun i => ?_⟩
  obtain ⟨l, hl1, hl2⟩ : ∃ l : Y ⟶ pullback G.hom h,
      l ≫ pullback.fst G.hom h = α ∧ l ≫ pullback.snd G.hom h = t ≫ M'.gp :=
    ⟨pullback.lift α (t ≫ M'.gp) (by rw [hpb.w, Category.assoc, hgp]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hout : IsPullback (l ≫ pullback.fst G.hom h) t G.hom (M'.gp ≫ h) := by
    rw [hl1, hgp]; exact hpb
  have hpb' : IsPullback l t (pullback.snd G.hom h) M'.gp :=
    IsPullback.of_right hout hl2 (IsPullback.of_hasPullback G.hom h)
  haveI := hsm
  haveI : Flat G.hom := inferInstance
  have hflat : Flat (pullback.snd G.hom h) := inferInstance
  have hinj := GlobalTheory.T.genericFibre_sections_injective_flat_integral (FractionRing R) (pullback.snd G.hom h) M'.gp l t hpb' hflat M'.integral M'.dominant
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_pulledBackPowerSection_of_local_lifts L (pullback.fst G.hom h) l α hl1 (k i) hinj (s i) n j
    (fun b => pullback.fst G.hom h ⁻¹ᵁ W b) ((pullback.fst G.hom h).iSup_preimage_eq_top hcov)
    (fun b => extLI_preimage_mono _ (hWj b)) (fun b => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.sum_mul_pulledBack_functions_genericFibre_eq G.hom h M.gp M'.gp hgp (pullback.fst G.hom h) (pullback.snd G.hom h)
        pullback.condition α t hpb.w l hl1 hl2 (W b) (U b) (hWU b) (nn i b) (c i b) (bb i b)
        (fun m => cc ⟨(i, b), m⟩) (fun m => hcc ⟨(i, b), m⟩)
      refine ⟨y, hy.trans ?_⟩
      rw [← heq i b]
      exact extLI_res_res _ _ _ _)
  refine ⟨σ, ?_⟩
  intro Z p p' hp z J hJ
  have hp2 : p ≫ pullback.snd G.hom h = p' ≫ t ≫ M'.gp := by
    have := GlobalTheory.T.factorization_through_finite_modification R M M' h hfin hgp Z (p ≫ pullback.snd G.hom h) (p' ≫ t) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hp, Category.assoc, hpb.w, Category.assoc])
    rw [this, Category.assoc]
  have hpl : p = p' ≫ l := pullback.hom_ext (by rw [hp, Category.assoc, hl1]) (by rw [hp2, Category.assoc, hl2])
  subst hpl
  unfold sval
  simp only []
  rw [Category.assoc, hl1]
  have hJ' : ∀ ψ : Z ⟶ G.left, ψ z ∈ L.U (J ψ) := hJ
  have hz : (p' ≫ l) z ∈ LB.wchart L (K := Fin 1) (fun _ => pullback.fst G.hom h) (fun _ => J (p' ≫ α)) := by
    unfold LB.wchart
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    intro _
    convert hJ' (p' ≫ α) using 1
    rw [← hl1]
    simp
  exact secK_extend_locInt L (pullback.fst G.hom h) l α hl1 σ (s i) _ (hσ _) p' z hz

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralSectionsExtendOverFiniteModificatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyIntegralSections_extend_over_finiteModification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, LocInt M G L α t hpb.w (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  first | exact @GlobalTheory.Mum.extend_locInt | exact GlobalTheory.Mum.extend_locInt | (intros; apply GlobalTheory.Mum.extend_locInt <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem extend_finiteModif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (I : Type) [Finite I] (k : I → ℕ) (s : ∀ i, SecK L α (k i)), (∀ i, TraitReg M G L (s i)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S), IsFinite h ∧ M'.gp ≫ h = M.gp ∧ h ≫ M.π = M'.π ∧ ∀ i, ∃ σ : SecK L (pullback.fst G.hom h) (k i), Agree L σ (s i) := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb I _ k s hs
  exact GlobalTheory.T.locallyIntegralSections_extend_over_finiteModification R M G hsm hqc hgi L hL Y α t hpb I k s
    (fun i => GlobalTheory.T.locallyIntegral_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb (k i) (s i) (hs i))

end GlobalTheory.Mum
