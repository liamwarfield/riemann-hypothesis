module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecsOfIntFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.LinearRestriction.ResPullUVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullPt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def IsPullPt {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg φ D D') {T : Over (Sp R)} {T' : Over (Sp R')} (h : T'.left ⟶ T.left) (ξ : GtPt D T) (ξ' : GtPt D' T') : Prop :=
  ξ'.b.left ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ ξ.b.left ∧
  ∀ χ : D'.X, ∃ hψ : ∀ κ : Fin 4,
      DegPre.gtφT D' T' ξ'.b χ κ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = h ≫ DegPre.gtφT D T ξ.b (hD.xe χ) κ,
    LB.Gen.Maps (LB.linCombIso hD.w _ DegPre.gtε) (ξ'.s χ)
      (GeneratorPullback.pullAlong D.P.L (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) h _ DegPre.gtε _ hψ (ξ.s (hD.xe χ)))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLeadValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackThickeningOfCarriesTorusCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackThickeningOfCarriesTorusCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.FormalModel

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusModel GlobalTheory.ConstLin

section Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {D : DegPre R}
  {D' : DegPre R'} {F : D'.P.A.left ⟶ D.P.A.left} {w : LB.Iso D'.P.L (D.P.L.pull F)} {ε : D'.X → D.X}

theorem thru_pull_iff {T T₀ : Over (Sp R)} {T' : Over (Sp R')} (k : T₀ ⟶ T) {g : GtPt D T} {g₀ : GtPt D T₀}
    (hk : GtPt.IsPull k.left g g₀) (h : T'.left ⟶ T₀.left) (ξ : GtPt D' T') :
    Thru w ε h g₀ ξ ↔ Thru w ε (h ≫ k.left) g ξ := by
  have hb : k ≫ g.b = g₀.b := Over.OverMorphism.ext hk.1.symm
  refine forall_congr' fun y => and_congr (forall_congr' fun j => ?_) (forall_congr' fun Z => forall_congr' fun r =>
    forall_congr' fun z => forall_congr' fun J => forall_congr' fun J' => forall_congr' fun hJ => ?_)
  · rw [Category.assoc, ConstTanRed.comp_gtφT D k g.b g₀.b hb]
  · rw [(val_corr hJ (hk.2 (ε y)) (r ≫ h)).trans (val_pull hJ _ _ _), Category.assoc]

theorem eq_of_thru {Y : Over (Sp R)} [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ)
    (hε : Function.Surjective ε) {T' : Over (Sp R')} {r r' : T'.left ⟶ Y.left} {ξ : GtPt D' T'}
    (h : Thru w ε r (Φ Y (𝟙 Y)) ξ) (h' : Thru w ε r' (Φ Y (𝟙 Y)) ξ) : r = r' := by
  refine hom_ext hΦ (((h 0).1 2).symm.trans ((h' 0).1 2)) fun χ z J hJ => ?_
  obtain ⟨χ, rfl⟩ := hε χ
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have a := ((h χ).2 _ (𝟙 _) z J J' hJ hJ').trans ((h' χ).2 _ (𝟙 _) z J J' hJ hJ').symm
  rwa [Category.id_comp, Category.id_comp] at a

end Thru

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R}
  {I : Ideal R'} {E : DegData R' I} {hE : IsPullDeg ρ D E.toPre} {A' : PolAV (Sp (FractionRing R'))}
  {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {Y : Over (Sp R)}

theorem Carries.thru {e : ℕ} {c : GtCoord I E.toPre e G'} {g : GtPt D Y} {φ} (h : Carries hE c g φ)
    {T : Over (Sp (R' ⧸ I ^ (e + 1)))} (x : T ⟶ thickObj R' I e G') :
    Thru hE.w hE.xe (T' := (Over.map (thick R' I e)).obj T) (x.left ≫ φ) g (TorusCoord.toGtPt c x) := by
  have hx := TorusCoord.isPointOf_toGtPt c x
  intro y
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [TorusCoord.gtφT_eq, TorusCoord.gtφT_eq]
    refine TorusCoordPull.Oφ_pull hE g.b (TorusCoord.toGtPt c x).b (x.left ≫ φ) ?_ y k
    rw [hx.1, Category.assoc, h.1, Category.assoc]
  · have o := (TorusCoord.comp_eq_of_left (TorusCoord.toGtPt c x).b c.pG r (r ≫ x.left)
      (by rw [hx.1, Category.assoc])).1 y
    refine (congrArg (fun q => val (g.s (hE.xe y)) q z J) (Category.assoc _ _ _).symm).trans
      ((h.2 y Z (r ≫ x.left) z J J' hJ hJ').trans (congrArg₂ (· * ·)
        (Finset.prod_congr rfl fun k _ => congrArg (fun q => TorusCoordPull.om hE.w z J J' q ^ Oinvε k) (o k).symm) ?_))
    exact ((val_corr hJ' (hx.2 y) r).trans (val_pull hJ' _ _ _)).symm

theorem Carries.isGrpPullback' [GrpObj Y] {Φ : ∀ T, (T ⟶ Y) ≃ GtPt D T} (hΦ : Represents Φ) (U : UnifPre I E A' G')
    {e : ℕ} {φ} (h : Carries hE (U.gt e) (Φ Y (𝟙 Y)) φ) :
    IsGrpPullback (thickObj R' I e G') Y (thick R' I e ≫ spMap ρ) φ := by
  refine ⟨h.isPullback hΦ U, fun T x y x₀ y₀ hx hy => ?_⟩
  let Tw := (Over.map (thick R' I e)).obj T
  let T₀ : Over (Sp R) := Over.mk (T.hom ≫ thick R' I e ≫ spMap ρ)
  let i : Tw.left ⟶ T₀.left := 𝟙 T.left
  have hi : i ≫ T₀.hom = Tw.hom ≫ spMap ρ := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have pl : ∀ k : T₀ ⟶ Y, GtPt.IsPull k.left (Φ Y (𝟙 Y)) (Φ T₀ k) := fun k => by
    have := hΦ.1 _ _ k (𝟙 Y)
    rwa [Category.comp_id] at this
  have key : ∀ (x : T ⟶ thickObj R' I e G') (x₀ : T₀ ⟶ Y), x₀.left = x.left ≫ φ →
      Thru hE.w hE.xe i (Φ T₀ x₀) (TorusCoord.toGtPt (U.gt e) x) := fun x x₀ hx => by
    refine (thru_pull_iff x₀ (pl x₀) i _).2 ?_
    have e₁ : i ≫ x₀.left = x.left ≫ φ := (Category.id_comp _).trans hx
    rw [e₁]
    exact h.thru x
  obtain ⟨ξ, hξ⟩ := ConstPoint.exists_gtPt_through globalFns_holds (pull_grp hE) hE.w_gen hE.xe.toAddMonoidHom hE.c_pr
    (T := T₀) (T' := Tw) i hi (Φ T₀ (x₀ * y₀))
  have hξ' : Thru hE.w hE.xe i (Φ T₀ (x₀ * y₀)) ξ := hξ
  have ad := Thru.isAdd (pull_grp hE) globalFns_holds hE.w_gen hi (key x x₀ hx) (key y y₀ hy) hξ' (hΦ.2 T₀ x₀ y₀)
  obtain rfl : ξ = TorusCoord.toGtPt (U.gt e) (x * y) :=
    isAdd_unique ad (TorusCoord.isAdd_pointsEquiv (U.gt e) globalFns_holds x y)
  exact (Category.id_comp _).symm.trans
    (eq_of_thru hΦ hE.xe.surjective ((thru_pull_iff _ (pl _) i _).1 hξ') (h.thru (x * y)))

theorem isGrpPullback_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ :=
  fun _ _ _ _ _ U Y _ _ h => h.isGrpPullback' Y.rep U

end GlobalTheory.FormalModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackThickeningOfCarriesTorusCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGrpPullback_thickening_of_carries_torusCoordinates : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → IsGrpPullback (thickObj R' I e G') Y.H (thick R' I e ≫ spMap ρ) φ := by
  first | exact @GlobalTheory.FormalModel.isGrpPullback_of_carries | exact GlobalTheory.FormalModel.isGrpPullback_of_carries | (intros; apply GlobalTheory.FormalModel.isGrpPullback_of_carries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.TorusCoordPull in
theorem isPullPt_of_carries : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  intro R R' _ _ _ _ ρ D I E hE A' G' _ _ U Y e φ h Z g
  obtain ⟨ξ', hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt e)
    (T := Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)) g rfl
  have hp := Y.rep.1 (Over.mk ((g ≫ φ) ≫ Y.H.hom)) Y.H (Over.homMk (g ≫ φ) rfl) (𝟙 Y.H)
  rw [Category.comp_id] at hp
  set Yξ := Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl) with hYξ
  have hb : ξ'.b.left ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) = 𝟙 Z ≫ Yξ.b.left := by
    rw [hξ.1, Category.assoc, h.1, hp.1, Category.id_comp]
    rfl
  refine ⟨ξ', hξ, hb, fun χ => ?_⟩
  have hψ : ∀ κ : Fin 4, DegPre.gtφT E.toPre _ ξ'.b χ κ ≫ hE.e.hom.left ≫ pullback.fst D.P.A.hom (specOf ρ) =
      𝟙 Z ≫ DegPre.gtφT D _ Yξ.b (hE.xe χ) κ := fun κ => by
    rw [GlobalTheory.TorusCoord.gtφT_eq, GlobalTheory.TorusCoord.gtφT_eq]
    exact Oφ_pull hE Yξ.b ξ'.b (𝟙 Z) hb χ κ
  refine ⟨hψ, maps_of_good ((isGen_iff hE.w).1 hE.w_gen) D.P.isLB E.toPre.P.isLB (ξ'.s χ) (ξ'.isGen χ) _
    (Yξ.isGen _) hψ fun z J J' hJ hJ' => ?_⟩
  have o := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (U.gt e).pG (𝟙 Z) g (by rw [Category.id_comp]; exact hξ.1)).1 χ
  have r1 : val (Yξ.s (hE.xe χ)) (𝟙 Z) z J = val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) (g ≫ φ) z J :=
    (val_corr hJ (hp.2 _) (𝟙 _)).trans ((val_pull hJ _ _ _).trans
      (congrArg (fun r => val ((Y.Φ Y.H (𝟙 Y.H)).s (hE.xe χ)) r z J) (Category.id_comp _)))
  have r3 : val (ξ'.s χ) (𝟙 Z) z J' = val ((U.gt e).t χ) g z J' :=
    (val_corr hJ' (hξ.2 χ) (𝟙 _)).trans ((val_pull hJ' _ _ _).trans
      (congrArg (fun r => val ((U.gt e).t χ) r z J') (Category.id_comp _)))
  refine r1.trans ((h.2 χ Z g z J J' hJ hJ').trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) r3.symm))
  have ok := o k
  rw [Category.id_comp] at ok
  rw [← ok]
  rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointOfThickeningEqTransportStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'} {D : DegPre R} {I : Ideal R'} {E : DegData R' I} (hE : IsPullDeg ρ D E.toPre) {A' : PolAV (Sp (FractionRing R'))} {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I E A' G') (Y : Ext D) {e : ℕ} {φ : (thickObj R' I e G').left ⟶ Y.H.left}, GlobalTheory.FormalModel.Carries hE (U.gt e) (Y.Φ Y.H (𝟙 Y.H)) φ → ∀ (Z : Scheme.{0}) (g : Z ⟶ (thickObj R' I e G').left), ∃ ξ' : GtPt E.toPre (Over.mk (g ≫ (thickObj R' I e G').hom ≫ thick R' I e)), GlobalTheory.TorusCoord.IsPointOf (U.gt e) g ξ' ∧ IsPullPt hE (𝟙 Z) (Y.Φ (Over.mk ((g ≫ φ) ≫ Y.H.hom)) (Over.homMk (g ≫ φ) rfl)) ξ' := by
  first | exact @GlobalTheory.Mum.isPullPt_of_carries | exact GlobalTheory.Mum.isPullPt_of_carries | (intros; apply GlobalTheory.Mum.isPullPt_of_carries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closedFibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∃ (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' ∧ GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' ∧ IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' := by
  intro R _ _ _ hR D C Y W _ _ _ T
  haveI := T.loc
  let κ : ResidueField R →+* ResidueField W := ResidueField.map T.φ
  have hκ : κ.comp (residue R) = (residue W).comp T.φ := RingHom.ext fun r => ResidueField.map_residue T.φ r
  obtain ⟨φ₀, hφ₀⟩ := GlobalTheory.FormalModel.exists_carries T.hD Y.rep (T.U.gt 0)
  have gA := GlobalTheory.T.isGrpPullback_thickening_of_carries_torusCoordinates T.hD T.U.toUnifPre Y hφ₀
  have hle : maximalIdeal W ^ (0 + 1) ≤ RingHom.ker (residue W) := by
    rw [zero_add, pow_one, ker_residue]
  let c : W ⧸ maximalIdeal W ^ (0 + 1) →+* ResidueField W :=
    Ideal.Quotient.lift _ (residue W) fun a ha => (RingHom.mem_ker).1 (hle ha)
  have hc : spMap c ≫ thick W (maximalIdeal W) 0 = spMap (residue W) := by
    rw [show thick W (maximalIdeal W) 0 = spMap (Ideal.Quotient.mk _) from rfl, ← spMap_comp]
    congr 1
  have hc' : spMap c ≫ thick W (maximalIdeal W) 0 ≫ spMap T.φ = spMap κ ≫ spMap (residue R) := by
    rw [← Category.assoc, hc, ← spMap_comp, ← spMap_comp, hκ]
  let P := (Over.pullback (spMap c)).obj (thickObj W (maximalIdeal W) 0 T.G)
  have g1 : IsGrpPullback P T.G (spMap (residue W))
      (pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0)) :=
    ((isGrpPullback_pullback _ (spMap c)).comp (isGrpPullback_pullback T.G (thick W (maximalIdeal W) 0))).congr hc rfl
  obtain ⟨e1, he1, he1'⟩ := grpPullback_iso g1 (isGrpPullback_pullback T.G (spMap (residue W)))
  have g2 : IsGrpPullback P Y.H (spMap κ ≫ spMap (residue R)) (pullback.fst _ _ ≫ φ₀) :=
    ((isGrpPullback_pullback _ (spMap c)).comp gA).congr hc' rfl
  have g3 := (isGrpPullback_pullback ((Over.pullback (spMap (residue R))).obj Y.H) (spMap κ)).comp
    (isGrpPullback_pullback Y.H (spMap (residue R)))
  obtain ⟨e2, he2, he2'⟩ := grpPullback_iso g2 g3
  refine ⟨κ, e1.symm ≪≫ e2, hκ, ?_, ?_⟩
  · haveI := he1; haveI := he2
    show IsMonHom (e1.inv ≫ e2.hom)
    infer_instance
  · intro Z p p' y hp hy
    have i1 : e1.inv.left ≫ pullback.fst _ _ ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) =
        pullback.fst T.G.hom (spMap (residue W)) := by
      rw [← he1', ← Category.assoc, ← Over.comp_left, e1.inv_hom_id, Over.id_left, Category.id_comp]
    let g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left := p ≫ e1.inv.left ≫ pullback.fst _ _
    have hy' : y = g ≫ φ₀ := by
      rw [hy]
      have := he2'
      simp only [Iso.trans_hom, Iso.symm_hom, Over.comp_left, Category.assoc, g]
      rw [this]
    subst hy'
    obtain ⟨ξ', h1, h2⟩ := GlobalTheory.T.torusExtensionPoint_of_thickening_eq_transport T.hD T.U.toUnifPre Y hφ₀ Z g
    refine ⟨g, ξ', ?_, h1, h2⟩
    rw [hp]
    show (p ≫ e1.inv.left ≫ pullback.fst _ _) ≫ pullback.fst T.G.hom (thick W (maximalIdeal W) 0) = _
    rw [Category.assoc, Category.assoc, i1]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibreIsoTorusExtensionBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedFibre_iso_torusExtension_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∃ (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' ∧ GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' ∧ IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' := by
  first | exact @GlobalTheory.Mum.closedFibre_iso | exact GlobalTheory.Mum.closedFibre_iso | (intros; apply GlobalTheory.Mum.closedFibre_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RedVal

theorem commGroup_fourFactor_exponents_cancel_pow {M : Type} [CommGroup M] (a b c d : M) (k : ℕ) :
    a ^ ((k:ℤ)-1) * b ^ (1:ℤ) * c ^ (-1:ℤ) * d ^ (1:ℤ) * (b ^ (-1:ℤ) * c ^ (1:ℤ) * a ^ (1:ℤ) * d ^ (-1:ℤ)) = a ^ k := by
  rw [zpow_sub_one]; simp only [zpow_neg, zpow_one, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {Ix : Type} (s : Finset Ix)
    (a : Ix → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem sval_zero_of_van {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (a : D'.X) (b : D.SecB k (hD.xe a))
    (b' : D'.SecB k a) (hb : PullB hD a b b') (I : Ideal R) (e : ℕ) (hv : VanMod I b e) {Z : Scheme.{0}}
    (r : Z ⟶ D'.P.A.left) (h' : Z ⟶ pullback D.P.A.hom (thick R I e))
    (hh : h' ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (z : Z) {J₁ : (Z ⟶ D'.P.A.left) → D'.P.L.ι} (hJ₁ : Good D'.P.L z J₁) : sval b' r z J₁ = 0 := by
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.P.isLB z
  have E := hb Z r z (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    (fun κ => J₁ (r ≫ D'.famφB a κ)) (fun κ => hJ' _) (fun κ => hJ₁ _)
  have h0 : gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z
      (LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
      (b.f (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) = 0 := by
    rw [← hh]
    by_cases hm : (h' ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈ LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    · exact (gs_pull h' _ z _ hm _).symm.trans ((congrArg (gs h' z _) (hv _)).trans (gs_zero' _ _ _))
    · unfold gs
      exact dif_neg hm
  rw [h0] at E
  exact (Units.mul_right_eq_zero _).1 E.symm

theorem expand_eval {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing W)))} {G : Over (Spec (CommRingCat.of W))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {k : ℕ} (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hX : U.ExpandsAt 0 k σ f) {Z : Scheme.{0}} (g : Z ⟶ (thickObj W I 0 G).left) (z : Z)
    {J₁ : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J₂ : (Z ⟶ G.left) → U.LG.L.ι}
    (hJ₁ : Good D.toPre.P.L z J₁) (hJ₂ : Good U.LG.L z J₂) (x : D.toPre.X)
    (hv : ∀ a, a ≠ x → sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ = 0) :
    (gm g z _ ((U.w 0).s (fun _ => J₁ (g ≫ (U.gt 0).pG.left),
        fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)))).val ^ k *
      sval σ (g ≫ (fstG I 0 G).left) z J₂ =
    sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t x) g z J₁).val := by
  obtain ⟨S, hS0, hS⟩ := hX
  let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
    (fun _ => J₁ (g ≫ (U.gt 0).pG.left), fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB a κ)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ (g ≫ D.toPre.Oφ (U.gt 0).pG a κ)
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ i, (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) i =
        J₁ (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) i) := by
      rintro (_ | (_ | _))
      · rfl
      · simp only [Sum.elim_inl, Sum.elim_inr, jf, Category.assoc]
      · rfl
    intro a b e
    rw [key a, key b, e]
  have E := hS p j₁ jf jt rfl hcoh
  have hA : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG I 0 G).left)).U p :=
    ⟨mem_pull.2 (hJ₁ (g ≫ (U.gt 0).pG.left)), mem_pull.2 (hJ₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))⟩
  have hB : g z ∈ (fstG I 0 G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ :=
    hJ₂.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG I 0 G).left)
  have hC : ∀ a, g z ∈ (U.gt 0).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB a) (jf a) := fun a =>
    hJ₁.mem (D.toPre.famφB a) (g ≫ (U.gt 0).pG.left)
  have hD' : ∀ a, g z ∈ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt 0).pG a) (jt a) := fun a =>
    hJ₁.mem (D.toPre.Oφ (U.gt 0).pG a) g
  have hm : g z ∈ U.expW 0 p j₁ S jf jt := by
    refine ⟨⟨hA, hB⟩, ?_⟩
    exact Finset.inf_induction (p := fun V : (thickObj W I 0 G).left.Opens => g z ∈ V) trivial
      (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) (fun a _ => ⟨hC a, hD' a⟩)
  have E' := congrArg (gs g z (U.expW 0 p j₁ S jf jt)) E
  rw [gs_mul g z _ hm, gs_pow' g z _ hm, gs_unit g z _ hm, gm_res g z _ hm, gs_res g z _ hm, gs_sum' g z _ hm] at E'
  erw [gs_pull g (fstG I 0 G).left z _ hB] at E'
  refine E'.trans ?_
  have hterm : ∀ a : S, gs g z (U.expW 0 p j₁ S jf jt)
      (((thickObj W I 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 p j₁ jf jt a.2)).op).hom
        (((U.gt 0).pG.left.app _).hom ((f a.1).f (jf a.1))) *
        (res (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) (((U.gt 0).t a.1).s (jt a.1))).val) =
      sval (f a.1) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a.1) g z J₁).val := fun a => by
    rw [gs_mul g z _ hm, gs_res g z _ hm, gs_unit g z _ hm]
    erw [gm_res g z (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) hm, gs_pull g (U.gt 0).pG.left z _ (hC a.1)]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_attach S (fun a => sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a) g z J₁).val)]
  refine Finset.sum_eq_single x (fun b _ hb => by rw [hv b hb, zero_mul]) (fun hx => ?_)
  have h0 : sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ = 0 :=
    (gs_pull g (U.gt 0).pG.left z _ (hC x) _).symm.trans ((congrArg (gs g z _) (hS0 x hx _)).trans (gs_zero' _ _ _))
  rw [h0, zero_mul]

theorem closedFibre_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ _ D C Y W _ _ _ T Z p' y g ξ' hg hpt hpull k u z J J' hJ hJ'
  subst hg
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.TorusCoord.exists_good' T.D'.toPre.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.TorusCoord.exists_good' T.U.LG.isLB z
  set Fm := T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) with hFm
  set r := g ≫ (T.U.gt 0).pG.left with hr
  set p' := g ≫ (fstG (maximalIdeal W) 0 T.G).left with hp'
  let Gw : (Z ⟶ T.D'.toPre.P.A.left) → (Z.presheaf.stalk z)ˣ := fun f => gw T.hD.w f z (J' (f ≫ Fm)) (J₁ f)
  let W0 := gm g z _ ((T.U.w 0).s (fun _ => J₁ (g ≫ (T.U.gt 0).pG.left), fun _ => J₂ (p' ≫ 𝟙 T.G.left)))
  let uG : Γ(T.G.left, ⊤)ˣ := Units.map
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom).toMonoidHom u
  refine ⟨gm p' z ⊤ uG * gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k * (W0 ^ k)⁻¹ * (Gw r ^ k)⁻¹, ?_⟩
  intro α b τ F σ hτ hL hE
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  obtain ⟨σ', f', hC, hP, hX⟩ := hE

  have hb' : ξ'.b.left = r := hpt.1
  have hq : (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).b.left = y ≫ Y.q.left := by
    have h := (Y.rep.1 (Over.mk (y ≫ Y.H.hom)) Y.H (Over.homMk y rfl) (𝟙 _)).1
    rw [Category.comp_id] at h
    exact h
  have hrF : r ≫ Fm = y ≫ Y.q.left := by
    have h := hpull.1
    rw [hb'] at h
    exact h.trans ((Category.id_comp _).trans hq)
  haveI := T.loc
  have hmm : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal W ^ (0 + 1)).comap T.φ := by
    simp only [zero_add, pow_one]
    intro a ha
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit T.φ a hu)
  let qm : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1) := Ideal.quotientMap _ T.φ hmm
  have hsq : thick W (maximalIdeal W) 0 ≫ specOf T.φ =
      Spec.map (CommRingCat.ofHom qm) ≫ thick R (maximalIdeal R) 0 := by
    simp only [thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hcond : (r ≫ Fm) ≫ D.toPre.P.A.hom = (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫
      Spec.map (CommRingCat.ofHom qm)) ≫ thick R (maximalIdeal R) 0 := by
    have e1 : Fm ≫ D.toPre.P.A.hom = T.D'.toPre.P.A.hom ≫ specOf T.φ := by
      rw [hFm, Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w T.hD.e.hom
    have e2 : r ≫ T.D'.toPre.P.A.hom =
        g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0 := by
      rw [hr, Category.assoc, Over.w (T.U.gt 0).pG]; rfl
    rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc, hsq, Category.assoc,
      Category.assoc]
  let h' := pullback.lift (r ≫ Fm) _ hcond
  have hh : h' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
      r ≫ T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) := pullback.lift_fst _ _ _
  have hvan : ∀ a, a ≠ x → sval (f' a) r z J₁ = 0 := fun a ha =>
    sval_zero_of_van T.hD a (F.f (T.hD.xe a)) (f' a) (hP a) (maximalIdeal R) 0
      (hL.2 _ (fun e => ha (T.hD.xe.injective e))) r h' hh z hJ₁
  have E1 := expand_eval T.U.toUnifPre σ' f' (hX 0) g z hJ₁ hJ₂ x hvan
  have E2 := hC Z p' z J J₂ hJ hJ₂
  have E3 := hτ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl) z J' hJ'
  have E4 := hP x Z r z (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => J₁ (r ≫ T.D'.toPre.famφB x κ))
    (fun κ => hJ' _) (fun κ => hJ₁ _)
  rw [hL.1] at E4
  have E4' : sval b (y ≫ Y.q.left) z J' = (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
      sval (f' x) r z J₁ := by
    have hfam : ∀ κ, (r ≫ Fm) ≫ D.toPre.famφB (T.hD.xe x) κ = (r ≫ T.D'.toPre.famφB x κ) ≫ Fm := fun κ => by
      have e := GlobalTheory.ExpGTrans.famφB_pull T.hD x κ
      rw [← hFm] at e
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
    rw [sval_of b (y ≫ Y.q.left) z J' (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => by
      rw [← hrF, hfam])]
    rw [← hrF]
    exact E4
  have E5 : val ((T.U.gt 0).t x) g z J₁ = val (ξ'.s x) (𝟙 Z) z J₁ := by
    rw [val_corr hJ₁ (hpt.2 x) (𝟙 Z), val_pull hJ₁, Category.id_comp]
  obtain ⟨hψ, hM⟩ := hpull.2 x
  have E6 := ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin.val_maps _ T.hD.w _ DegPre.gtε _ (𝟙 Z) hψ _ _ hM (𝟙 Z) z J₁ J' hJ₁ hJ'
  have hO := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (𝟙 T.D'.toPre.P.A) (𝟙 Z) r (by rw [hb']; simp)).1 x
  have Gprod : (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ) *
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) = Gw r ^ k := by
    simp only [hO, Fin.prod_univ_four]
    simp only [DegPre.famφB, DegPre.Oφ, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Over.id_left, Category.comp_id]
    exact commGroup_fourFactor_exponents_cancel_pow _ _ _ _ k
  have E3' : sval τ y z J' = sval b (y ≫ Y.q.left) z J' *
      (val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J').val := E3
  have E6' : val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J' =
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) * val ((T.U.gt 0).t x) g z J₁ := by
    rw [E5]
    exact (congrArg (fun q => val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) q z J')
      (Category.comp_id (𝟙 Z)).symm).trans E6
  have hu : gs p' z ⊤ (scal T.G.hom u.val) = (gm p' z ⊤ uG).val := gs_unit p' z ⊤ trivial uG
  have hW : ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * W0.val ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
  have hG : ((Gw r ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val *
      ((∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
        (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ).val) = 1 := by
    rw [← Units.val_mul, Gprod, Units.inv_mul]
  rw [E2, hu, E3', E4', E6']
  simp only [Units.val_mul]
  linear_combination (-((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * sval (f' x) r z J₁ * (val ((T.U.gt 0).t x) g z J₁).val)) * hG -
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val * sval σ' p' z J₂) * hW +
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val) * E1

end GlobalTheory.Mum.RedVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTermStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_value_eq_unit_mul_leadingFourierTerm : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  first | exact @GlobalTheory.Mum.RedVal.closedFibre_val | exact GlobalTheory.Mum.RedVal.closedFibre_val | (intros; apply GlobalTheory.Mum.RedVal.closedFibre_val <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.trait_lead_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ (κ : ResidueField R →+* ResidueField W) (e : (Over.pullback (spMap (residue W))).obj T.G ≅ (Over.pullback (spMap κ)).obj ((Over.pullback (spMap (residue R))).obj Y.H)), κ.comp (residue R) = (residue W).comp T.φ ∧ IsMonHom e.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ ((Over.pullback (spMap (residue W))).obj T.G).left) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left), p' = p ≫ pullback.fst T.G.hom (spMap (residue W)) → y = p ≫ e.hom.left ≫ pullback.fst ((Over.pullback (spMap (residue R))).obj Y.H).hom (spMap κ) ≫ pullback.fst Y.H.hom (spMap (residue R)) → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ hB D C Y W _ _ _ T
  obtain ⟨κ, e, h1, h2, h3⟩ := GlobalTheory.T.exists_closedFibre_iso_torusExtension_baseChange R hB D C Y W T
  refine ⟨κ, e, h1, h2, fun Z p p' y hp hy k u z J J' hJ hJ' => ?_⟩
  obtain ⟨g, ξ', hg, hξ, hP⟩ := h3 Z p p' y hp hy
  exact GlobalTheory.T.closedFibre_value_eq_unit_mul_leadingFourierTerm R hB D C Y W T Z p' y g ξ' hg hξ hP k u z J J' hJ hJ'
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermNonzeroClosed
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_term_nonzero_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)) (Y : Ext D.toPre), ∃ (b : D.toPre.SecB 1 0) (τ : SecK D.toPre.P.L Y.q.left 1)
      (y : Y.H.left), IsTermOf Y b τ ∧ Y.H.hom y = closedPoint R ∧ y ∈ nonzeroLocus τ := by
  intro R _ _ _ hB D Y
  haveI : IsNoetherianRing R := hB.1.1
  obtain ⟨-, -, hsurj, -, hterm⟩ := GlobalTheory.T.torusExtension_smooth_affine_surjective_fourierTerms R D.toPre Y
  obtain ⟨th, x, hx, hn⟩ :=
    GlobalTheory.ThetaSectionTest.exists_nonzero_closed GlobalTheory.abelianSchemeLaws_all.1.secBaseChange D.toPre
  obtain ⟨τ, hτ⟩ := hterm 1 0 th
  obtain ⟨y, rfl⟩ := Y.q.left.surjective x
  refine ⟨th, τ, y, hτ, ?_, ?_⟩
  · rw [← hx, ← Scheme.Hom.comp_apply, Over.w]
  · obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' D.toPre.P.isLB y
    have e := hτ Y.H (𝟙 _) y J hJ
    have hu : IsUnit (sval th (𝟙 Y.H ≫ Y.q).left y J) := by
      rw [Category.id_comp]
      exact GlobalTheory.ThetaUnit.isUnit_sval th _ y hn hJ
    have hτu : IsUnit (sval τ (𝟙 Y.H : Y.H ⟶ Y.H).left y J) := by
      rw [e]; exact hu.mul (Units.isUnit _)
    rw [Over.id_left] at hτu
    exact (GlobalTheory.SectionBaseChange.mem_nonzeroLocus τ _).2
      ⟨_, hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left),
        (GlobalTheory.ThetaUnit.isUnit_gs_iff _ y _ (hJ.mem (fun _ : Fin 1 => Y.q.left) (𝟙 Y.H.left)) _).1 hτu⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsPrescribedReductionFiniteExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.SecsAsm

theorem gs_scal_one {R : Type} [CommRing R] {Y Z : Scheme.{0}} (q : Y ⟶ Sp R) (p : Z ⟶ Y) (z : Z) :
    gs p z ⊤ (scal q 1) = 1 := by
  unfold scal
  rw [map_one, map_one, gs_eq p z ⊤ trivial, map_one, map_one]

theorem closed_pt (R : Type) [CommRing R] [IsLocalRing R] :
    spMap (residue R) (closedPoint (ResidueField R)) = closedPoint R :=
  IsLocalRing.comap_closedPoint (residue R)

theorem secs_exists (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (D : DegData R (maximalIdeal R))
    (C : LabCover D) : Nonempty (Secs C.toModif C.G C.P.L.L C.α) := by
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨hsm, -, -, -, -⟩ := GlobalTheory.Mum.ext_smooth_affine_surj_terms R D.toPre Y
  obtain ⟨S, k₁, himm⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  obtain ⟨hth, hth0⟩ := GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D
  choose k₀ hk₀ using hth
  obtain ⟨⟨j₀, hdesc⟩, hdescθ⟩ := GlobalTheory.Mum.exists_secs_of_intFam R hB D C
  have hk : k₁ + ∑ a ∈ S, k₀ a ≤ C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) :=
    (le_max_right _ _).trans (Nat.lt_pow_self C.n_prime.one_lt).le
  obtain ⟨Φ, hΦ⟩ := hdesc (max j₀ (k₁ + ∑ a ∈ S, k₀ a)) (le_max_left _ _)
  obtain ⟨N, α, b, τ, hτ, hατ, hI⟩ := himm _ ((Nat.le_add_right _ _).trans hk)
  have hF : ∀ i, ∃ F : IntFam (maximalIdeal R) D.toPre (C.n ^ (max j₀ (k₁ + ∑ a ∈ S, k₀ a))), F.Lead (α i) (b i) :=
    fun i => hk₀ (α i) _ (((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hατ i).1).trans
      (Nat.le_add_left _ _)).trans hk) (b i)
  choose F hFl using hF
  obtain ⟨bθ, τθ, y₀, hθt, hy₀c, hy₀⟩ := GlobalTheory.Mum.exists_term_nonzero_closed R hB D Y
  obtain ⟨F₁, hF₁⟩ := hth0 1 le_rfl bθ
  obtain ⟨θ, hθ⟩ := hdescθ F₁
  have hsm0 : Smooth ((Over.pullback (spMap (residue R))).obj Y.H).hom :=
    inferInstanceAs (Smooth (pullback.snd Y.H.hom (spMap (residue R))))
  have himm0 : IsImmersion (pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := by
    have : IsClosedImmersion (spMap (residue R)) := IsClosedImmersion.spec_of_surjective _ residue_surjective
    have : IsClosedImmersion (pullback.fst Y.H.hom (spMap (residue R))) := inferInstance
    infer_instance
  refine ⟨{ N := N, k := _, s := fun i => Φ (F i), θ := θ, Y := (Over.pullback (spMap (residue R))).obj Y.H
            smooth := hsm0
            j := pullback.fst Y.H.hom (spMap (residue R)) ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
            j_over := ?_
            imm := himm0
            O := pullback.fst Y.H.hom (spMap (residue R)) ⁻¹ᵁ nonzeroLocus τθ
            O_ne := ?_
            trait := ?_ }⟩
  · rw [Category.assoc, GlobalTheory.ProjSpace.toProj_str, pullback.condition]; rfl
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.H.hom) (g := spMap (residue R)) y₀
      (closedPoint _) (hy₀c.trans (closed_pt R).symm)
    exact ⟨z, show pullback.fst Y.H.hom (spMap (residue R)) z ∈ nonzeroLocus τθ by rw [hz]; exact hy₀⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, T, hio, hfin, hTφ, hTξ⟩ := C.exists_trait W hW φ ξ hφ hloc hξ
  obtain ⟨u, hu⟩ := hΦ W' T
  obtain ⟨uθ, huθ⟩ := hθ W' T
  choose σ hσE hσA using fun i => hu (F i)
  obtain ⟨θ', hθE, hθA⟩ := huθ
  obtain ⟨κ, e, hκ, he, hred⟩ := GlobalTheory.Mum.trait_lead_value R hB D C Y W' T
  have hκ' : κ.comp (residue R) = (residue W').comp (io.comp φ) := by rw [hκ, hTφ]
  refine ⟨W', _, inferInstance, inferInstance, io, T.G, inferInstance, T.β, σ, θ', κ, e, T.cdvr, hio, hfin,
    by rw [← hTξ]; exact T.cart, hκ', he, fun i Z p p' hpp z J hJ => ?_, fun Z p p' hpp z J hJ => ?_, ?_⟩
  · rw [hσA i Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  · rw [hθA Z p p' hpp z J hJ, gs_scal_one, _root_.one_mul]
  intro Ω _ p p' y hp hy
  have hval := hred (Sp Ω) p p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) hp
    (by rw [hy]; simp only [Category.assoc])
  have e1 : spMap (residue W') ≫ spMap (io.comp φ) = spMap κ ≫ spMap (residue R) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hκ']
  have hw := Over.w e.hom
  have hbase : p' ≫ T.G.hom ≫ spMap (io.comp φ) = (y ≫ pullback.fst Y.H.hom (spMap (residue R))) ≫ Y.H.hom := by
    rw [hp]
    simp only [Category.assoc]
    rw [pullback.condition_assoc, e1, pullback.condition]
    rw [hy]
    simp only [Category.assoc]
    erw [pullback.condition_assoc]
    rw [← Category.assoc e.hom.left]
    erw [hw]
    rfl
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨-, hs, hP⟩ := GlobalTheory.Mum.toProj_secPull_of_sval R Ω C.G.left D.toPre.P.A.left T.G.left Y.H.left C.P.L.L D.toPre.P.L
      T.β Y.q.left _ N σ τ Y.H.hom hτ p' (y ≫ pullback.fst Y.H.hom (spMap (residue R))) C.P.L.isLB D.toPre.P.isLB
      (fun z J J' hJ hJ' => by
        obtain ⟨c, hc⟩ := hval _ u z J J' hJ hJ'
        exact ⟨c, fun i => hc (α i) (b i) (τ i) (F i) (σ i) (hατ i).2 (hFl i) (hσE i)⟩)
    rw [hbase]
    exact ⟨hs, hP.trans (by simp only [Category.assoc])⟩
  · choose J hJ using fun χ : Sp Ω ⟶ C.G.left => exists_chart C.P.L.isLB (χ x)
    choose J' hJ' using fun χ : Sp Ω ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ x)
    obtain ⟨c, hc⟩ := hval 1 uθ x J J' hJ hJ'
    have h1 := hc 0 bθ τθ F₁ θ' hθt hF₁ hθE
    have hx' : (y ≫ pullback.fst Y.H.hom (spMap (residue R))) x ∈ nonzeroLocus τθ := hx
    have hu1 := (GlobalTheory.mem_nonzeroLocus_iff_pull τθ _ x (Good.mem hJ' _ _)).1 hx'
    refine (GlobalTheory.mem_nonzeroLocus_iff_pull θ' p' x (Good.mem hJ _ _)).2 ?_
    change IsUnit (sval θ' p' x J)
    rw [h1]
    exact c.isUnit.mul hu1

end GlobalTheory.Mum.SecsAsm

theorem GlobalTheory.Mum.exists_secs_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  intro R _ _ _ hB D C
  obtain ⟨h, -, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D, C,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, ⟨h⟩, GlobalTheory.Mum.SecsAsm.secs_exists R hB D C⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsPrescribedReductionFiniteExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sections_prescribed_reduction_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (C₁ : LabCover D₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ Nonempty (Secs C₁.toModif C₁.G C₁.P.L.L C₁.α) := by
  first | exact @GlobalTheory.Mum.exists_secs_finExt | exact GlobalTheory.Mum.exists_secs_finExt | (intros; apply GlobalTheory.Mum.exists_secs_finExt <;> assumption)
end
