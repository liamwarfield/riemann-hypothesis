module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupGaloisAutomorphismMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianGaloisDescent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisActionOnUniformisedGroupPulledData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMaps
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem val_eq_of_maps_pullAlong {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (F : X ⟶ X) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (W : LB.Iso (LB.LinComb L φ ε) (LB.LinComb (L.pull F) φ ε)) (a t : LB.Gen (LB.LinComb L φ ε))
    (f f' : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k) (hψ' : ∀ k, φ k ≫ F = f' ≫ φ k)
    (h : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f φ ε φ hψ t)) (h' : LB.Gen.Maps W a (GeneratorPullback.pullAlong L F f' φ ε φ hψ' t))
    (z : Y) (J : (Y ⟶ X) → L.ι) (hJ : Good L z J) : val t f z J = val t f' z J := by
  let jj : K → (L.pull F).ι := fun k _ => J (φ k ≫ F)
  let q : K → L.ι := fun k => J (φ k)
  have m₁ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ (φ k ≫ F)
  have m₂ : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart L φ q := Set.mem_iInter.2 fun k => hJ (φ k)
  have m : (𝟙 Y : Y ⟶ Y) z ∈ LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q := ⟨m₁, m₂⟩
  have key : ∀ (f : Y ⟶ Y) (hψ : ∀ k, φ k ≫ F = f ≫ φ k),
      val t f z J = gm (𝟙 Y) z _ (res (inf_le_left : LB.wchart (L.pull F) φ jj ⊓ LB.wchart L φ q ≤ _)
        ((GeneratorPullback.pullAlong L F f φ ε φ hψ t).s jj)) := by
    intro f hψ
    rw [val_of t f z J (fun k => J (φ k ≫ F)) (fun k => by rw [hψ k])]
    exact ((gm_res (𝟙 Y) z _ m _).trans ((gm_res (𝟙 Y) z _ m₁ _).trans
      (gm_pull (𝟙 Y) f z _ (@GeneratorPullback.pullAlong_le _ _ _ _ L _ _ F f φ φ hψ jj z m₁) _))).symm
  rw [key f hψ, key f' hψ']
  exact congrArg (gm (𝟙 Y) z _) ((h (jj, q)).trans (h' (jj, q)).symm)

theorem gtCoord_val_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J :=
  fun g F _ f f' x hψ hψ' h h' z J hJ => val_eq_of_maps_pullAlong F _ Oinvε _ (g.t x) (g.t x) f f' hψ hψ' h h' z J hJ

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateValueEqOfMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinate_value_eq_of_maps : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left) (w : LB.Iso D'.P.L (D'.P.L.pull F)) (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left) (x : D'.X) (hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k) (hψ' : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k), LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)) → LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x) (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ' (g.t x)) → ∀ (z : (thickObj R' I' e G').left) (J : ((thickObj R' I' e G').left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (g.t x) f z J = val (g.t x) f' z J := by
  first | exact @GlobalTheory.Mum.gtCoord_val_eq_of_maps | exact GlobalTheory.Mum.gtCoord_val_eq_of_maps | (intros; apply GlobalTheory.Mum.gtCoord_val_eq_of_maps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem gtCoord_overPoint_ext {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (a a' : Z ⟶ thickObj R I e G)
    (hp : a.left ≫ g.pG.left = a'.left ≫ g.pG.left)
    (hv : ∀ (z : Z.left) (J : (Z.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      ∀ χ : D.X, val (g.t χ) a.left z J = val (g.t χ) a'.left z J) : a = a' := by
  have := g.i_hom
  have := g.q_hom
  have hq : a ≫ g.q = a' ≫ g.q := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)
  have hd : (a' * a⁻¹) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hq, mul_inv_cancel]
    rfl
  let τ := g.isKernel.lift (a' * a⁻¹) (toUnit _) hd
  have hτ : τ ≫ g.i = a' * a⁻¹ := g.isKernel.lift_fst _ _ _
  have h1 : τ = 1 := by
    refine TorusPts.torusPt_ext fun χ => ?_
    refine congrArg Units.val (show pullU τ.left ⊤ (charUnit _ D.X χ) =
      pullU (1 : Z ⟶ splitTorus _ D.X).left ⊤ (charUnit _ D.X χ) from unit_ext fun z _ => ?_)
    choose J hJ using fun ψ : Z.left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
    have k := (TorusCoord.val_torus_point_and_translate R I D e G g Z τ a z J hJ χ).2
    have k' := (TorusCoord.val_torus_point_and_translate R I D e G g Z 1 a z J hJ χ).2
    rw [hτ, inv_mul_cancel_right] at k
    rw [MonObj.one_comp, _root_.one_mul] at k'
    have k2 := mul_right_cancel (k.symm.trans ((hv z J hJ χ).symm.trans k'))
    exact (gm_pull (𝟙 Z.left) τ.left z ⊤ trivial _).trans (k2.trans
      (gm_pull (𝟙 Z.left) (1 : Z ⟶ splitTorus _ D.X).left z ⊤ trivial _).symm)
  rw [h1, MonObj.one_comp] at hτ
  exact (mul_inv_eq_one.1 hτ.symm).symm

theorem gtCoord_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  intro R _ _ I D e G _ _ g Z r r' hb hp hv
  let FinalForm : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    Over.mk (r ≫ (thickObj R I e G).hom)
  exact congrArg (fun φ => φ.left) (gtCoord_overPoint_ext g (Z := FinalForm) (Over.homMk r rfl) (Over.homMk r' hb.symm) hp hv)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedUniformisedGroupPointExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedUniformisedGroup_point_ext : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left), r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom → r ≫ g.pG.left = r' ≫ g.pG.left → (∀ (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → ∀ χ : D.X, val (g.t χ) r z J = val (g.t χ) r' z J) → r = r' := by
  first | exact @GlobalTheory.Mum.gtCoord_point_ext | exact GlobalTheory.Mum.gtCoord_point_ext | (intros; apply GlobalTheory.Mum.gtCoord_point_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem abPart_eq {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg ρ D D') (h h' : IsPullDeg s D' D') (H : PullOver hD h) (H' : PullOver hD h') :
    h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) =
      h'.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) := by
  have hcb := H.2 _ _ rfl rfl
  have hcb' := H'.2 _ _ rfl rfl
  have hov : ∀ k : IsPullDeg s D' D', (k.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s)) ≫ D'.P.A.hom =
      D'.P.A.hom ≫ specOf s := by
    intro k
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w k.e.hom
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  rw [← cancel_mono hD.e.hom.left]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    simp only [Category.assoc] at hcb hcb'
    rw [hcb, hcb']
  · simp only [Category.assoc]
    have w0 : hD.e.hom.left ≫ pullback.snd D.P.A.hom (specOf ρ) = D'.P.A.hom := Over.w hD.e.hom
    rw [w0, ← Category.assoc, hov h, ← Category.assoc, hov h']

theorem iso_eq_of_rig {s : R' →+* R'} {D' : DegPre R'} (F : D'.P.A.left ⟶ D'.P.A.left)
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A)
    (w w' : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig)) : w = w' :=
  iso_unique_of_rig GlobalTheory.globalFns_holds D'.P.A D'.P.isAb D'.P.isLB D'.P.isLB hw hw' hr hr'

theorem level_eq {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ (g.t x))) : f = f' := by
  exact GlobalTheory.T.thickenedUniformisedGroup_point_ext g f f' hb (hp.symm.trans hp') fun z J hJ χ => by
    obtain ⟨hψ, hm⟩ := ht χ
    obtain ⟨hψ', hm'⟩ := ht' χ
    exact GlobalTheory.T.torusCoordinate_value_eq_of_maps g F w f f' χ hψ hψ' hm hm' z J hJ

end GlobalTheory.Mum.GalUniq

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem level_eq_two {s : R' →+* R'} {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F F' : D'.P.A.left ⟶ D'.P.A.left) (hF : F = F')
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A) (he' : eSec D'.P.A ≫ F' = specOf s ≫ eSec D'.P.A)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (w' : LB.Iso D'.P.L (D'.P.L.pull F')) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F' (specOf s) he' D'.P.L D'.rig))
    (xe xe' : D'.X → D'.X) (hxe : xe = id) (hxe' : xe' = id)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F' = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG (xe x) k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t (xe x))))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F' = f' ≫ D'.Oφ g.pG (xe' x) k,
      LB.Gen.Maps (LB.linCombIso w' _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F' f' _ Oinvε _ hψ (g.t (xe' x)))) : f = f' := by
  subst hF hxe hxe'
  obtain rfl := iso_eq_of_rig F he w w' hw hw' hr hr'
  exact level_eq g F w hw f f' hb hp hp' ht ht'

end GlobalTheory.Mum.GalUniq


open GlobalTheory.Mum.GalUniq in
theorem GlobalTheory.Mum.galMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG U' σ a a' ha ha'
  obtain ⟨-, h, bc, rfl, P, PO⟩ := ha
  obtain ⟨-, h', bc', rfl, P', PO'⟩ := ha'
  have hc := abPart_eq hD h h' PO PO'
  have hxe : (⇑h.xe : D'.toPre.X → D'.toPre.X) = id := funext PO.1
  have hxe' : (⇑h'.xe : D'.toPre.X → D'.toPre.X) = id := funext PO'.1
  have hov : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) ≫ G'.hom = G'.hom ≫ specOf (Gal.hom σ) := by
    intro b
    rw [pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w b.hom
  have lev : ∀ n : ℕ, (fstG (maximalIdeal R') n G').left ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      (fstG (maximalIdeal R') n G').left ≫ bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := by
    intro n
    obtain ⟨wL, -, he1, -, hl⟩ := P.lg
    obtain ⟨wL', -, he1', -, hl'⟩ := P'.lg
    obtain ⟨f, hf, hpG, hT, -⟩ := hl n
    obtain ⟨f', hf', hpG', hT', -⟩ := hl' n
    have hb : f ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) =
        f' ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) := by
      have : IsClosedImmersion (thick R' (maximalIdeal R') n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← cancel_mono (thick R' (maximalIdeal R') n), Category.assoc, Category.assoc,
        ← pullback.condition]
      have e1 : f ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf]; simp only [Category.assoc]; rw [hov bc]
      have e2 : f' ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf']; simp only [Category.assoc]; rw [hov bc']
      exact e1.trans e2.symm
    have := level_eq_two (U'.gt n) _ _ hc h.he h'.he h.w h.w_gen h'.w h'.w_gen h.w_rig h'.w_rig _ _ hxe hxe' f f' hb hpG hpG' hT hT'
    rw [← hf, ← hf', this]
  have hI : maximalIdeal R' ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have : IsNoetherianRing R' := hρ.1.1
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have : IsSeparated G'.hom := hG.separated
  have : IsIso (CommRingCat.ofHom (Gal.hom σ)) := σ.1.toCommRingCatIso.isIso_hom
  have : IsIso (specOf (Gal.hom σ)) := inferInstanceAs (IsIso (Spec.map _))
  let Y : Over (Sp R') := Over.mk (G'.hom ≫ inv (specOf (Gal.hom σ)))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (G'.hom ≫ inv (specOf (Gal.hom σ))))
  have hov2 : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      (b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) ≫ Y.hom = G'.hom := by
    intro b
    change _ ≫ G'.hom ≫ inv (specOf (Gal.hom σ)) = _
    simp only [Category.assoc]
    rw [reassoc_of% (hov b), IsIso.hom_inv_id, Category.comp_id]
  have key := (sec_eq_zero_and_hom_eq_of_thickenings R' (maximalIdeal R') hI G').2 Y
    (Over.homMk (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc))
    (Over.homMk (bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc')) lev
  exact congrArg CommaMorphism.left key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  first | exact @GlobalTheory.Mum.galMap_unique | exact GlobalTheory.Mum.galMap_unique | (intros; apply GlobalTheory.Mum.galMap_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGalActRankOne
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section
variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}}

end


open GlobalTheory.TorsionFormCompare in
theorem isPullUnif_refl {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif I D A G)
    (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre) (hid : IsIdPull hD)
    (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G)
    (hbc : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = 𝟙 _) : IsPullUnif (RingHom.id R) hD bc U U := by
  obtain ⟨hx, he, hw⟩ := hid
  have hs := specOf_id R
  have heG : eSec G ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = specOf (RingHom.id R) ≫ eSec G := by
    rw [hbc, hs, Category.comp_id]; exact (Category.id_comp _).symm
  refine (GlobalTheory.isPullUnif_iff_stalks R R I I _ D D hD A A G G bc U U).2
    ⟨isoPullId (Geo.Tor.idIso U.LG.L) hbc, (isGen_iff _).2 (isoPullId_pgen (idIso_isGen U.LG.isLB) hbc), heG,
      isoPullId_maps (idIso_maps U.LG) hbc hs heG, fun e => ⟨𝟙 _, by rw [hbc, Category.id_comp, Category.comp_id],
      ⟨by rw [he, Category.id_comp, Category.comp_id], fun x => ?_⟩, ?_⟩⟩
  · rw [hx x]
    exact ⟨fun κ => by rw [he, Category.id_comp, Category.comp_id],
      pmaps_self_of_tautological he hD.w hw _ _ _ ((U.gt e).t_gen x)⟩
  · intro Z r z jM jM' jL jL' h₁ h₂ h₃ h₄
    have h₁' : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM := by rw [he] at h₁; exact h₁
    have h₃' : (fstG I e G).left (r z) ∈ U.LG.L.U jL := by rw [hbc] at h₃; exact h₃
    rw [Category.comp_id, gw_isoPullId _ hbc _ z jL jL' h₃' h₄, hw Z (r ≫ (U.gt e).pG.left) z jM jM' h₁' h₂]
    have H := (isGen_iff (U.w e)).1 (U.w_gen e) Z r z jM jM' (fun _ => jL) (fun _ => jL') h₁' h₂
      (mem_pull.2 h₃') (mem_pull.2 h₄)
    have hp : r z ∈ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jL') :=
      ⟨mem_pull.2 h₃', mem_pull.2 h₄⟩
    have e₂ : gm r z _ ((U.LG.L.pull (fstG I e G).left).g (fun _ => jL) (fun _ => jL')) =
        gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL') := by
      show gm r z _ (∏ _k : PUnit, (res _ (pullU _ _ (U.LG.L.g jL jL'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact (gm_res r z _ hp _).trans (gm_pull r _ z (U.LG.L.U jL ⊓ U.LG.L.U jL') ⟨h₃', h₄⟩ _)
    rw [H, e₂]
    show _ = _ * gm (r ≫ (fstG I e G).left) z _ (U.LG.L.g jL jL')
    rw [mul_right_comm _ _⁻¹, inv_mul_cancel_right]

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.TorsionFormCompare in
theorem galMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ _ U'
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.psiOnExists R' (maximalIdeal R') hρ.1 D'
  obtain ⟨h, hid⟩ := exists_isIdPull R' D'.toPre W hW hψ
  have gp : IsGrpPullback G' G' (specOf (RingHom.id R')) (𝟙 _) :=
    (@isGrpPullback_of_iso _ _ _ _ _ (Iso.refl G') (inferInstanceAs (IsMonHom (𝟙 G')))).congr (specOf_id R').symm rfl
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf (RingHom.id R')))
  have hP : PullOver hD h := ⟨hid.1, fun b c _ hc => by rw [hc, hid.2.1, Category.id_comp]⟩
  exact ⟨gp, h, bc, hbc, isPullUnif_refl U' h hid bc hbc, hP⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_galoisMap_one : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), GalMap hD U' 1 (𝟙 _) := by
  first | exact @GlobalTheory.Mum.galMap_one | exact GlobalTheory.Mum.galMap_one | (intros; apply GlobalTheory.Mum.galMap_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

theorem galAct_nonempty : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hG U'
  have hex : ∀ σ : Gal ρ, ∃ a, GalMap hD U' σ a := GlobalTheory.T.exists_uniformisedGroup_galoisAutomorphism_map R hR R' ρ hfin D D' hD A' G' hG U'
  choose act hact using hex
  exact ⟨{ act := act
           cart := fun σ => (hact σ).1
           act_one := GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' 1 _ _ (hact 1) (GlobalTheory.T.uniformisedGroup_galoisMap_one R hR R' ρ hfin D D' hD A' G' hG U')
           act_mul := fun σ τ => GlobalTheory.T.uniformisedGroup_galoisMap_unique R hR R' ρ hfin D D' hD A' G' hG U' (σ * τ) _ _ (hact (σ * τ))
             (GlobalTheory.T.uniformisedGroup_galoisMap_mul R hR R' ρ hfin D D' hD A' G' hG U' σ τ _ _ (hact σ) (hact τ))
           unif := fun σ => (hact σ).2 }⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyGaloisActionPulledBackUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_galoisAction_pulledBack_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  first | exact @GlobalTheory.Mum.galAct_nonempty | exact GlobalTheory.Mum.galAct_nonempty | (intros; apply GlobalTheory.Mum.galAct_nonempty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisActionOnUniformisedGroupPulledData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem galAct_exists : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  intro R R' _ _ _ _ _ _ ρ hB hF hG D D' hD A' G' _ _ hS U'
  exact GlobalTheory.T.nonempty_galoisAction_pulledBack_uniformisation R hB R' ρ hF hG D D' hD A' G' hS U'

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisActionOnUniformisedGroupPulledDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisAction_on_uniformisedGroup_pulledData : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), Nonempty (GalAct ρ hD U') := by
  first | exact @GlobalTheory.Mum.galAct_exists | exact GlobalTheory.Mum.galAct_exists | (intros; apply GlobalTheory.Mum.galAct_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisEmbedding
namespace GlobalTheory.GaloisEmbeddingExistence

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R]
    [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R']
    (hinj : Function.Injective (algebraMap R R')) :
    ∃ (L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R))),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
        ∃ (j : R' →ₐ[R] L), Function.Injective j := by
  classical
  set K := FractionRing R
  set Ω := AlgebraicClosure K
  haveI : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
  have hΩ : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hΩ
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let φ : R' →ₐ[R] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφ : Function.Injective φ := by
    have h1 : (RingHom.ker φ).comap (algebraMap R R') = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes] at hx
      exact hΩ (by simpa using hx)
    have h2 : RingHom.ker φ = ⊥ := Ideal.eq_bot_of_comap_eq_bot h1
    exact (RingHom.injective_iff_ker_eq_bot φ).2 h2
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (inferInstance : Module.Finite R R'))
  let M : IntermediateField K Ω := IntermediateField.adjoin K (φ '' (s : Set R'))
  haveI : Finite (φ '' (s : Set R')) := (s.finite_toSet.image φ).to_subtype
  haveI : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let L : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hML : M ≤ L := IntermediateField.le_normalClosure M
  have hmem : ∀ x : R', φ x ∈ L := by
    intro x
    have hx : x ∈ Submodule.span R (s : Set R') := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact hML (IntermediateField.subset_adjoin K _ ⟨x, hx, rfl⟩)
    | zero => simpa using L.zero_mem
    | add x y _ _ hx hy => simpa using L.add_mem hx hy
    | smul r x _ hx =>
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, IsScalarTower.algebraMap_apply R K Ω]
      exact L.mul_mem (L.algebraMap_mem _) hx
  refine ⟨L, inferInstance, inferInstance, ?_⟩
  let j : R' →ₐ[R] L :=
    { toFun := fun x => ⟨φ x, hmem x⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun x y => Subtype.ext (map_mul φ x y)
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun x y => Subtype.ext (map_add φ x y)
      commutes' := fun r => Subtype.ext (φ.commutes r) }
  exact ⟨j, fun x y h => hφ (congrArg Subtype.val h)⟩

end GlobalTheory.GaloisEmbeddingExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GalClosure

theorem exists_galois_embedding (R R' : Type) [CommRing R] [IsDomain R] [CharZero R] [CommRing R'] [IsDomain R']
    [Algebra R R'] [Module.Finite R R'] (hinj : Function.Injective (algebraMap R R')) :
    ∃ L : IntermediateField (FractionRing R) (AlgebraicClosure (FractionRing R)),
      FiniteDimensional (FractionRing R) L ∧ IsGalois (FractionRing R) L ∧
      ∃ j : R' →ₐ[R] L, Function.Injective j := by
  first
  | exact @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding
  | (apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisEmbeddingExistence.exists_galois_embedding ..)

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem isGal_integralClosure_of_tower (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (L : Type) [Field L]
    [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L] [IsGalois (FractionRing R) L] [Algebra R L]
    [IsScalarTower R (FractionRing R) L] :
    IsGal (algebraMap R (integralClosure R L)) := by
  set K := FractionRing R
  set B := integralClosure R L
  haveI : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have hRL : ∀ r : R, algebraMap B L (algebraMap R B r) = algebraMap K L (algebraMap R K r) := fun r => by
    rw [← IsScalarTower.algebraMap_apply R K L]; rfl
  have hfix : ∀ τ : Gal (algebraMap R B), ∀ k : K,
      IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1 (algebraMap K L k) = algebraMap K L k := by
    intro τ k
    have h := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := K)
      (j := (IsFractionRing.ringEquivOfRingEquiv (K := L) (L := L) τ.1).toRingHom.comp (algebraMap K L))
      (k := algebraMap K L) (by
        ext r
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
        rw [← hRL, IsFractionRing.ringEquivOfRingEquiv_algebraMap, τ.2 r])
    exact congrArg (fun f => f k) h
  let toAut : Gal (algebraMap R B) → (L ≃ₐ[K] L) := fun τ => AlgEquiv.ofRingEquiv (hfix τ)
  have htoAut : ∀ τ b, toAut τ (algebraMap B L b) = algebraMap B L (τ.1 b) := fun τ b =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap _ b
  refine ⟨Finite.of_injective toAut fun τ τ' h => Subtype.ext (RingEquiv.ext fun b => ?_), fun x hx => ?_⟩
  · apply IsFractionRing.injective B L
    rw [← htoAut, ← htoAut, h]
  · have hg : ∀ g : L ≃ₐ[K] L, g (x : L) = x := by
      intro g
      let gR : L →ₐ[R] L := (g : L →ₐ[K] L).restrictScalars R
      let gR' : L →ₐ[R] L := (g.symm : L →ₐ[K] L).restrictScalars R
      let τ : B ≃+* B :=
        { toFun := fun b => ⟨g b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR)⟩
          invFun := fun b => ⟨g.symm b, (mem_integralClosure_iff R L).2 ((b.2 : IsIntegral R (b : L)).map gR')⟩
          left_inv := fun b => Subtype.ext (g.symm_apply_apply (b : L))
          right_inv := fun b => Subtype.ext (g.apply_symm_apply (b : L))
          map_mul' := fun a b => Subtype.ext (map_mul g (a : L) b)
          map_add' := fun a b => Subtype.ext (map_add g (a : L) b) }
      have hτ : τ ∈ Gal (algebraMap R B) := fun r => Subtype.ext (by
        show g ((algebraMap R B r : B) : L) = ((algebraMap R B r : B) : L)
        have e : ((algebraMap R B r : B) : L) = algebraMap K L (algebraMap R K r) := hRL r
        rw [e, AlgEquiv.commutes])
      exact congrArg Subtype.val (hx τ hτ)
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 ((IsGalois.mem_bot_iff_fixed (F := K) (x : L)).2 hg)
    have hint : IsIntegral R k := by
      have h1 : IsIntegral R (algebraMap K L k) := hk ▸ (x.2 : IsIntegral R (x : L))
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective).1 h1
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨r, Subtype.ext ?_⟩
    have := hRL r
    rw [hr, hk] at this
    exact this

end GlobalTheory.GalClosure

namespace GlobalTheory.GalClosure

theorem exists_galois_finExt_isLocalHom : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'')
    (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  intro R R' _ _ _ _ _ _ ρ hR hρ
  obtain ⟨⟨hRn, -, hRic, hRc⟩, hR0⟩ := hR
  obtain ⟨-, hinj, hfin⟩ := hρ
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  obtain ⟨L, hLf, hLg, j, hj⟩ := exists_galois_embedding R R' hinj
  set B := integralClosure R L
  obtain ⟨hBfin, hBloc, hBn, hBic, -⟩ := GlobalTheory.integralClosure_finite_local_of_isAdicComplete R hRc L
  have hmem : ∀ x : R', j x ∈ B := fun x => (Algebra.IsIntegral.isIntegral (R := R) x).map j
  let jB : R' →ₐ[R] B := j.codRestrict B hmem
  let σ : R' →+* B := jB.toRingHom
  have hcomp : σ.comp ρ = algebraMap R B := RingHom.ext fun r => jB.commutes r
  have hadm : AdmBase B (maximalIdeal B) :=
    ⟨hBn, inferInstance, hBic, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R B⟩
  have hσinj : Function.Injective σ := fun a b h => hj (congrArg (fun y : B => (y : L)) h)
  have hcfin : (σ.comp ρ).Finite := hcomp ▸ RingHom.finite_algebraMap.2 hBfin
  have hσfin : σ.Finite := RingHom.Finite.of_comp_finite hcfin
  refine ⟨B, inferInstance, inferInstance, hBloc, σ, ⟨hadm, hσinj, hσfin⟩,
    RingHom.IsIntegral.isLocalHom hσfin.to_isIntegral hσinj, ⟨hadm, hσinj.comp hinj, hcfin⟩, ?_⟩
  rw [hcomp]
  exact isGal_integralClosure_of_tower R L

end GlobalTheory.GalClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisClosureLocalDomainExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_closure_local_domain_extension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Base R → FinExt ρ → ∃ (R'' : Type) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsLocalRing R'') (σ : R' →+* R''), FinExt σ ∧ IsLocalHom σ ∧ FinExt (σ.comp ρ) ∧ IsGal (σ.comp ρ) := by
  first | exact @GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | exact GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom | (intros; apply GlobalTheory.GalClosure.exists_galois_finExt_isLocalHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_hasFin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  intro R _ _ _ hR D ⟨R', _, _, _, ρ, D', hρ, ⟨p⟩, hH⟩
  obtain ⟨R'', _, _, _, σ, hσ, hσl, hc, hg⟩ := GlobalTheory.T.exists_galois_closure_local_domain_extension R R' ρ hR hρ
  obtain ⟨D'', ⟨q⟩⟩ := GlobalTheory.T.exists_degenerationData_pullback_injective_localHom R' R'' σ hσ.2.1 hσl D'
  obtain ⟨G'', _, _, A'', hG, ⟨U⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local R' R'' σ hρ.1 hσ.1 hσ.2.1 hσl D' D'' ⟨q⟩ hH
  obtain ⟨r⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q
  obtain ⟨act⟩ := GlobalTheory.T.exists_galoisAction_on_uniformisedGroup_pulledData R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U
  exact GlobalTheory.T.uniformised_semiAbelian_galois_descent R R'' (σ.comp ρ) hR hc hg D D'' r A'' G'' hG U act

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), HasFin D → Has D := by
  first | exact @GlobalTheory.Mum.has_of_hasFin | exact GlobalTheory.Mum.has_of_hasFin | (intros; apply GlobalTheory.Mum.has_of_hasFin <;> assumption)
end
