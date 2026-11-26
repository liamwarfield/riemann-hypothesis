module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OLinearIffIsOLinear
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OLinearCompare

open GlobalTheory.TorusCoord

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen :=
  isGen_of_gm _ fun _ _ _ _ _ =>
    (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)))

theorem val₂_axis {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {T : Over S} {z : T.left} {J} (hJ : Good L z J) (x : T ⟶ A) : val₂ u z J x 1 = 1 := by
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (𝟙 A) (1 : A ⟶ A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g (𝟙 A) 1 h).trans ?_))
      rw [MonObj.one_comp, _root_.mul_one, _root_.mul_one]
      simp)
    A.hom η[A].left (Over.w η[A]) (globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    (oneGen_isGen L) (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (𝟙 A) (1 : A ⟶ A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ x.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem val_pull_lift {b b' : D.P.A ⟶ D.P.A}
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A b' b) rosatiε)) (χ : D.X)
    {T Z : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (x : Z ⟶ T) {z : Z.left} {J}
    (hJ : Good D.P.L z J) :
    val (LB.pullGen D.P.L _ _ u (lift (toUnit T ≫ D.c χ) p).left) x.left z J =
      val₂ u z J (toUnit Z ≫ D.c χ) (x ≫ p) := by
  rw [val_pull hJ, ← Over.comp_left, comp_lift, comp_toUnit_assoc]; rfl

end GlobalTheory.OLinearCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordEnd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

def IsCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  F.left ≫ g.pG.left = g.pG.left ≫ a.left ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι),
      Good D.P.L z J →
      val (g.t χ) (r ≫ F.left) z J =
        val (g.t (h' χ)) r z J * val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) r z J

end GlobalTheory.Mum.EndThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem isCoordEnd_thickMap_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  intro R _ _ I D A G _ _ U e a a' h' u F F' hF hF'
  have hq := U.gt_q e
  have hO : GlobalTheory.LevelCompat.thickMapOver I e G ≫ (U.gt (e + 1)).pG = (U.gt e).pG := Over.OverMorphism.ext hq
  have hL : ∀ χ, thickMap R I e G ≫ (lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG).left =
      (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left := by
    intro χ
    have : GlobalTheory.LevelCompat.thickMapOver I e G ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt (e + 1)).pG =
        lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG := by
      simp only [comp_lift, comp_toUnit_assoc, hO]
    exact congrArg (·.left) this
  refine GlobalTheory.TorusCoord.ext_of_val (U.gt (e + 1)) _ _ ?_ ?_
  · calc (thickMap R I e G ≫ F'.left) ≫ (U.gt (e + 1)).pG.left
          = thickMap R I e G ≫ ((U.gt (e + 1)).pG.left ≫ a.left) := by rw [Category.assoc, hF'.1]
      _ = (U.gt e).pG.left ≫ a.left := by rw [← Category.assoc, hq]
      _ = F.left ≫ (U.gt e).pG.left := hF.1.symm
      _ = (F.left ≫ thickMap R I e G) ≫ (U.gt (e + 1)).pG.left := by rw [Category.assoc, hq]
  · intro χ w J hJ
    have e1 := hF'.2 χ _ (thickMap R I e G) w J hJ
    have e2 := hF.2 χ _ (𝟙 _) w J hJ
    rw [Category.id_comp] at e2
    rw [e1, ← val_pull hJ, val_corr hJ (U.gt_t e χ), e2]
    congr 1
    · have e3 := val_pull hJ ((U.gt (e + 1)).t (h' χ)) (thickMap R I e G) (𝟙 _)
      rw [Category.id_comp] at e3
      rw [← e3, val_corr hJ (U.gt_t e _)]
    · rw [val_pull hJ, val_pull hJ, hL, Category.id_comp]

end GlobalTheory.Mum.EndThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTransitionCompatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedGroup_endomorphism_transition_compat : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ) (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (u : LB.Gen (LB.LinComb D.toPre.P.L (rosatiφ D.toPre.P.A a' a) rosatiε)) (F : thickObj R I e G ⟶ thickObj R I e G) (F' : thickObj R I (e + 1) G ⟶ thickObj R I (e + 1) G), IsCoordEnd (U.gt e) a a' h' u F → IsCoordEnd (U.gt (e + 1)) a a' h' u F' → thickMap R I e G ≫ F'.left = F.left ≫ thickMap R I e G := by
  first | exact @GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat | exact GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat | (intros; apply GlobalTheory.Mum.EndThick.isCoordEnd_thickMap_compat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem exists_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X)
    (hc : ∀ χ, D.c (h' χ) = D.c χ ≫ a') (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) :
    ∃ F, IsCoordEnd g a a' h' u F := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcT : ∀ χ, DegPre.cT D T (h' χ) = DegPre.cT D T χ ≫ a' := fun χ => by
    simp only [DegPre.cT, hc, Category.assoc]
  have key : ∀ χ : D.X, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (g.pG ≫ a) χ) DegPre.gtε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val s r z J = val (g.t (h' χ)) r z J *
          val (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left) r z J := by
    intro χ
    obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (g.pG ≫ a) χ) (ε' := DegPre.gtε)
      (by
        intro U _ f
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _
          (c := (f (padd D.P.A g.pG (DegPre.cT D T (h' χ))).left)⁻¹ * f (DegPre.cT D T (h' χ)).left *
            f g.pG.left * (f (DegPre.zeroT D T).left)⁻¹) ?_
          (prod_ros a' a (DegPre.cT D T χ) g.pG f)).trans ?_
        · rw [Fin.prod_univ_four]
          show f _ ^ (-1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (-1 : ℤ) = _
          simp only [zpow_neg, zpow_one]
          rfl
        · rw [Fin.prod_univ_four]
          show _ = f (padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a)).left ^ (-1 : ℤ) * f (DegPre.cT D T χ).left ^ (1 : ℤ) *
            f (g.pG ≫ a).left ^ (1 : ℤ) * f (DegPre.zeroT D T).left ^ (-1 : ℤ)
          have p1 : padd D.P.A g.pG (DegPre.cT D T χ ≫ a') = (DegPre.cT D T χ ≫ a') * g.pG := mul_comm _ _
          have p2 : padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a) = DegPre.cT D T χ * (g.pG ≫ a) := rfl
          rw [hcT χ, p1, p2]
          simp only [zpow_neg, zpow_one]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
      (LB.mulGen D.P.L _ _ _ _ (g.t (h' χ)) (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.t_gen _) (DVR.pullGen_isGen _ _ _ _ hu _))
    exact ⟨s, hs, fun Z r z J hJ => (hv Z r z J hJ).trans (val_mul hJ _ _ _)⟩

  choose s hs hv using key
  have vv : ∀ χ (y : T.left) J, Good D.P.L y J → val (s χ) (𝟙 _) y J =
      val (g.t (h' χ)) (𝟙 _) y J * val₂ u y J (DegPre.cT D T χ) g.pG := fun χ y J hJ => by
    rw [hv χ _ _ y J hJ, val_pull hJ, Category.id_comp]; rfl
  have hm : ∀ χ χ' (y : T.left) J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J *
      cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) =
        val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J := fun χ χ' y J hJ => by
    have e1 : val (g.t (h' χ + h' χ')) (𝟙 _) y J *
        cubV D.cub y J (DegPre.cT D T χ ≫ a') (DegPre.cT D T χ' ≫ a') g.pG =
          val (g.t (h' χ)) (𝟙 _) y J * val (g.t (h' χ')) (𝟙 _) y J := by
      have := GlobalTheory.TorusCoord.val_t_mul g (𝟙 _) (h' χ) (h' χ') y J hJ
      rw [Category.id_comp] at this
      rw [← hcT, ← hcT]
      exact this
    have e2 := (ros_add D.cub GlobalTheory.globalFns_holds D.P.isAb a' a u hu h₀ hJ (DegPre.cT D T χ) (DegPre.cT D T χ')
      g.pG).1
    have hadd : DegPre.cT D T (χ + χ') = DegPre.cT D T χ * DegPre.cT D T χ' := DVR.cPoint_add D T χ χ'
    rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, map_add (f := _), hadd, _root_.mul_assoc, e2, ← _root_.mul_assoc, e1]
    exact mul_mul_mul_comm _ _ _ _
  have hcub : ∀ χ χ' (y : T.left) J, Good D.P.L y J →
      val (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)) (𝟙 _) y J =
        cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) := fun χ χ' y J hJ => by
    exact (val_cub D.cub (𝟙 T) hJ _ _ _).trans (by simp only [Category.id_comp])
  have hmult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)))
      (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' => corr_of_val D.P.isLB fun y J hJ => by
    exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl (hcub χ χ' y J hJ)).trans
      ((hm χ χ' y J hJ).trans (val_mul hJ _ _ _).symm))
  have hzero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L) := corr_of_val D.P.isLB fun y J hJ => by
    have h := hm 0 0 y J hJ
    have c0 : DegPre.cT D T 0 = 1 := cPoint_zero T
    have c1 : cubV D.cub y J (DegPre.cT D T 0) (DegPre.cT D T 0) (g.pG ≫ a) = 1 := by
      rw [c0]
      exact (isCub_cubV D.cub hJ).face 1 _
    rw [c1, add_zero, _root_.mul_one] at h
    exact (mul_eq_left.1 h.symm).trans (val_one _).symm
  let ξ : GtPt D T := ⟨g.pG ≫ a, s, hs, hzero, hmult⟩
  obtain ⟨F, hF⟩ := (GlobalTheory.TorusCoord.toGtPt_bijective g (T := thickObj R I e G)).2 ξ
  have hP := (GlobalTheory.TorusCoord.toGtPt_eq_iff g F ξ).1 hF
  refine ⟨F, hP.1.symm, fun χ Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hP.2 χ) r).symm.trans (hv χ Z r z J hJ))

end GlobalTheory.Mum.EndThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∃ F, IsCoordEnd g a a' h' u F := by
  first | exact @GlobalTheory.Mum.EndThick.exists_isCoordEnd | exact GlobalTheory.Mum.EndThick.exists_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.exists_isCoordEnd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomThickenedGroupEndomorphismTorusCoordinat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomThickenedGroupEndomorphismTorusCoordinat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section

namespace GlobalTheory.Mum.EndThick

theorem commGroup_torusCoordinate_mul_identity {U : Type} [CommGroup U] {vxy wXY ux uy vX vY wx wy c₁ c₂ uxy : U}
    (m₁ : wXY * c₁ = vX * vY) (m₂ : vxy * c₂ = wx * wy) (r : uxy * c₁ = c₂ * (ux * uy))
    (ex : vX = wx * ux) (ey : vY = wy * uy) : vxy * uxy = wXY := by
  rw [eq_mul_inv_of_mul_eq m₁, eq_mul_inv_of_mul_eq m₂, eq_mul_inv_of_mul_eq r, ex, ey]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare in
theorem isMonHom_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → IsMonHom F := by
  intro R _ _ I D e G _ _ g a a' _ _ h' hc u hu h₀ F hF
  obtain ⟨hF₁, hF₂⟩ := hF
  have hG := GlobalTheory.globalFns_holds
  have him : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G),
      im g (x ≫ F) = im g x ≫ a := fun x =>
    Over.OverMorphism.ext ((Category.assoc x.left F.left _).trans
      ((congrArg (x.left ≫ ·) hF₁).trans (Category.assoc _ _ _).symm))
  have hU : ∀ {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : T ⟶ thickObj R I e G) (χ : D.X)
      (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
      val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) x.left z J =
        val₂ u z J (cPt T χ) (im g x) :=
    fun x χ z J hJ => val_pull_lift u χ g.pG ((Over.map (thick R I e)).map x) hJ
  have mul : ∀ (T) (x y : T ⟶ thickObj R I e G), (x * y) ≫ F = (x ≫ F) * (y ≫ F) := by
    intro T x y
    refine Over.OverMorphism.ext (ext_of_val g _ _ ?_ fun χ z J hJ => ?_)
    · have : im g ((x * y) ≫ F) = im g ((x ≫ F) * (y ≫ F)) := by
        rw [him, im_mul, im_mul, him, him, MonObj.mul_comp]
      exact congrArg (·.left) this
    · have e₁ := hF₂ χ _ (x * y).left z J hJ
      have ex := hF₂ χ _ x.left z J hJ
      have ey := hF₂ χ _ y.left z J hJ
      have m₁ := val_t_mul_points g hG χ (x ≫ F) (y ≫ F) z J hJ
      have m₂ := val_t_mul_points g hG (h' χ) x y z J hJ
      have r := (ros_add D.cub hG D.P.isAb a' a u hu h₀ hJ (im g x) (im g y) (cPt T χ)).2
      have c₁ : cubeVal g χ z J (x ≫ F) (y ≫ F) = cubV D.cub z J (cPt T χ) (im g x ≫ a) (im g y ≫ a) := by
        unfold cubeVal
        rw [him, him]
      have c₂ : cubeVal g (h' χ) z J x y = cubV D.cub z J (cPt T χ ≫ a') (im g x) (im g y) := by
        unfold cubeVal
        congr 1
        show toUnit _ ≫ D.c (h' χ) = (toUnit _ ≫ D.c χ) ≫ a'
        rw [hc, Category.assoc]
      rw [c₁] at m₁
      rw [c₂] at m₂
      rw [hU _ χ z J hJ, im_mul] at e₁
      rw [hU _ χ z J hJ] at ex ey
      refine e₁.trans (commGroup_torusCoordinate_mul_identity m₁ m₂ r ex ey)
  refine ⟨?_, ?_⟩
  · have h := mul (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ _ ⟶ thickObj R I e G) ≫ F = 1 := mul_eq_left.1 h.symm
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using h'
  · have h := mul _ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    refine h.trans ?_
    congr 1

end GlobalTheory.Mum.EndThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomThickenedGroupEndomorphismTorusCoordinatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_thickenedGroup_endomorphism_torusCoordinates : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), (∀ χ, D.c (h' χ) = D.c χ ≫ a') → ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → IsMonHom F := by
  first | exact @GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd | exact GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.isMonHom_of_isCoordEnd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharacters
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick

noncomputable section
namespace GlobalTheory.Mum.EndThick

open GlobalTheory.TorusCoord GlobalTheory.OLinearCompare

theorem q_comm_of_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a : D.P.A ⟶ D.P.A) (F : thickObj R I e G ⟶ thickObj R I e G)
    (hF : F.left ≫ g.pG.left = g.pG.left ≫ a.left) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  ext1
  apply pullback.hom_ext
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
    have := hF
    simp only [GtCoord.pG, Over.comp_left, Over.map_map_left, DegPre.prBe, Over.homMk_left] at this
    simpa [Category.assoc] using this
  · simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_snd]
    have h1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) :=
      Over.w g.q
    have h2 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [h1, h2]

theorem torus_of_isCoordEnd : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  intro R _ _ I D e G _ _ g a a' _ _ h' u hu h₀ F hF
  have hb : IsMonHom ((Over.pullback (thick R I e)).map a) := inferInstance
  have hq := q_comm_of_isCoordEnd g a F hF.1
  have hd : (g.i ≫ F) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g.isKernel.w, Category.assoc, IsMonHom.one_hom]
  obtain ⟨t, ht⟩ : ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X,
      t ≫ g.i = g.i ≫ F :=
    ⟨g.isKernel.lift _ _ hd, g.isKernel.lift_fst _ _ hd⟩
  refine ⟨t, fun χ => unit_ext fun y hy => ?_, ht.symm⟩
  obtain ⟨J, hJ⟩ := TLinPf.idx_exists D.P.L D.P.isLB y
  have hJ : Good D.P.L y J := hJ
  have := g.q_hom
  have v₁ := val_torus g χ hJ t 1
  have v₂ := val_torus g (h' χ) hJ (𝟙 _) 1
  rw [_root_.mul_one, val_unit g _ hJ, _root_.mul_one] at v₁ v₂
  rw [ht] at v₁
  rw [Category.id_comp] at v₂
  have e1 : TorusCoord.im g g.i = 1 := (im_congr g (x' := 1) (by
    rw [g.isKernel.w, MonObj.one_comp, Hom.one_def])).trans (im_one g)
  have v₃ : val (LB.pullGen D.P.L _ _ u (lift (toUnit _ ≫ D.c χ) g.pG).left) g.i.left y J = 1 :=
    (val_pull_lift u χ g.pG ((Over.map (thick R I e)).map g.i) hJ).trans
      ((congrArg _ e1).trans (val₂_axis D.P.isAb D.P.isLB a' a u hu h₀ hJ _))
  have v₄ := (hF.2 χ _ g.i.left y J hJ).trans ((congrArg₂ (· * ·) v₂ v₃).trans (_root_.mul_one _))
  refine (gm_res _ y (V := ⊤) (U := t.left ⁻¹ᵁ ⊤) (fun _ _ => trivial) trivial _).trans
    ((gm_pull (𝟙 _) t.left y ⊤ trivial _).trans ?_)
  rw [Category.id_comp]
  rw [Over.comp_left] at v₁
  exact v₁.symm.trans v₄

end GlobalTheory.Mum.EndThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickenedGroupEndomorphismTorusViaCharactersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum.EndThick
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickenedGroup_endomorphism_torus_via_characters : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X), ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε)), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) → ∀ (F : thickObj R I e G ⟶ thickObj R I e G), IsCoordEnd g a a' h' u F → ∃ t : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X ⟶ splitTorus _ D.X, TorusEndOf D.X h' t ∧ g.i ≫ F = t ≫ g.i := by
  first | exact @GlobalTheory.Mum.EndThick.torus_of_isCoordEnd | exact GlobalTheory.Mum.EndThick.torus_of_isCoordEnd | (intros; apply GlobalTheory.Mum.EndThick.torus_of_isCoordEnd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThick
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem q_comm_of_coordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) (h' : D.X →+ D.X)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (F : thickObj R I e G ⟶ thickObj R I e G) (hF : IsCoordEnd g a a' h' u F) :
    F ≫ g.q = g.q ≫ (Over.pullback (thick R I e)).map a := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have h2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.fst D.P.A.hom (thick R I e) =
        pullback.fst D.P.A.hom (thick R I e) ≫ a.left := by
      simp
    rw [h2]
    exact hF.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc]
    have w1 : g.q.left ≫ pullback.snd D.P.A.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w g.q
    have w2 : ((Over.pullback (thick R I e)).map a).left ≫ pullback.snd D.P.A.hom (thick R I e) =
        pullback.snd D.P.A.hom (thick R I e) := Over.w ((Over.pullback (thick R I e)).map a)
    have w3 : F.left ≫ pullback.snd G.hom (thick R I e) = pullback.snd G.hom (thick R I e) := Over.w F
    rw [w2, w1]
    exact w3

theorem formalEnd_exists : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  intro R _ _ _ _ D A G _ _ _ U a a' h h' hE
  obtain ⟨ha, ha', hr, -, hc, -⟩ := hE
  have hr' := GlobalTheory.Mum.RosatiSymmetry.rosatiAdj_symm D.toPre.P.A D.toPre.P.L D.toPre.P.isLB a a' hr
  obtain ⟨u, hu, h₀⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB a' a hr'
  choose F hF using fun e => GlobalTheory.T.exists_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀
  exact ⟨F, fun e => GlobalTheory.T.isMonHom_thickenedGroup_endomorphism_torusCoordinates (U.gt e) a a' h' hc u hu h₀ (F e) (hF e),
    fun e => GlobalTheory.T.thickenedGroup_endomorphism_transition_compat U.toUnifPre e a a' h' u (F e) (F (e + 1)) (hF e) (hF (e + 1)),
    fun e => q_comm_of_coordEnd (U.gt e) a a' h' u (F e) (hF e),
    fun e => GlobalTheory.T.thickenedGroup_endomorphism_torus_via_characters (U.gt e) a a' h' u hu h₀ (F e) (hF e)⟩

end GlobalTheory.Mum.EndThick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjointEndomorphismsActionUniformisedThickStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adjointEndomorphisms_action_uniformisedThickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∃ b, FormalEnd U.toUnifPre a h' b := by
  first | exact @GlobalTheory.Mum.EndThick.formalEnd_exists | exact GlobalTheory.Mum.EndThick.formalEnd_exists | (intros; apply GlobalTheory.Mum.EndThick.formalEnd_exists <;> assumption)
end
