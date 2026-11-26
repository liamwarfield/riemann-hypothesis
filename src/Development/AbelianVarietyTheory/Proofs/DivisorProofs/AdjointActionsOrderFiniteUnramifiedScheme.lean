module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnramifiedRepresentingPolarizedHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin.DiagPow

theorem eSec_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] :
    eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  unfold eSec
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [comp_lift, comp_lift]
  congr 1
  rw [Hom.one_def, ← Category.assoc, Category.comp_id, toUnit_unique (η[A] ≫ toUnit A) (𝟙 _), Category.id_comp]

theorem diagPow_isLB_rigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
    (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d →
      (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  intro S A _ _ Q hQ d hd
  obtain ⟨hA, hQL, ⟨t₁, ht₁⟩, -, -, hamp⟩ := hQ
  have hM : (Q.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hQL _
  have hD : (diagPow A Q d).IsLB := LB.isLB_linComb hQL _ _
  have hcls : CechPic.cls _ hD = d • CechPic.cls _ hM := by
    refine (CechPic.cls_linComb hQL (K := Fin 1) (fun _ => (lift (𝟙 A) (𝟙 A)).left) (fun _ => (d : ℤ)) hD).trans ?_
    rw [Fintype.sum_unique, CechPic.cls_pull hQL _ hM]
    exact natCast_zsmul _ d
  refine ⟨hD, ?_, GlobalTheory.SiegelOfTheta.relAmple_of_pow hA hM hD hd hcls hamp⟩
  have h₁ : CechPic.cls _ (pull_isLB hQL (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 :=
    (CechPic.cls_eq_zero_iff _).2 ⟨t₁, ht₁⟩
  refine (CechPic.cls_eq_zero_iff (pull_isLB hD (eSec A))).1 ?_
  rw [CechPic.cls_pull hD, hcls, map_nsmul, CechPic.cls_pull hQL, ← CechPic.pull_comp, eSec_diag,
    CechPic.pull_comp, ← CechPic.cls_pull hQL _ (pull_isLB hQL _), h₁, map_zero, nsmul_zero]

end GlobalTheory.ActFin.DiagPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalPullbackPowerIsRigidifiedRelAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalPullbackPower_isRigidified_relAmple : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d → (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) := by
  first | (exact @GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (exact GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple) | (intros; apply GlobalTheory.ActFin.DiagPow.diagPow_isLB_rigidified_relAmple  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpBC

theorem exists_baseChange_hom : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  intro S S' f G A _ _ G' A' _ _ φG φA p hG hA hp
  have w : (φG ≫ p.left) ≫ A.hom = G'.hom ≫ f := by
    rw [Category.assoc, Over.w p, hG.1.w]
  have hq1 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ φA = φG ≫ p.left := hA.1.lift_fst _ _ _
  have hq2 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ A'.hom = G'.hom := hA.1.lift_snd _ _ _
  let p' : G' ⟶ A' := Over.homMk (hA.1.lift (φG ≫ p.left) G'.hom w) hq2
  have hp' : p'.left ≫ φA = φG ≫ p.left := hq1
  have isMonHom_of_mul_comp (e : G' ⟶ A')
      (mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
      IsMonHom e := by
    have hone : (1 : 𝟙_ (Over S') ⟶ G') ≫ e = 1 := by
      have h1 := mul (𝟙_ (Over S')) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := mul (G' ⊗ G') (fst G' G') (snd G' G')
      simpa [Hom.mul_def] using h2
  refine ⟨p', isMonHom_of_mul_comp p' fun T x y => ?_, hp'⟩
  apply Over.OverMorphism.ext
  apply hA.1.hom_ext
  · have e1 := hG.2 T x y (pushPt hG.1.w x) (pushPt hG.1.w y) rfl rfl
    have e2 := hA.2 T (x ≫ p') (y ≫ p') (pushPt hG.1.w x ≫ p) (pushPt hG.1.w y ≫ p)
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
    have e3 : (pushPt hG.1.w x ≫ p * pushPt hG.1.w y ≫ p).left = (x * y).left ≫ φG ≫ p.left := by
      rw [← MonObj.mul_comp, Over.comp_left, e1, Category.assoc]
    rw [← e2, e3, Over.comp_left, Category.assoc, hp']
  · rw [Over.w, Over.w]

end GlobalTheory.GrpBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupSchemeBaseChangeHomOfGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupScheme_baseChange_hom_of_grpPullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  first | (exact @GlobalTheory.GrpBC.exists_baseChange_hom) | (exact GlobalTheory.GrpBC.exists_baseChange_hom) | (intros; apply GlobalTheory.GrpBC.exists_baseChange_hom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackPowObjProjections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackPowObjProjections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin

theorem exists_powPr_of_isGrpPullback : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  intro S T t A _ A' _ φ' B' _ r φB hA hB
  have wu : ∀ u : Fin r, (φB ≫ (Out.powPr A u).left) ≫ A.hom = B'.hom ≫ t := fun u => by
    rw [Category.assoc, Over.w (Out.powPr A u)]; exact hB.1.w
  let pr' : Fin r → (B' ⟶ A') := fun u => Over.homMk (hA.1.lift _ _ (wu u)) (hA.1.lift_snd _ _ _)
  have hpr : ∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left := fun u => hA.1.lift_fst _ _ _
  have inj : ∀ {X : Over T} (a b : X ⟶ A'), a.left ≫ φ' = b.left ≫ φ' → a = b := fun a b h =>
    Over.OverMorphism.ext (hA.1.hom_ext h ((Over.w a).trans (Over.w b).symm))
  have key : ∀ {X : Over T} (z : X ⟶ B') (u : Fin r),
      pushPt hA.1.w (z ≫ pr' u) = pushPt hB.1.w z ≫ Out.powPr A u := fun z u =>
    Over.OverMorphism.ext (by
      show (z.left ≫ (pr' u).left) ≫ φ' = (z.left ≫ φB) ≫ (Out.powPr A u).left
      rw [Category.assoc, hpr, Category.assoc])
  have isMonHom_of_mul_comp (e : B' ⟶ A')
      (mul : ∀ (X : Over T) (x y : X ⟶ B'), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
      IsMonHom e := by
    have hone : (1 : 𝟙_ (Over T) ⟶ B') ≫ e = 1 := by
      have h1 := mul (𝟙_ (Over T)) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := mul (B' ⊗ B') (fst B' B') (snd B' B')
      simpa [Hom.mul_def] using h2
  refine ⟨pr', fun u => ?_, hpr, fun X y => ?_⟩
  · refine isMonHom_of_mul_comp _ fun X x y => inj _ _ ?_
    have hm : pushPt hB.1.w (x * y) = pushPt hB.1.w x * pushPt hB.1.w y := map_mul (pushHom hB X) x y
    calc ((x * y) ≫ pr' u).left ≫ φ' = (pushPt hA.1.w ((x * y) ≫ pr' u)).left := rfl
      _ = ((pushPt hB.1.w x * pushPt hB.1.w y) ≫ Out.powPr A u).left := by rw [key, hm]
      _ = ((pushPt hB.1.w x ≫ Out.powPr A u) * (pushPt hB.1.w y ≫ Out.powPr A u)).left := by
        rw [MonObj.mul_comp]
      _ = (pushPt hA.1.w (x ≫ pr' u) * pushPt hA.1.w (y ≫ pr' u)).left := by rw [key, key]
      _ = ((x ≫ pr' u) * (y ≫ pr' u)).left ≫ φ' := hA.2 X _ _ _ _ rfl rfl
  · let z : Over.mk (X.hom ≫ t) ⟶ Out.powObj A r :=
      (Out.powIsLimit A r).lift (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u))
    have hz : ∀ u, z ≫ Out.powPr A u = pushPt hA.1.w (y u) := fun u =>
      (Out.powIsLimit A r).fac (Fan.mk (Over.mk (X.hom ≫ t)) fun u => pushPt hA.1.w (y u)) ⟨u⟩
    have hz0 : z.left ≫ (Out.powObj A r).hom = X.hom ≫ t := Over.w z
    let x : X ⟶ B' := Over.homMk (hB.1.lift z.left X.hom hz0) (hB.1.lift_snd _ _ _)
    have comp : ∀ (x₁ : X ⟶ B') (u : Fin r), (x₁ ≫ pr' u).left ≫ φ' = x₁.left ≫ φB ≫ (Out.powPr A u).left :=
      fun x₁ u => by
        show (x₁.left ≫ (pr' u).left) ≫ φ' = _
        rw [Category.assoc, hpr]
    have uniq : ∀ x₁ x₂ : X ⟶ B', (∀ u, x₁ ≫ pr' u = y u) → (∀ u, x₂ ≫ pr' u = y u) → x₁ = x₂ := by
      intro x₁ x₂ h₁ h₂
      refine Over.OverMorphism.ext (hB.1.hom_ext ?_ ((Over.w x₁).trans (Over.w x₂).symm))
      refine powext A r _ _ ?_ fun k => ?_
      · rw [Category.assoc, Category.assoc, hB.1.w, ← Category.assoc, ← Category.assoc, Over.w x₁, Over.w x₂]
      · rw [Category.assoc, Category.assoc, ← comp x₁ k, ← comp x₂ k, h₁, h₂]
    have hx : ∀ u, x ≫ pr' u = y u := fun u => inj _ _ (by
      rw [comp]
      show hB.1.lift z.left X.hom hz0 ≫ φB ≫ (Out.powPr A u).left = (y u).left ≫ φ'
      rw [← Category.assoc, hB.1.lift_fst]
      exact congrArg (fun w => w.left) (hz u))
    exact ⟨x, hx, fun x₁ h₁ => uniq _ _ h₁ hx⟩

end GlobalTheory.ActFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackPowObjProjectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_powObj_projections : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u := by
  first | (exact @GlobalTheory.ActFin.exists_powPr_of_isGrpPullback) | (exact GlobalTheory.ActFin.exists_powPr_of_isGrpPullback) | (intros; apply GlobalTheory.ActFin.exists_powPr_of_isGrpPullback  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_inter_exists : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H),
    IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H),
      IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H),
        (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  intro H Z₁ Z₂ i₁ i₂ h₁ h₂
  refine ⟨pullback i₁ i₂, pullback.snd i₁ i₂ ≫ i₂, inferInstance, ?_⟩
  intro T h
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ pullback.fst i₁ i₂, ?_⟩, ⟨z ≫ pullback.snd i₁ i₂, ?_⟩⟩
    · rw [Category.assoc, pullback.condition]
    · rw [Category.assoc]
  · rintro ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩⟩
    exact ⟨pullback.lift z₁ z₂ (hz₁.trans hz₂.symm), by rw [← Category.assoc, pullback.lift_snd, hz₂]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeIntersectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_intersection : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H), IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h := by
  first | (exact @GlobalTheory.closedSubscheme_inter_exists) | (exact GlobalTheory.closedSubscheme_inter_exists) | (intros; apply GlobalTheory.closedSubscheme_inter_exists  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActFin

theorem prod_zpow_transport : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  intro S S' t A _ _ A' _ _ φ h r g f c hc
  let U : Over.mk (A'.hom ≫ t) ⟶ A := pushPt h.1.w (𝟙 A')
  have hk : ∀ k, pushHom h A' (g k) = preHom U (f k) := fun k => by
    ext
    show (g k).left ≫ φ = (𝟙 A' : A' ⟶ A').left ≫ φ ≫ (f k).left
    rw [hc k, Over.id_left, Category.id_comp]
  have e : pushHom h A' (∏ k, g k ^ c k) = preHom U (∏ k, f k ^ c k) := by
    rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hk k]
  have e' := congrArg (fun z => z.left) e
  change (∏ k, g k ^ c k).left ≫ φ = ((𝟙 A' : A' ⟶ A').left ≫ φ) ≫ (∏ k, f k ^ c k).left at e'
  rwa [Over.id_left, Category.id_comp] at e'

end GlobalTheory.ActFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeEndProductPowers_transport_grpPullback : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  first | (exact @GlobalTheory.ActFin.prod_zpow_transport) | (exact GlobalTheory.ActFin.prod_zpow_transport) | (intros; apply GlobalTheory.ActFin.prod_zpow_transport  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransfer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullIsoCongr

theorem lbIso_pull_congr (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X) (h₁ : Q₁.IsLB) (h₂ : Q₂.IsLB)
    (e : LBIso Q₁ Q₂) (f : LBIso (Q₁.pull m) (Q₁.pull m')) : LBIso (Q₂.pull m) (Q₂.pull m') := by
  have a : LBIso (Q₂.pull m) (Q₁.pull m) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q₂ m m rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q₁ m m rfl) (LBIso.symm e)
  have b : LBIso (Q₁.pull m') (Q₂.pull m') :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q₁ m' m' rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull Q₂ m' m' rfl) e
  exact LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m') (pull_isLB h₂ m')
    (LBIso.trans (pull_isLB h₂ m) (pull_isLB h₁ m) (pull_isLB h₁ m') a f) b

theorem isocongr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  fun X Y Q₁ Q₂ m m' h₁ h₂ e f => lbIso_pull_congr X Y Q₁ Q₂ m m' h₁ h₂ e f

end GlobalTheory.PullIsoCongr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackPairTransferStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_pair_transfer : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') := by
  first | (exact @GlobalTheory.PullIsoCongr.isocongr) | (exact GlobalTheory.PullIsoCongr.isocongr) | (intros; apply GlobalTheory.PullIsoCongr.isocongr  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeFiniteIntersection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeFiniteIntersection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem closedSubscheme_iInter_exists :
    ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  intro H Idx _ Z i hi
  revert Z i hi
  refine Finite.induction_empty_option
    (P := fun (α : Type) => ∀ (Z : α → Scheme.{0}) (i : ∀ k, Z k ⟶ H),
      (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧
        ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h)
    ?_ ?_ ?_ Idx
  · intro α β e ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (e a)) (fun a => i (e a)) (fun a => hi (e a))
    refine ⟨Z₀, i₀, h₀, fun T h => (hp T h).trans ?_⟩
    exact e.forall_congr_right (q := fun k => ∃ z, z ≫ i k = h)
  · intro Z i _
    refine ⟨H, 𝟙 H, inferInstance, fun T h => ⟨fun _ k => k.elim, fun _ => ⟨h, Category.comp_id h⟩⟩⟩
  · intro α _ ih Z i hi
    obtain ⟨Z₀, i₀, h₀, hp⟩ := ih (fun a => Z (some a)) (fun a => i (some a)) (fun a => hi (some a))
    haveI := h₀
    haveI := hi none
    refine ⟨Limits.pullback i₀ (i none), Limits.pullback.fst i₀ (i none) ≫ i₀, inferInstance, ?_⟩
    intro T h
    rw [Option.forall, ← hp T h]
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨z ≫ Limits.pullback.snd _ _, ?_⟩, ⟨z ≫ Limits.pullback.fst _ _, ?_⟩⟩
      · rw [Category.assoc, ← Limits.pullback.condition]
      · rfl
    · rintro ⟨⟨z₂, h₂⟩, ⟨z₁, h₁⟩⟩
      exact ⟨Limits.pullback.lift z₁ z₂ (h₁.trans h₂.symm), by rw [Limits.pullback.lift_fst_assoc, h₁]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeFiniteIntersectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_finite_intersection : ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H), (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h := by
  first | (exact @GlobalTheory.closedSubscheme_iInter_exists) | (exact GlobalTheory.closedSubscheme_iInter_exists) | (intros; apply GlobalTheory.closedSubscheme_iInter_exists  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProduct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.Serre

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  intro T A' B' C _ _ _ r pr' hpr huniv Φ hΦ
  have hcomp : ∀ u, IsMonHom (pr' u) := hpr
  have hΦu : ∀ u, IsMonHom (Φ ≫ pr' u) := hΦ
  refine ⟨?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := huniv (𝟙_ (Over T)) (fun u => η[C] ≫ Φ ≫ pr' u)
    have h1 : η[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (η[B'] : 𝟙_ (Over T) ⟶ B') = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [IsMonHom.one_hom, IsMonHom.one_hom (Φ ≫ pr' u)])
    rw [h1, h2]
  · obtain ⟨x, -, hx⟩ := huniv (C ⊗ C) (fun u => μ[C] ≫ Φ ≫ pr' u)
    have h1 : μ[C] ≫ Φ = x := hx _ (fun u => by simp)
    have h2 : (Φ ⊗ₘ Φ) ≫ μ[B'] = x := hx _ (fun u => by
      haveI := hcomp u; haveI := hΦu u
      rw [Category.assoc, IsMonHom.mul_hom (Φ ≫ pr' u), IsMonHom.mul_hom (pr' u),
        ← Category.assoc, tensorHom_comp_tensorHom])
    rw [h1, h2]

end GlobalTheory.Serre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProductStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_components_into_groupScheme_product : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  first | (exact @GlobalTheory.Serre.isMonHom_of_components) | (exact GlobalTheory.Serre.isMonHom_of_components) | (intros; apply GlobalTheory.Serre.isMonHom_of_components  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.ActSum

theorem act_sum_zsmul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  intro S A _ _ O _ act h r e c
  let f : Multiplicative O →* (A ⟶ A) := MonoidHom.mk' (fun a => act (Multiplicative.toAdd a)) (fun a b => h.2.2.2 _ _)
  have key : ∀ x : O, act x = f (Multiplicative.ofAdd x) := fun x => rfl
  rw [key, ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ofAdd_zsmul, map_zpow]
  rfl

end GlobalTheory.ActSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringActionOnGroupScheme_intCombination_eq_prod_zpow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  first | (exact @GlobalTheory.ActSum.act_sum_zsmul) | (exact GlobalTheory.ActSum.act_sum_zsmul) | (intros; apply GlobalTheory.ActSum.act_sum_zsmul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActRel

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

def prodPow {r : ℕ} (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ) : A ⟶ A := ∏ k, f k ^ c k

theorem prodPow_add {r : ℕ} (f : Fin r → (A ⟶ A)) (c d : Fin r → ℤ) :
    prodPow f (c + d) = prodPow f c * prodPow f d := by
  simp [prodPow, zpow_add, Finset.prod_mul_distrib]

theorem prodPow_zero {r : ℕ} (f : Fin r → (A ⟶ A)) : prodPow f 0 = 1 := by
  simp [prodPow]

theorem prodPow_zsmul {r : ℕ} (f : Fin r → (A ⟶ A)) (n : ℤ) (c : Fin r → ℤ) :
    prodPow f (n • c) = prodPow f c ^ n := by
  simp [prodPow, zpow_mul', Finset.prod_zpow]

theorem prodPow_single {r : ℕ} (f : Fin r → (A ⟶ A)) (k : Fin r) : prodPow f (Pi.single k 1) = f k := by
  unfold prodPow
  rw [Finset.prod_eq_single k]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

def prodPowHom {r : ℕ} (f : Fin r → (A ⟶ A)) : Multiplicative (Fin r → ℤ) →* (A ⟶ A) :=
  MonoidHom.mk' (fun c => prodPow f c.toAdd) (fun c d => prodPow_add f c.toAdd d.toAdd)

theorem prodPow_sum {r : ℕ} (f : Fin r → (A ⟶ A)) {J : Type} (s : Finset J) (g : J → Fin r → ℤ) :
    prodPow f (∑ i ∈ s, g i) = ∏ i ∈ s, prodPow f (g i) := by
  have := map_prod (prodPowHom f) (fun i => Multiplicative.ofAdd (g i)) s
  rw [← ofAdd_sum] at this
  exact this

def precompHom (h : A ⟶ A) : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => h ≫ x) (fun x y => MonObj.comp_mul h x y)

def postcompHom (h : A ⟶ A) [IsMonHom h] : (A ⟶ A) →* (A ⟶ A) :=
  MonoidHom.mk' (fun x => x ≫ h) (fun x y => MonObj.mul_comp x y h)

end GlobalTheory.ActRel

namespace GlobalTheory.ActRel

theorem prodPow_comp {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (f : Fin r → (A ⟶ A))
    (hf : ∀ k, IsMonHom (f k)) (cm : Fin r → Fin r → Fin r → ℤ) (hm : ∀ i j, f i ≫ f j = prodPow f (cm i j))
    (c d : Fin r → ℤ) :
    prodPow f c ≫ prodPow f d = prodPow f (∑ k, ∑ l, (c k * d l) • cm k l) := by
  haveI : IsMonHom (prodPow f d) := isMonHom_prodPow f hf d
  have h1 : prodPow f c ≫ prodPow f d = ∏ k, (f k ≫ prodPow f d) ^ c k := by
    have := map_prod (postcompHom (prodPow f d)) (fun k => f k ^ c k) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun k _ => ?_)
    show (f k ^ c k) ≫ prodPow f d = _
    exact GrpObj.zpow_comp (f k) (c k) (prodPow f d)
  have h2 : ∀ k, f k ≫ prodPow f d = ∏ l, prodPow f (cm k l) ^ d l := by
    intro k
    have := map_prod (precompHom (f k)) (fun l => f l ^ d l) Finset.univ
    refine this.trans (Finset.prod_congr rfl fun l _ => ?_)
    show f k ≫ f l ^ d l = _
    rw [GrpObj.comp_zpow, hm]
  rw [h1, prodPow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h2, prodPow_sum, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [prodPow_zsmul, ← zpow_mul, mul_comm]

theorem ringAct_iff_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O),
    Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ)
      (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A]
      (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔
        ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧
          ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  intro O _ r e he
  let φ : (Fin r → ℤ) →ₗ[ℤ] O :=
    { toFun := fun c => ∑ k, c k • e k
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun n c => by simp [Finset.smul_sum, mul_smul] }
  have hφ : ∀ c, φ c = ∑ k, c k • e k := fun _ => rfl
  have hsurj : ∀ a, ∃ c, φ c = a := fun a => by
    have : a ∈ Submodule.span ℤ (Set.range e) := he ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp this
    exact ⟨c, hc⟩
  obtain ⟨m, N, hN⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (LinearMap.ker φ))
  choose coef hcoef using hsurj
  refine ⟨m, N, coef 1, fun i j => coef (e i * e j), ?_⟩
  intro S A _ _ f hf
  have hker : (∀ j, prodPow f (N j) = 1) → ∀ c ∈ LinearMap.ker φ, prodPow f c = 1 := by
    intro hNj c hc
    rw [← hN] at hc
    induction hc using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hNj j
    | zero => exact prodPow_zero f
    | add x y _ _ hx hy => rw [prodPow_add, hx, hy, _root_.mul_one]
    | smul n x _ hx => rw [prodPow_zsmul, hx, one_zpow]
  have hwd : (∀ j, prodPow f (N j) = 1) → ∀ c d, φ c = φ d → prodPow f c = prodPow f d := by
    intro hNj c d h
    have hcd : c - d ∈ LinearMap.ker φ := by simp [LinearMap.mem_ker, map_sub, h]
    calc prodPow f c = prodPow f (d + (c - d)) := by rw [add_sub_cancel]
      _ = prodPow f d := by rw [prodPow_add, hker hNj _ hcd, _root_.mul_one]
  have hmul : ∀ c d : Fin r → ℤ, φ c * φ d = ∑ k, ∑ l, (c k * d l) • (e k * e l) := by
    intro c d
    rw [hφ, hφ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, mul_smul]
  constructor
  · rintro ⟨act, hact, hek⟩
    have h0 : act 0 = 1 := by
      have := hact.2.2.2 0 0
      rw [add_zero] at this
      exact mul_eq_left.mp this.symm
    let H : Multiplicative O →* (A ⟶ A) :=
      MonoidHom.mk' (fun a => act a.toAdd) (fun a b => hact.2.2.2 a.toAdd b.toAdd)
    have hact' : ∀ c, act (φ c) = prodPow f c := by
      intro c
      have : act (φ c) = H (Multiplicative.ofAdd (∑ k, c k • e k)) := rfl
      rw [this, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [ofAdd_zsmul, map_zpow]
      show act (e k) ^ c k = _
      rw [hek]
    refine ⟨fun j => ?_, ?_, fun i j => ?_⟩
    · show prodPow f (N j) = 1
      have hNj : N j ∈ LinearMap.ker φ := hN ▸ Submodule.subset_span ⟨j, rfl⟩
      rw [← hact', LinearMap.mem_ker.mp hNj, h0]
    · show prodPow f (coef 1) = 𝟙 A
      rw [← hact', hcoef, hact.2.1]
    · show f i ≫ f j = prodPow f (coef (e i * e j))
      rw [← hact', hcoef, hact.2.2.1, hek, hek]
  · rintro ⟨hNj, h1, hm⟩
    refine ⟨fun a => prodPow f (coef a), ⟨fun a => isMonHom_prodPow f hf _, h1, fun a b => ?_, fun a b => ?_⟩,
      fun k => ?_⟩
    · rw [prodPow_comp f hf _ hm]
      apply hwd hNj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcoef, map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, hcoef]
      rw [← hmul, hcoef, hcoef]
    · rw [← prodPow_add]
      apply hwd hNj
      rw [map_add (f := _), hcoef, hcoef, hcoef]
    · show prodPow f (coef (e k)) = f k
      rw [hwd hNj (coef (e k)) (Pi.single k 1) (by rw [hcoef, hφ]; simp [Pi.single_apply]),
        prodPow_single]

end GlobalTheory.ActRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeRingActionIffEndomorphismRelationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupScheme_ringAction_iff_endomorphism_relations : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O), Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ) (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔ ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧ ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) := by
  first | exact @GlobalTheory.ActRel.ringAct_iff_relations | exact GlobalTheory.ActRel.ringAct_iff_relations | (intros; apply GlobalTheory.ActRel.ringAct_iff_relations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.ActFin
open ReciprocityTheory.ChartRestriction.G.Out

theorem qHyp_pull : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left) (Q : LB (A ⊗ A).left), IsGrpPullback A' A f φ → IsSquare φ φ₂ → QHyp A Q → QHyp A' (Q.pull φ₂) :=
  GlobalTheory.T.symmetricBiextensionHyp_pullback_of_groupPullback

theorem formLB_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧ Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧ Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) :=
  GlobalTheory.T.matrixWeightedPairBundle_rigidified_ample

theorem diagPow_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (d : ℕ), 0 < d → (diagPow A Q d).IsLB ∧ Out.Rigidified A (diagPow A Q d) ∧ Out.RelAmple A (diagPow A Q d) :=
  GlobalTheory.T.diagonalPullbackPower_isRigidified_relAmple

theorem closed_inter : ∀ (H : Scheme.{0}) (Idx : Type) [Finite Idx] (Z : Idx → Scheme.{0}) (i : ∀ k, Z k ⟶ H), (∀ k, IsClosedImmersion (i k)) → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ ∀ k, ∃ z, z ≫ i k = h :=
  GlobalTheory.T.exists_closedSubscheme_finite_intersection

theorem closed_inter₂ : ∀ (H Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ H) (i₂ : Z₂ ⟶ H), IsClosedImmersion i₁ → IsClosedImmersion i₂ → ∃ (Z₀ : Scheme.{0}) (i₀ : Z₀ ⟶ H), IsClosedImmersion i₀ ∧ ∀ (T : Scheme.{0}) (h : T ⟶ H), (∃ z, z ≫ i₀ = h) ↔ (∃ z, z ≫ i₁ = h) ∧ ∃ z, z ≫ i₂ = h :=
  GlobalTheory.T.exists_closedSubscheme_intersection

theorem exists_act_iff_rels : ∀ (O : Type) [Ring O] (r : ℕ) (e : Fin r → O), Submodule.span ℤ (Set.range e) = ⊤ → ∃ (m : ℕ) (N : Fin m → Fin r → ℤ) (c1 : Fin r → ℤ) (cm : Fin r → Fin r → Fin r → ℤ), ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (f : Fin r → (A ⟶ A)), (∀ k, IsMonHom (f k)) → ((∃ act : O → (A ⟶ A), IsRAct A act ∧ ∀ k, act (e k) = f k) ↔ ((∀ j, ∏ k, f k ^ N j k = 1) ∧ ∏ k, f k ^ c1 k = 𝟙 A ∧ ∀ i j, f i ≫ f j = ∏ k, f k ^ cm i j k)) :=
  GlobalTheory.T.groupScheme_ringAction_iff_endomorphism_relations

theorem act_sum_smul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k :=
  GlobalTheory.T.ringActionOnGroupScheme_intCombination_eq_prod_zpow

theorem adj_of_span : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ∀ (act : O → (A ⟶ A)), IsRAct A act → (∀ i, LBIso (Q.pull (lift (fst A A ≫ act (e i)) (snd A A)).left) (Q.pull (lift (fst A A) (snd A A ≫ act (bar (e i)))).left)) → Adj A Q bar act :=
  GlobalTheory.T.ringAction_adjoint_of_adjoint_on_spanning_family

theorem lbIso_pull_congr : ∀ (X Y : Scheme.{0}) (Q₁ Q₂ : LB X) (m m' : Y ⟶ X), Q₁.IsLB → Q₂.IsLB → LBIso Q₁ Q₂ → LBIso (Q₁.pull m) (Q₁.pull m') → LBIso (Q₂.pull m) (Q₂.pull m') :=
  GlobalTheory.T.lineBundleIso_pullback_pair_transfer

theorem exists_hom_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left :=
  GlobalTheory.T.exists_groupScheme_baseChange_hom_of_grpPullback

theorem exists_pow_baseChange : ∀ (S T : Scheme.{0}) (t : T ⟶ S) (A : Over S) [GrpObj A] (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left) (B' : Over T) [GrpObj B'] (r : ℕ) (φB : B'.left ⟶ (Out.powObj A r).left), IsGrpPullback A' A t φ' → IsGrpPullback B' (Out.powObj A r) t φB → ∃ pr' : Fin r → (B' ⟶ A'), (∀ u, IsMonHom (pr' u)) ∧ (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) ∧ ∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u :=
  GlobalTheory.T.exists_grpPullback_powObj_projections

theorem isMonHom_of_components : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ :=
  GlobalTheory.T.isMonHom_of_components_into_groupScheme_product

theorem prodPow_transport : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left :=
  GlobalTheory.T.groupSchemeEndProductPowers_transport_grpPullback

theorem homFix_iso_of_act : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (B' : Over T) [GrpObj B'] (φB : B'.left ⟶ (Out.powObj A r).left) (pr' : Fin r → (B' ⟶ A')), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → IsGrpPullback B' (Out.powObj A r) t φB → (∀ u, IsMonHom (pr' u)) → (∀ u, (pr' u).left ≫ φ' = φB ≫ (Out.powPr A u).left) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ (act : O → (A' ⟶ A')), IsRAct A' act → Adj A' (Q.pull φ₂') bar act → ∀ Φ : A' ⟶ B', (∀ u, Φ ≫ pr' u = act (e u)) → LBIso ((diagPow A Q d).pull φ') (((formLB A Q (Out.powPr A (n := r)) W).pull φB).pull Φ.left) :=
  GlobalTheory.T.formBundle_pullback_adjointAction_eq_diagonalPower

end GlobalTheory.ActFin

namespace GlobalTheory.ActFin
open ReciprocityTheory.ChartRestriction.G.Out

theorem exists_actRep_finite : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π := by
  intro S _ A _ _ Q hab hQ hr1 hr2 hsym hamp O _ bar r e W d hbar hspan hW hd hcas
  have hQQ : QHyp A Q := ⟨hab, hQ, hr1, hr2, hsym, hamp⟩
  obtain ⟨hGab, hMLB, hMrig, hMamp⟩ := formLB_props S A Q hQQ r W hW
  obtain ⟨hLLB, hLrig, hLamp⟩ := diagPow_props S A Q hQQ d hd
  obtain ⟨R, hfin, -⟩ := GlobalTheory.T.exists_finite_unramified_representing_polarizedHoms S A (Out.powObj A r) (diagPow A Q d) (formLB A Q (Out.powPr A (n := r)) W)
    hab hGab hLLB hMLB hLrig hMrig hLamp hMamp
  haveI : IsFinite R.π := hfin
  haveI : IsLocallyNoetherian R.H := LocallyOfFiniteType.isLocallyNoetherian R.π
  haveI : IsCommMonObj R.AH := GlobalTheory.isCommMonObj_of_grpPullback _ _ A R.AH R.π R.φA R.pbA
  let φ₂H := sqMap R.π R.φA R.pbA.1.w
  have hsqH : IsSquare R.φA φ₂H := isSquare_sqMap _ _ _
  obtain ⟨habH, hQHLB, hr1H, hr2H, hsymH, hampH⟩ := qHyp_pull S R.H R.π A R.AH R.φA φ₂H Q R.pbA hsqH hQQ
  obtain ⟨prH, hprHhom, hprH, -⟩ := exists_pow_baseChange S R.H R.π A R.AH R.φA R.BH r R.φB R.pbA R.pbB
  let f : Fin r → (R.AH ⟶ R.AH) := fun k => R.Φ ≫ prH k
  have hfhom : ∀ k, IsMonHom (f k) := fun k => by
    haveI := R.hom; haveI := hprHhom k; exact inferInstanceAs (IsMonHom (R.Φ ≫ prH k))
  obtain ⟨m, N, c1, cm, halg⟩ := exists_act_iff_rels O r e hspan
  have hcb : ∀ i, ∃ c : Fin r → ℤ, ∑ k, c k • e k = bar (e i) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hspan ▸ Submodule.mem_top)
  choose cb hcb using hcb
  have hN := fun j => GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme R.H R.AH R.AH (∏ k, f k ^ N j k) 1 habH habH
    (isMonHom_prodPow f hfhom _) GlobalTheory.Serre.isMonHom_one
  choose ZN iN hiN hZN using hN
  obtain ⟨Z1, i1, hi1, hZ1⟩ := GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme R.H R.AH R.AH (∏ k, f k ^ c1 k) (𝟙 _) habH habH
    (isMonHom_prodPow f hfhom _) inferInstance
  have hM := fun ij : Fin r × Fin r => GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme R.H R.AH R.AH (f ij.1 ≫ f ij.2) (∏ k, f k ^ cm ij.1 ij.2 k) habH habH
    (by haveI := hfhom ij.1; haveI := hfhom ij.2; exact inferInstance) (isMonHom_prodPow f hfhom _)
  choose ZM iM hiM hZM using hM
  have hA := fun i : Fin r => GlobalTheory.T.exists_closedSubscheme_pullback_adjoint_endomorphism_pair R.H R.AH (Q.pull φ₂H) habH hQHLB hr1H hr2H hsymH hampH (f i)
    (∏ k, f k ^ cb i k) (hfhom i) (isMonHom_prodPow f hfhom _)
  choose ZA iA hiA hZA using hA
  obtain ⟨ZN0, iN0, hiN0, hZN0⟩ := closed_inter R.H (Fin m) ZN iN hiN
  obtain ⟨ZM0, iM0, hiM0, hZM0⟩ := closed_inter R.H (Fin r × Fin r) ZM iM hiM
  obtain ⟨ZA0, iA0, hiA0, hZA0⟩ := closed_inter R.H (Fin r) ZA iA hiA
  obtain ⟨Y1, j1, hj1, hY1⟩ := closed_inter₂ R.H ZN0 Z1 iN0 i1 hiN0 hi1
  obtain ⟨Y2, j2, hj2, hY2⟩ := closed_inter₂ R.H Y1 ZM0 j1 iM0 hj1 hiM0
  obtain ⟨Z, iZ, hiZ, hZ⟩ := closed_inter₂ R.H Y2 ZA0 j2 iA0 hj2 hiA0
  have key : ∀ (T : Scheme.{0}) (h : T ⟶ R.H) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (ψ : A'.left ⟶ R.AH.left)
      (ψ₂ : (A' ⊗ A').left ⟶ (R.AH ⊗ R.AH).left) (g : Fin r → (A' ⟶ A')), IsGrpPullback A' R.AH h ψ →
      IsSquare ψ ψ₂ → (∀ k, (g k).left ≫ ψ = ψ ≫ (f k).left) →
      ((∃ z : T ⟶ Z, z ≫ iZ = h) ↔ ((∀ j, ∏ k, g k ^ N j k = 1) ∧ ∏ k, g k ^ c1 k = 𝟙 A' ∧
        (∀ i j, g i ≫ g j = ∏ k, g k ^ cm i j k)) ∧
        ∀ i, LBIso (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A' ≫ g i) (snd A' A')).left)
          (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A') (snd A' A' ≫ ∏ k, g k ^ cb i k)).left)) := by
    intro T h A' _ _ ψ ψ₂ g hpb hsq hg
    have canc : ∀ (a b : A' ⟶ A'), a.left ≫ ψ = b.left ≫ ψ → a = b := fun a b hab =>
      Over.OverMorphism.ext (hpb.1.hom_ext hab (by rw [Over.w a, Over.w b]))
    have tr := fun c => prodPow_transport R.H T h R.AH A' ψ hpb r g f c hg
    have t0 : (1 : A' ⟶ A').left ≫ ψ = ψ ≫ (1 : R.AH ⟶ R.AH).left := by
      simpa using tr (fun _ => 0)
    have eN : ∀ j, (∃ z, z ≫ iN j = h) ↔ ∏ k, g k ^ N j k = 1 := fun j => by
      rw [← hZN j T h A' ψ hpb, ← tr, ← t0]
      exact ⟨canc _ _, fun e => by rw [e]⟩
    have e1 : (∃ z, z ≫ i1 = h) ↔ ∏ k, g k ^ c1 k = 𝟙 A' := by
      rw [← hZ1 T h A' ψ hpb, ← tr, Over.id_left, Category.comp_id]
      refine ⟨fun e => canc _ _ (by rw [e, Over.id_left, Category.id_comp]), fun e => by rw [e, Over.id_left, Category.id_comp]⟩
    have eM : ∀ ij : Fin r × Fin r, (∃ z, z ≫ iM ij = h) ↔ g ij.1 ≫ g ij.2 = ∏ k, g k ^ cm ij.1 ij.2 k := fun ij => by
      rw [← hZM ij T h A' ψ hpb, ← tr]
      have : (g ij.1 ≫ g ij.2).left ≫ ψ = ψ ≫ (f ij.1 ≫ f ij.2).left := by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hg, ← Category.assoc, hg, Category.assoc]
      rw [← this]
      exact ⟨canc _ _, fun e => by rw [e]⟩
    have eA : ∀ i, (∃ z, z ≫ iA i = h) ↔ LBIso (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A' ≫ g i) (snd A' A')).left)
          (((Q.pull φ₂H).pull ψ₂).pull (lift (fst A' A') (snd A' A' ≫ ∏ k, g k ^ cb i k)).left) := fun i =>
      (hZA i T h A' ψ ψ₂ (g i) (∏ k, g k ^ cb i k) hpb hsq (hg i) (tr (cb i))).symm
    rw [hZ, hY2, hY1, hZN0, hZM0, hZA0]
    constructor
    · rintro ⟨⟨⟨hN', h1'⟩, hM'⟩, hA'⟩
      exact ⟨⟨fun j => (eN j).1 (hN' j), e1.1 h1', fun i j => (eM (i, j)).1 (hM' (i, j))⟩, fun i => (eA i).1 (hA' i)⟩
    · rintro ⟨⟨hN', h1', hM'⟩, hA'⟩
      exact ⟨⟨⟨fun j => (eN j).2 (hN' j), e1.2 h1'⟩, fun ij => (eM ij).2 (hM' ij.1 ij.2)⟩, fun i => (eA i).2 (hA' i)⟩

  haveI : IsClosedImmersion iZ := hiZ
  let AZ : Over Z := (Over.pullback iZ).obj R.AH
  let ψZ : AZ.left ⟶ R.AH.left := pullback.fst R.AH.hom iZ
  have pbZ : IsGrpPullback AZ R.AH iZ ψZ := isGrpPullback_pullback R.AH iZ
  haveI : IsCommMonObj AZ := GlobalTheory.isCommMonObj_of_grpPullback _ _ R.AH AZ iZ ψZ pbZ
  let ψ₂Z := sqMap iZ ψZ pbZ.1.w
  have hsqZ : IsSquare ψZ ψ₂Z := isSquare_sqMap _ _ _
  have hgZ := fun k => exists_hom_baseChange R.H Z iZ R.AH R.AH AZ AZ ψZ ψZ (f k) pbZ pbZ (hfhom k)
  choose gZ hgZhom hgZ using hgZ
  obtain ⟨hrelZ, hadjZ⟩ := (key Z iZ AZ ψZ ψ₂Z gZ pbZ hsqZ hgZ).1 ⟨𝟙 Z, Category.id_comp _⟩
  obtain ⟨actZ, hactZ, hactZe⟩ := (halg Z AZ gZ hgZhom).2 hrelZ
  have hbZ : ∀ i, ∏ k, gZ k ^ cb i k = actZ (bar (e i)) := fun i => by
    rw [← hcb i, act_sum_smul Z AZ O actZ hactZ r e (cb i)]
    simp only [hactZe]
  have hQZ : QHyp AZ (Q.pull (ψ₂Z ≫ φ₂H)) :=
    qHyp_pull S Z (iZ ≫ R.π) A AZ (ψZ ≫ R.φA) (ψ₂Z ≫ φ₂H) Q (pbZ.comp R.pbA) (isSquare_comp hsqZ hsqH) hQQ
  have isoZ : LBIso ((Q.pull φ₂H).pull ψ₂Z) (Q.pull (ψ₂Z ≫ φ₂H)) :=
    GlobalTheory.ArcDataDescent.lbIso_pull_pull hQ _ _ rfl
  have hadjZ' : Adj AZ (Q.pull (ψ₂Z ≫ φ₂H)) bar actZ := adj_of_span Z AZ _ hQZ O bar r e hbar hspan actZ hactZ fun i => by
    have := lbIso_pull_congr _ _ _ _ _ _ (pull_isLB (pull_isLB hQ _) _) hQZ.2.1 isoZ (hadjZ i)
    rwa [hbZ i, ← hactZe i] at this
  refine ⟨{
      H := Z
      π := iZ ≫ R.π
      AH := AZ
      φ := ψZ ≫ R.φA
      φ₂ := ψ₂Z ≫ φ₂H
      pb := pbZ.comp R.pbA
      sq := isSquare_comp hsqZ hsqH
      act := actZ
      isAct := hactZ
      adj := hadjZ'
      rep := ?_ }, ?_⟩
  · intro T t A' _ φ' φ₂' act' hpb hsq hact hadj
    haveI : IsCommMonObj A' := GlobalTheory.isCommMonObj_of_grpPullback _ _ A A' t φ' hpb
    let B' := (Over.pullback t).obj (Out.powObj A r)
    let φB : B'.left ⟶ (Out.powObj A r).left := pullback.fst _ t
    have hB : IsGrpPullback B' (Out.powObj A r) t φB := isGrpPullback_pullback _ t
    obtain ⟨pr', hpr'hom, hpr', hprod'⟩ := exists_pow_baseChange S T t A A' φ' B' r φB hpb hB
    obtain ⟨Φ', hΦ', -⟩ := hprod' A' (fun u => act' (e u))
    have hΦhom : IsMonHom Φ' := isMonHom_of_components T A' B' A' r pr' hpr'hom hprod' Φ' fun u => by
      rw [hΦ' u]; exact hact.1 _
    have hiso := homFix_iso_of_act S A Q hQQ O bar r e W d hbar hspan hW hd hcas T t A' φ' φ₂' B' φB pr' hpb hsq hB hpr'hom hpr'
      hprod' act' hact hadj Φ' hΦ'
    obtain ⟨h₀, ⟨hh₀, ψA, ψB, hψA, hψB, hψAφ, hψBφ, hΦψ⟩, huniq⟩ := R.rep T t A' B' φ' φB Φ' hpb hB hΦhom hiso
    let g : Fin r → (A' ⟶ A') := fun k => act' (e k)
    have hprc : ∀ k, (pr' k).left ≫ ψA = ψB ≫ (prH k).left := fun k => by
      apply R.pbA.1.hom_ext
      · simp only [Category.assoc, hψAφ, hprH k]
        rw [hpr' k, ← Category.assoc, hψBφ]
      · simp only [Category.assoc, hψA.1.w, Over.w (prH k), hψB.1.w]
        rw [← Category.assoc, Over.w (pr' k)]
    have hg : ∀ k, (g k).left ≫ ψA = ψA ≫ (f k).left := fun k => by
      show (act' (e k)).left ≫ ψA = ψA ≫ (R.Φ ≫ prH k).left
      rw [← hΦ' k, Over.comp_left, Over.comp_left, Category.assoc, hprc k, ← Category.assoc, hΦψ, Category.assoc]
    let ψ₂A := sqMap h₀ ψA hψA.1.w
    have hsqA : IsSquare ψA ψ₂A := isSquare_sqMap _ _ _
    have hrel' := (halg T A' g (fun k => hact.1 _)).1 ⟨act', hact, fun k => rfl⟩
    have e₂ : φ₂' = ψ₂A ≫ φ₂H := by
      have hc : IsSquare φ' (ψ₂A ≫ φ₂H) := hψAφ ▸ isSquare_comp hsqA hsqH
      exact pullback.hom_ext (hsq.1.trans hc.1.symm) (hsq.2.trans hc.2.symm)
    have isoA : LBIso (Q.pull φ₂') ((Q.pull φ₂H).pull ψ₂A) := by
      rw [e₂]; exact LBIso.symm (GlobalTheory.ArcDataDescent.lbIso_pull_pull hQ _ _ rfl)
    have hadj' : ∀ i, LBIso (((Q.pull φ₂H).pull ψ₂A).pull (lift (fst A' A' ≫ g i) (snd A' A')).left)
        (((Q.pull φ₂H).pull ψ₂A).pull (lift (fst A' A') (snd A' A' ≫ ∏ k, g k ^ cb i k)).left) := fun i => by
      have hb : ∏ k, g k ^ cb i k = act' (bar (e i)) := by
        rw [← hcb i, act_sum_smul T A' O act' hact r e (cb i)]
      rw [hb]
      exact lbIso_pull_congr _ _ _ _ _ _ (pull_isLB hQ _) (pull_isLB (pull_isLB hQ _) _) isoA (hadj (e i))
    obtain ⟨z₀, hz₀⟩ := (key T h₀ A' ψA ψ₂A g hψA hsqA hg).2 ⟨hrel', hadj'⟩
    let ψ : A'.left ⟶ AZ.left := pullback.lift ψA (A'.hom ≫ z₀) (by rw [hψA.1.w, Category.assoc, hz₀])
    have hψ1 : ψ ≫ ψZ = ψA := pullback.lift_fst _ _ _
    have hpbψ : IsGrpPullback A' AZ z₀ ψ :=
      IsGrpPullback.cancel pbZ (IsGrpPullback.congr hψA hz₀.symm hψ1.symm) (pullback.lift_snd _ _ _)
    have hgψ : ∀ k, (g k).left ≫ ψ = ψ ≫ (gZ k).left := fun k => by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hψ1, hgZ k, ← Category.assoc, hψ1, hg k]
      · rw [Category.assoc, Category.assoc]
        erw [pullback.lift_snd, Over.w (gZ k), pullback.lift_snd]
        rw [← Category.assoc, Over.w (g k)]
    refine ⟨z₀, ⟨by rw [← Category.assoc, hz₀, hh₀], ψ, hpbψ, by rw [← Category.assoc, hψ1, hψAφ], fun a => ?_⟩, ?_⟩
    · obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hspan ▸ Submodule.mem_top : a ∈ Submodule.span ℤ (Set.range e))
      rw [← hc, act_sum_smul T A' O act' hact r e c, act_sum_smul Z AZ O actZ hactZ r e c]
      simp only [hactZe]
      exact prodPow_transport Z T z₀ AZ A' ψ hpbψ r g gZ c hgψ
    · rintro h ⟨hπ, ψ₁, hpb₁, hφ₁, hact₁⟩
      have hpb₁' := hpb₁.comp pbZ
      let ψB₁ : B'.left ⟶ R.BH.left := R.pbB.1.lift φB (B'.hom ≫ h ≫ iZ) (by
        rw [hB.1.w, ← hπ]; simp only [Category.assoc])
      have hψB₁φ : ψB₁ ≫ R.φB = φB := R.pbB.1.lift_fst _ _ _
      have hB₁ : IsGrpPullback B' R.BH (h ≫ iZ) ψB₁ :=
        IsGrpPullback.cancel R.pbB (IsGrpPullback.congr hB (by rw [Category.assoc, hπ]) hψB₁φ.symm)
          (by rw [R.pbB.1.lift_snd])
      have hcomp : ∀ k, (g k).left ≫ (ψ₁ ≫ ψZ) = (ψ₁ ≫ ψZ) ≫ (f k).left := fun k => by
        rw [← Category.assoc, hact₁ (e k), Category.assoc, hactZe k, hgZ k, Category.assoc]
      have hH : Φ'.left ≫ ψB₁ ≫ R.BH.hom = ψ₁ ≫ ψZ ≫ R.Φ.left ≫ R.BH.hom := by
        have w1 := hpb₁'.1.w
        have w2 := Over.w Φ'
        have w3 := Over.w R.Φ
        have w4 : ψB₁ ≫ R.BH.hom = B'.hom ≫ h ≫ iZ := R.pbB.1.lift_snd _ _ _
        simp only [Category.assoc] at w1 w4 ⊢
        rw [w4, w3, w1, ← Category.assoc, w2]
      have hΦ₁ : Φ'.left ≫ ψB₁ = (ψ₁ ≫ ψZ) ≫ R.Φ.left := by
        apply R.pbB.1.hom_ext
        · apply powext A r
          · have := congrArg (· ≫ R.π) hH
            simp only [Category.assoc] at this ⊢
            rw [R.pbB.1.w]
            simpa only [Category.assoc] using this
          · intro k
            have l1 : Φ'.left ≫ φB ≫ (Out.powPr A k).left = (g k).left ≫ φ' := by
              rw [← hpr' k, ← Category.assoc, ← Over.comp_left, hΦ' k]
            have l2 : R.Φ.left ≫ R.φB ≫ (Out.powPr A k).left = (f k).left ≫ R.φA := by
              rw [← hprH k, ← Category.assoc, ← Over.comp_left]
            have hc := hcomp k
            simp only [Category.assoc] at hc ⊢
            rw [← Category.assoc ψB₁ R.φB, hψB₁φ, l1, l2, ← hφ₁]
            rw [show (g k).left ≫ ψ₁ ≫ ψZ ≫ R.φA = ((g k).left ≫ ψ₁ ≫ ψZ) ≫ R.φA by simp only [Category.assoc], hc]
            simp only [Category.assoc]
        · simpa only [Category.assoc] using hH
      have e₀ : h ≫ iZ = h₀ := huniq (h ≫ iZ) ⟨by rw [Category.assoc, hπ], ψ₁ ≫ ψZ, ψB₁, hpb₁', hB₁,
        by rw [Category.assoc, hφ₁], hψB₁φ, hΦ₁⟩
      exact (cancel_mono iZ).1 (e₀.trans hz₀.symm)
  · show IsFinite (iZ ≫ R.π)
    infer_instance

end GlobalTheory.ActFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSchemeAdjointActionsAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_scheme_adjoint_actions_abelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π := by
  first | (exact @GlobalTheory.ActFin.exists_actRep_finite) | (exact GlobalTheory.ActFin.exists_actRep_finite) | (intros; apply GlobalTheory.ActFin.exists_actRep_finite  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem GlobalTheory.EndLoc.actRep_finite_unramified : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π ∧ FormallyUnramified R.π := by
  intro S _ A _ _ Q hA hQ h1 h2 hs ha O _ bar r e W d hbar hspan hW hd hcas
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_finite_scheme_adjoint_actions_abelian S A Q hA hQ h1 h2 hs ha O bar r e W d hbar hspan hW hd hcas
  exact ⟨R, hR, GlobalTheory.T.formallyUnramified_adjointRingAction_scheme S A Q O bar R hA⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointActions_order_finite_unramified_scheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π ∧ FormallyUnramified R.π := by
  first | (exact @GlobalTheory.EndLoc.actRep_finite_unramified) | (exact GlobalTheory.EndLoc.actRep_finite_unramified) | (intros; apply GlobalTheory.EndLoc.actRep_finite_unramified  <;> assumption)
end
