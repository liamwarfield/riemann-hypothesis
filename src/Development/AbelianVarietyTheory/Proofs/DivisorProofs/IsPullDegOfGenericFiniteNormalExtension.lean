module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleIsoGenericExtendsNormalLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleIsoGenericExtendsNormalLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenBundle

variable {X Y Z : Scheme.{0}}

theorem lbIso_self {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p => L.g p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.symm ((map_mul _ _ _).trans ((congrArg₂ (· * ·)
    (gm_div L L (𝟙 X) y p q hy) (gm_res _ y _ hy _)).trans ?_)))
  have a := gm_cocycle hL (𝟙 X) y hy.1.1 hy.2.1 hy.2.2
  have b := gm_cocycle hL (𝟙 X) y hy.1.1 hy.1.2 hy.2.2
  show gm (𝟙 X) y _ (L.g p.1 q.1) * (gm (𝟙 X) y _ (L.g p.2 q.2))⁻¹ * gm (𝟙 X) y _ (L.g q.1 q.2) =
    gm (𝟙 X) y _ (L.g p.1 p.2)
  rw [mul_right_comm, a, ← b, mul_inv_cancel_right]

theorem lbIso_pull_comp' {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (chartPullSame L (fun _ : PUnit => g ≫ f) (fun _ => f) (fun _ => 1) g fun _ => rfl)
    (chartPullPull _ g) (lbIso_self (pull_isLB hL f))

end GlobalTheory.Mum.GenBundle


open GlobalTheory.Mum.GenBundle in
theorem GlobalTheory.Mum.genBundle_extends : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w := by
  intro R R' _ _ _ _ _ ρ hA _ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ h1 h2
  obtain ⟨hN, -, hI, -⟩ := hA
  haveI := D₃.P.isAb
  haveI : Smooth D₃.P.A.hom := D₃.P.isAb.smooth
  haveI : GeometricallyIntegral D₃.P.A.hom := geometricallyIntegral_of_isAbelianScheme D₃.P.A
  have hL₁ := D₁.P.isLB
  have hL₂ := D₂.P.isLB
  have hL₃ := D₃.P.isLB
  have hLE := E.P.isLB
  have a₁ : LBIso (D₃.P.L.pull κ) (D₁.P.L.pull (GlobalTheory.PsiEvenPull.proj q₁)) :=
    LBIso.chartPull (chartPullPull D₃.P.L κ)
      (chartPullSame D₁.P.L (fun _ : PUnit => GlobalTheory.PsiEvenPull.proj q₁) (fun _ => GlobalTheory.PsiEvenPull.proj p)
        (fun _ => 1) κ fun _ => h1.symm) ⟨p.w, p.w_gen⟩
  have a : LBIso (D₃.P.L.pull κ) E.P.L :=
    LBIso.trans (pull_isLB hL₃ κ) (pull_isLB hL₁ _) hLE a₁ (LBIso.symm ⟨q₁.w, q₁.w_gen⟩)
  have b₀ : LBIso E.P.L (D₂.P.L.pull (κ ≫ Φ)) := h2 ▸ ⟨q₂.w, q₂.w_gen⟩
  have b : LBIso (D₃.P.L.pull κ) ((D₂.P.L.pull Φ).pull κ) :=
    LBIso.trans (pull_isLB hL₃ κ) (pull_isLB hL₂ _) (pull_isLB (pull_isLB hL₂ Φ) κ)
      (LBIso.trans (pull_isLB hL₃ κ) hLE (pull_isLB hL₂ _) a b₀) (lbIso_pull_comp' hL₂ Φ κ)
  have hj : pullback.fst D₃.P.A.hom (jK R') = hκ.1.isoPullback.inv ≫ κ := by
    exact (Iso.inv_hom_id_assoc hκ.1.isoPullback _).symm.trans
      (congrArg (hκ.1.isoPullback.inv ≫ ·) hκ.1.isoPullback_hom_fst)
  have c : LBIso (D₃.P.L.pull (pullback.fst D₃.P.A.hom (jK R')))
      ((D₂.P.L.pull Φ).pull (pullback.fst D₃.P.A.hom (jK R'))) :=
    LBIso.chartPull
      (chartPullSame D₃.P.L (fun _ : PUnit => pullback.fst D₃.P.A.hom (jK R')) (fun _ => κ) (fun _ => 1)
        hκ.1.isoPullback.inv fun _ => hj)
      (chartPullSame (D₂.P.L.pull Φ) (fun _ : PUnit => pullback.fst D₃.P.A.hom (jK R')) (fun _ => κ) (fun _ => 1)
        hκ.1.isoPullback.inv fun _ => hj) b
  obtain ⟨w, hw⟩ := GlobalTheory.Mum.lbIso_of_generic_local R' D₃.P.A (eSec D₃.P.A) (Over.w η[D₃.P.A]) D₃.P.L
    (D₂.P.L.pull Φ) hL₃ (pull_isLB hL₂ Φ) c
  exact ⟨w, (isGen_iff w).1 hw⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationBundleIsoGenericExtendsNormalLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationBundleIso_generic_extends_normalLocal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w := by
  first | exact @GlobalTheory.Mum.genBundle_extends | exact GlobalTheory.Mum.genBundle_extends | (intros; apply GlobalTheory.Mum.genBundle_extends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum.RigScale

private theorem mem_pull_lemma {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : F (f y) ∈ L.U i) : f y ∈ (L.pull F).U (fun _ => i) := by
  simp only [LB.pull, LB.LinComb, LB.wchart]
  simpa using hi

private theorem mem_U_of_mem_pull_U {X X' Y : Scheme.{0}} {L : LB X} {F : X' ⟶ X} (f : Y ⟶ X') (y : Y) (i : L.ι)
    (hi : f y ∈ (L.pull F).U (fun _ => i)) : F (f y) ∈ L.U i := by
  simp only [LB.pull, LB.LinComb, LB.wchart] at hi
  simpa using hi

set_option maxHeartbeats 1000000 in
private theorem pgen_of_isGen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : LB.Gen.IsGen w) : PGen w := by
  intro Y f y j j' k k' h1 h2 h3 h4
  have m1 := mem_pull_lemma f y j h1
  have m2 := mem_pull_lemma f y j' h2
  have hy : f y ∈ ((L.pull F).div L').U (fun _ => j, k) ⊓ ((L.pull F).div L').U (fun _ => j', k') :=
    ⟨⟨m1, h3⟩, ⟨m2, h4⟩⟩
  have e := congrArg (gm f y _) (hw (fun _ => j, k) (fun _ => j', k'))
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy] at e
  unfold gw
  refine e.trans ?_
  congr 1
  refine (map_mul (gm f y _) _ _).trans ?_
  congr 1
  · refine (gm_res f y _ hy _).trans ?_
    simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
    refine (gm_res f y _ (show f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') from ⟨m1, m2⟩) _).trans ?_
    exact gm_pull f F y (L.U j ⊓ L.U j') ⟨h1, h2⟩ _
  · refine (map_inv (gm f y _) _).trans ?_
    congr 1
    exact gm_res f y _ hy _

set_option maxHeartbeats 1000000 in
private theorem isGen_of_pgen {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
    (w : LB.Iso L' (L.pull F)) (hw : PGen w) : LB.Gen.IsGen w := by
  rintro ⟨a, k⟩ ⟨a', k'⟩
  apply unit_ext
  intro x hx
  have m1 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) := hx.1.1
  have m2 : (𝟙 X') x ∈ (L.pull F).U (fun _ => a' PUnit.unit) := hx.2.1
  have n1 := mem_U_of_mem_pull_U (𝟙 X') x (a PUnit.unit) m1
  have n2 := mem_U_of_mem_pull_U (𝟙 X') x (a' PUnit.unit) m2
  have h := hw X' (𝟙 X') x (a PUnit.unit) (a' PUnit.unit) k k' n1 n2 hx.1.2 hx.2.2
  unfold gw at h
  rw [map_mul, gm_res, gm_res]
  · refine h.trans ?_
    symm
    congr 1
    refine (map_mul (gm (𝟙 X') x _) _ _).trans ?_
    congr 1
    · refine (gm_res (𝟙 X') x _ hx _).trans ?_
      simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
      refine (gm_res (𝟙 X') x _ (show (𝟙 X') x ∈ (L.pull F).U (fun _ => a PUnit.unit) ⊓ (L.pull F).U (fun _ => a' PUnit.unit) from ⟨m1, m2⟩) _).trans ?_
      exact gm_pull (𝟙 X') F x (L.U (a PUnit.unit) ⊓ L.U (a' PUnit.unit)) ⟨n1, n2⟩ _
    · refine (map_inv (gm (𝟙 X') x _) _).trans ?_
      congr 1
      exact gm_res (𝟙 X') x _ hx _
  all_goals first | exact hx | skip

theorem exists_rig_rescale : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  intro R R' _ _ _ _ ρ D₂ D₃ Φ hΦ w₀ hw₀
  have hσ : eSec D₃.P.A ≫ D₃.P.A.hom = 𝟙 _ := Over.w (η[D₃.P.A])
  obtain ⟨w, hw, hm⟩ := GlobalTheory.UnifPreCompare.exists_rigidified (F := Φ) D₂.P.isLB D₃.P.isLB D₃.P.A.hom
    (eSec D₃.P.A) hσ w₀ (isGen_of_pgen w₀ hw₀) D₃.rig D₃.rig_gen D₂.rig D₂.rig_gen (spMap ρ)
    (GlobalTheory.PolBaseChange.eSec_comm hΦ)
  exact ⟨w, pgen_of_isGen w hw, hm⟩

end GlobalTheory.Mum.RigScale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBundleIsoRescaledPreservingRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₂ : DegPre R) (D₃ : DegPre R') (Φ : D₃.P.A.left ⟶ D₂.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → ∀ w₀ : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w₀ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) := by
  first | exact @GlobalTheory.Mum.RigScale.exists_rig_rescale | exact GlobalTheory.Mum.RigScale.exists_rig_rescale | (intros; apply GlobalTheory.Mum.RigScale.exists_rig_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GenEqual

theorem key {X₁ X₂ X₃ XE S₁ S₂ S₃ SE : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {L₃ : LB X₃} {LE : LB XE}
    (hL₁ : L₁.IsLB) (hL₂ : L₂.IsLB) (hL₃ : L₃.IsLB) (hLE : LE.IsLB)
    (Fp : X₃ ⟶ X₁) (Φ : X₃ ⟶ X₂) (κ : XE ⟶ X₃)
    (e₁ : S₁ ⟶ X₁) (e₂ : S₂ ⟶ X₂) (e₃ : S₃ ⟶ X₃) (eE : SE ⟶ XE)
    (t₁ : S₃ ⟶ S₁) (t₂ : S₃ ⟶ S₂) (sE : SE ⟶ S₃) (pE : XE ⟶ SE) (hpE : eE ≫ pE = 𝟙 _)
    (hsurj : Function.Surjective pE.appTop.hom) (hc : eE ≫ κ = sE ≫ e₃)
    (r₁ : LB.Gen (L₁.pull e₁)) (r₂ : LB.Gen (L₂.pull e₂)) (r₃ : LB.Gen (L₃.pull e₃)) (rE : LB.Gen (LE.pull eE))
    (wp : LB.Iso L₃ (L₁.pull Fp)) (w : LB.Iso L₃ (L₂.pull Φ)) (F₁ : XE ⟶ X₁) (F₂ : XE ⟶ X₂) (h₁ : κ ≫ Fp = F₁) (h₂ : κ ≫ Φ = F₂) (u₁ : LB.Iso LE (L₁.pull F₁))
    (u₂ : LB.Iso LE (L₂.pull F₂)) (gp : PGen wp) (gw' : PGen w) (g₁ : PGen u₁) (g₂ : PGen u₂)
    (mp : PMaps wp (K := PUnit) (fun _ => e₃) (fun _ => e₁) (fun _ => 1) r₃ r₁ t₁)
    (mw : PMaps w (K := PUnit) (fun _ => e₃) (fun _ => e₂) (fun _ => 1) r₃ r₂ t₂)
    (m₁ : PMaps u₁ (K := PUnit) (fun _ => eE) (fun _ => e₁) (fun _ => 1) rE r₁ (sE ≫ t₁))
    (m₂ : PMaps u₂ (K := PUnit) (fun _ => eE) (fun _ => e₂) (fun _ => 1) rE r₂ (sE ≫ t₂))
    (Z : Scheme.{0}) (f : Z ⟶ XE) (z : Z) (j : L₂.ι) (i : L₃.ι) (k : LE.ι) (l : L₁.ι)
    (hj : F₂ (f z) ∈ L₂.U j) (hi : κ (f z) ∈ L₃.U i) (hk : f z ∈ LE.U k) (hl : F₁ (f z) ∈ L₁.U l) :
    gw w (f ≫ κ) z j i * (gw wp (f ≫ κ) z l i)⁻¹ = gw u₂ f z j k * (gw u₁ f z l k)⁻¹ := by
  subst h₁ h₂
  obtain ⟨v, Tv⟩ := exists_cancel hL₁ wp u₁ gp g₁ hL₃ hLE
  have gv := Tv.pgen_cancel hL₁ gp g₁
  have rv := Tv.pmaps_cancel hL₁ (fun _ => hc) mp m₁
  obtain ⟨u, Tu⟩ := exists_comp hL₃ w v gw' gv hL₂ hLE
  have gu := Tu.pgen_comp hL₃ gw' gv
  have ru := Tu.pmaps_comp hL₃ (fun _ => hc) mw rv
  have e := GlobalTheory.OverMove.gw_eq_of_pmaps hL₂ hLE pE eE hpE hsurj rfl gu g₂ rfl ru m₂ f z j k
  rw [← e, Tu Z f z j i k hj hi hk, Tv Z f z l i k hl hi hk]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem genequal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ _ hκ hκp hκΦ w hw hr Z f z j i k l hj hi hk hl
  have hs : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ := by
    rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have m₁ := GlobalTheory.FieldPull.pmaps_rig q₁
  have m₂ := GlobalTheory.FieldPull.pmaps_rig q₂
  rw [hs] at m₁ m₂
  exact key D₁.P.isLB D₂.P.isLB D₃.P.isLB E.P.isLB (GlobalTheory.PsiEvenPull.proj p) Φ κ (eSec D₁.P.A) (eSec D₂.P.A)
    (eSec D₃.P.A) (eSec E.P.A) (spMap ρ) (spMap ρ) (spMap (algebraMap R' (FractionRing R'))) E.P.A.hom
    (Over.w η[E.P.A]) (GlobalTheory.globalFns_holds _ E.P.A E.P.isAb).2 (cubeMapOf hκ).e_comm D₁.rig D₂.rig D₃.rig E.rig
    p.w w _ _ hκp hκΦ q₁.w q₂.w ((isGen_iff _).1 p.w_gen) hw ((isGen_iff _).1 q₁.w_gen) ((isGen_iff _).1 q₂.w_gen)
    (GlobalTheory.FieldPull.pmaps_rig p) hr m₁ m₂ Z f z j i k l hj hi hk hl

end GlobalTheory.GenEqual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_identifications_generic_fibre_agree : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  first | exact @GlobalTheory.GenEqual.genequal | exact GlobalTheory.GenEqual.genequal | (intros; apply GlobalTheory.GenEqual.genequal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegOfGenericFiniteNormalExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GenExt

attribute [local instance] ReciprocityTheory.ChartRestriction.G.DVR.isDominant_jK

theorem grp : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E), ∃ (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ ∧ IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ ∧ κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧ κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  haveI : IsNoetherianRing R' := hR.1
  haveI : IsIntegrallyClosed R' := hR.2.2.1
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have g1 := (pull_grp q₁).congr sc rfl
  have g2 := (pull_grp q₂).congr sc rfl

  obtain ⟨κ, k₁, k₂⟩ : ∃ κ : E.P.A.left ⟶ D₃.P.A.left, κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ ∧
      κ ≫ D₃.P.A.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gpp.1.lift _ _ (g1.1.w.trans (Category.assoc _ _ _).symm), gpp.1.lift_fst _ _ _, gpp.1.lift_snd _ _ _⟩
  have gκ : IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ :=
    IsGrpPullback.cancel gpp (g1.congr rfl k₁.symm) k₂

  let G₂ := (Over.pullback (specOf ρ)).obj D₂.P.A
  have gb : IsGrpPullback G₂ D₂.P.A (spMap ρ) (pullback.fst D₂.P.A.hom (specOf ρ)) := isGrpPullback_pullback _ _
  obtain ⟨κ₂, l₁, l₂⟩ : ∃ κ₂ : E.P.A.left ⟶ G₂.left, κ₂ ≫ pullback.fst D₂.P.A.hom (specOf ρ) = GlobalTheory.PsiEvenPull.proj q₂ ∧
      κ₂ ≫ G₂.hom = E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) :=
    ⟨gb.1.lift _ _ (g2.1.w.trans (Category.assoc _ _ _).symm), gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gκ₂ : IsGrpPullback E.P.A G₂ (spMap (algebraMap R' (FractionRing R'))) κ₂ :=
    IsGrpPullback.cancel gb (g2.congr rfl l₁.symm) l₂
  have hj : GlobalTheory.IsGenericPointHom (S := Sp R') (jK R') := .fractionField R' (FractionRing R')
  have s₃ : IsSemiAbelian D₃.P.A := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ D₃.P.isAb
  have s₂ : IsSemiAbelian G₂ :=
    GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ D₂.P.isAb)
  obtain ⟨F, ⟨hF, hκ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) hj s₃ s₂ gκ gκ₂
  refine ⟨F.hom.left ≫ pullback.fst D₂.P.A.hom (specOf ρ), κ, ?_, gκ, k₁, ?_⟩
  · exact ((isGrpPullback_of_iso F).comp gb).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, hκ, l₁]

theorem bundle : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.polarisationBundleIso_generic_extends_normalLocal R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨w, hw, hr⟩ := GlobalTheory.T.exists_bundleIso_rescaled_preserving_rigidification R R' ρ D₂ D₃ Φ gp w₀ hw₀
  exact ⟨w, hw, hr, GlobalTheory.T.rigidified_identifications_generic_fibre_agree R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ w hw hr⟩

theorem cpt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ x : D₃.X, (D₃.c x).left ≫ Φ = spMap ρ ≫ (D₂.c (q₂.xe (q₁.xe.symm (p.xe x)))).left := by
  intro R R' _ _ _ _ ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂ x
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  have sc : spMap ((algebraMap R' (FractionRing R')).comp ρ) = jK R' ≫ spMap ρ :=
    spMap_comp ρ (algebraMap R' (FractionRing R'))
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have hx : (E.c y).left ≫ κ = jK R' ≫ (D₃.c x).left := by
    apply gpp.1.hom_ext
    · show ((E.c y).left ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
      rw [Category.assoc, h₁, cq, Category.assoc, cp, sc, Category.assoc]
    · rw [Category.assoc, gκ.1.w, ← Category.assoc, b1, Category.id_comp, Category.assoc, b3]
      exact (Category.comp_id _).symm
  have c2 : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₂ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₂.c (q₂.xe y)).left := q₂.c_pr y
  have hsep := (GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian D₂.P.A
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme D₂.P.A D₂.P.isAb)).2
  have b2 : (D₂.c (q₂.xe y)).left ≫ D₂.P.A.hom = 𝟙 _ := by simpa using Over.w (D₂.c (q₂.xe y))
  haveI := hsep
  refine ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R')) D₂.P.A.hom ?_ (jK R') ?_
  · rw [Category.assoc, gp.1.w, ← Category.assoc, b3, Category.assoc, b2]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · rw [← Category.assoc, ← hx, Category.assoc, h₂, c2, sc, Category.assoc]

end GlobalTheory.Mum.GenExt

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem isPullDeg_of_generic : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')), IsPullDeg ρ D₁ D₃ → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E → Nonempty (IsPullDeg ρ D₂ D₃) := by
  intro R R' _ _ _ _ _ ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  have hα : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' _
  obtain ⟨Φ, κ, gp, gκ, h₁, h₂⟩ := GenExt.grp R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂
  obtain ⟨w, hw, hr, hT⟩ := GenExt.bundle R R' ρ hR hρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  have hc := GenExt.cpt R R' ρ D₁ D₂ D₃ E p q₁ q₂ Φ κ gp gκ h₁ h₂
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift (show Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) from hα.comp hρ) q₂

  let lf : FractionRing (FractionRing R') →+* FractionRing R' :=
    IsFractionRing.lift (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id
  let r' : (TK R').left ⟶ (TK (FractionRing R')).left := spMap lf
  have hrj : r' ≫ jK (FractionRing R') = 𝟙 _ := by
    show spMap lf ≫ spMap (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = 𝟙 _
    rw [← spMap_comp]
    have : lf.comp (algebraMap (FractionRing R') (FractionRing (FractionRing R'))) = RingHom.id _ :=
      RingHom.ext fun a => IsFractionRing.lift_algebraMap (A := FractionRing R') (K := FractionRing (FractionRing R')) (g := RingHom.id (FractionRing R')) Function.injective_id a
    rw [this]; exact Spec.map_id _
  have hr2 : r' ≫ jK (FractionRing R') ≫ spMap ((algebraMap R' (FractionRing R')).comp ρ) =
      GlobalTheory.ArcPull.genMap hρ ≫ jK R := by
    refine (Category.assoc _ _ _).symm.trans ?_
    rw [hrj, Category.id_comp]
    exact (spMap_comp ρ (algebraMap R' (FractionRing R'))).trans ((Category.id_comp _).symm.trans (GlobalTheory.ArcPull.fracMap_sq hρ))
  refine ⟨(GlobalTheory.DvrDeg.exists_isPullDeg_of_val hρ D₂ D₃ q₂.psiW s hs gp w hw hr
    (p.xe.trans (q₁.xe.symm.trans q₂.xe)) hc (fun x z J J' hJ hJ' => ?_)).choose⟩
  set y := q₁.xe.symm (p.xe x) with hy
  have hy' : q₁.xe y = p.xe x := q₁.xe.apply_symm_apply _
  set e : (TK R').left ⟶ E.P.A.left := r' ≫ E.xK y with he
  have gpp := pull_grp p
  have b1 : (E.c y).left ≫ E.P.A.hom = 𝟙 _ := by simpa using Over.w (E.c y)
  have b3 : (D₃.c x).left ≫ D₃.P.A.hom = 𝟙 _ := by simpa using Over.w (D₃.c x)
  have cq : (E.c y).left ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      spMap ((algebraMap R' (FractionRing R')).comp ρ) ≫ (D₁.c (p.xe x)).left := by
    rw [← hy']; exact q₁.c_pr y
  have cp : (D₃.c x).left ≫ GlobalTheory.PsiEvenPull.proj p = spMap ρ ≫ (D₁.c (p.xe x)).left := p.c_pr x
  have a1 : (e ≫ κ) ≫ GlobalTheory.PsiEvenPull.proj p = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by
    rw [Category.assoc, h₁]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ GlobalTheory.PsiEvenPull.proj q₁ =
      (jK R' ≫ (D₃.c x).left) ≫ GlobalTheory.PsiEvenPull.proj p
    rw [Category.assoc, Category.assoc, cq, Category.assoc, cp, ← Category.assoc (jK (FractionRing R')),
      ← Category.assoc r', hr2, ← Category.assoc (jK R'), ← GlobalTheory.ArcPull.fracMap_sq hρ, Category.id_comp]
  have a2 : (e ≫ κ) ≫ D₃.P.A.hom = D₃.xK x ≫ D₃.P.A.hom := by
    rw [Category.assoc, gκ.1.w]
    show (r' ≫ jK (FractionRing R') ≫ (E.c y).left) ≫ E.P.A.hom ≫ spMap (algebraMap R' (FractionRing R')) =
      (jK R' ≫ (D₃.c x).left) ≫ D₃.P.A.hom
    simp only [Category.assoc, reassoc_of% b1, b3, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, hrj, Category.id_comp]; rfl
  have hx : e ≫ κ = D₃.xK x := gpp.1.hom_ext a1 a2
  obtain ⟨JE, hJE⟩ := GlobalTheory.DegPull.exists_good' E.P.isLB z
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.DegPull.exists_good' D₁.P.isLB z
  have v₂ := GlobalTheory.ArcPull.psi_val q₂ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ hJE y
  have v₁ := GlobalTheory.ArcPull.psi_val q₁ (GlobalTheory.ArcPull.genMap hρ) r' hr2 hJ₁ hJE y
  have v₃ := GlobalTheory.ArcPull.psi_val p (GlobalTheory.ArcPull.genMap hρ) (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' x
  rw [hy'] at v₁
  rw [v₁, Category.id_comp] at v₃
  have ex₂ : e ≫ GlobalTheory.PsiEvenPull.proj q₂ = D₃.xK x ≫ Φ := by rw [← h₂, ← Category.assoc, hx]
  have ex₁ : e ≫ GlobalTheory.PsiEvenPull.proj q₁ = D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p := by rw [← h₁, ← Category.assoc, hx]
  have t := hT _ e z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) (JE e) (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p))
    (by rw [← Scheme.Hom.comp_apply, ex₂]; exact hJ _) (by rw [← Scheme.Hom.comp_apply, hx]; exact hJ' _) (hJE e)
    (by rw [← Scheme.Hom.comp_apply, ex₁]; exact hJ₁ _)
  simp only [hx] at t
  have o₂ : GlobalTheory.ArcPull.om q₂.w z J JE e = gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₂]
  have o₁ : GlobalTheory.ArcPull.om q₁.w z J₁ JE e = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) := by
    unfold GlobalTheory.ArcPull.om; rw [ex₁]
  have oo : GlobalTheory.ArcPull.om w z J J' (D₃.xK x) = gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) := rfl
  have op : GlobalTheory.ArcPull.om p.w z J₁ J' (D₃.xK x) =
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := rfl
  change val (D₂.psi (q₂.xe y)) _ z J = _
  rw [v₂, oo, o₂]
  rw [o₁, op] at v₃
  have v₄ : val (E.psi y) r' z JE = gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e) *
      ((gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)))⁻¹ *
        val (D₃.psi x) (𝟙 _) z J') := by
    rw [← v₃, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  rw [v₄]
  have t' : gw w (D₃.xK x) z (J (D₃.xK x ≫ Φ)) (J' (D₃.xK x)) =
      gw q₂.w e z (J (D₃.xK x ≫ Φ)) (JE e) * (gw q₁.w e z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (JE e))⁻¹ *
      gw p.w (D₃.xK x) z (J₁ (D₃.xK x ≫ GlobalTheory.PsiEvenPull.proj p)) (J' (D₃.xK x)) := by
    rw [← t, inv_mul_cancel_right]
  rw [t']
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegOfGenericFiniteNormalExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullDeg_of_generic_finite_normal_extension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')), IsPullDeg ρ D₁ D₃ → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E → IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E → Nonempty (IsPullDeg ρ D₂ D₃) := by
  first | exact @GlobalTheory.Mum.isPullDeg_of_generic | exact GlobalTheory.Mum.isPullDeg_of_generic | (intros; apply GlobalTheory.Mum.isPullDeg_of_generic <;> assumption)
end
