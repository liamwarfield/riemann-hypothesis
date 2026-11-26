module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VanishingIdealConePrimeHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointTranslatePure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedFibreThroughIso
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedPowerSectionBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlat
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoOfAssociatedGermsFlatStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_of_associated_germs_flat : ∀ (X Y : Scheme.{0}) [IsIntegral X] (f : Y ⟶ X) [Flat f] [Surjective f] (L L' : LB X) (s : L.Sec) (s' : L'.Sec), L.IsLB → L'.IsLB → (∃ i, s.f i ≠ 0) → (∀ y : Y, ∃ i i', f y ∈ L.U i ∧ f y ∈ L'.U i' ∧ Associated (gs f y (L.U i) (s.f i)) (gs f y (L'.U i') (s'.f i'))) → LBIso L L' := by
  first | exact @GlobalTheory.AssocDescent.lbIso_of_associated | exact GlobalTheory.AssocDescent.lbIso_of_associated | (intros; apply GlobalTheory.AssocDescent.lbIso_of_associated <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinates
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.PolAgree

open FieldDescentGen

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem crd_pull {X Y : Scheme.{0}} (φ : X ⟶ Y) (H : LB Y) {J : Type} (s : J → H.Sec) {R : Type} [CommRing R]
    (y : Sp R ⟶ X) (v : J → R) (h : Crd H s (y ≫ φ) v) :
    Crd (H.pull φ) (fun j => FieldDescentGen.secPull H φ (s j)) y v := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hl' : ⊤ ≤ y ⁻¹ᵁ (H.pull φ).U (fun _ => l) := fun z hz => mem_pull.2 (hl hz)
  refine ⟨fun _ => l, c, hl', fun j => ?_⟩
  rw [hv j]
  congr 1
  unfold valR
  rw [dite_eq_left hl, dite_eq_left hl']
  congr 1
  change _ = (y.appLE _ ⊤ hl').hom ((φ.appLE _ _ (pull_le H φ (fun _ => l))).hom ((s j).f l))
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem mulA_comp {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (m : ℕ) :
    Out.mulA A m ≫ φ = φ ≫ Out.mulA B m := by
  unfold Out.mulA
  rw [MonObj.comp_pow, Category.comp_id]
  have := map_pow (IsMonHom.monoidHom φ A) (𝟙 A) m
  simpa using this

theorem lbIso_pull : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (s' : J → (lbPow P'.L N).Sec) (a : J) (θ : (lbPow P.L 1).Sec) (θ' : (lbPow P'.L 1).Sec) (φ : P.A ⟶ P'.A), 1 ≤ m → IsMonHom φ → ⨆ j, Out.nonzeroLocus (s j) = ⊤ → (∀ (F : Type) [Field F] (y : Sp F ⟶ P.A.left) (v : J → F), Crd (lbPow P.L N) s y v → Crd (lbPow P'.L N) s' (y ≫ φ.left) v) → (∃ l, θ.f l ≠ 0) → (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s a).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((θ).f l))) → (∀ (y : P'.A.left) k l, y ∈ (lbPow P'.L N).U k → (Out.mulA P'.A m).left y ∈ (lbPow P'.L 1).U l → Associated (gs (𝟙 P'.A.left) y ((lbPow P'.L N).U k) ((s' a).f k)) (gs (Out.mulA P'.A m).left y ((lbPow P'.L 1).U l) ((θ').f l))) → LBIso (P'.L.pull φ.left) P.L := by
  intro h K _ _ P P' N m J s s' a θ θ' φ hm hφ hs hcrd hθ hP hP'
  have := polAV_isIntegral_of_isAlgClosed K P
  have hL := P.isLB
  have hL' := P'.isLB
  have hN : (lbPow P.L N).IsLB := LB.isLB_linComb hL _ _
  have hN' : (lbPow P'.L N).IsLB := LB.isLB_linComb hL' _ _
  have h1 : (lbPow P.L 1).IsLB := LB.isLB_linComb hL _ _
  have h1' : (lbPow P'.L 1).IsLB := LB.isLB_linComb hL' _ _
  have hmul := h.mulN _ P m hm
  have hfl : Flat (Out.mulA P.A m).left := hmul.2.1
  have hsu : Surjective (Out.mulA P.A m).left := hmul.2.2.1
  have hc : (Out.mulA P.A m).left ≫ φ.left = φ.left ≫ (Out.mulA P'.A m).left := by
    rw [← Over.comp_left, mulA_comp, Over.comp_left]
  have hw := CrdIso.exists_chart_unit (H := lbPow P.L N) (H' := (lbPow P'.L N).pull φ.left) (s := s)
    (s' := fun j => FieldDescentGen.secPull _ φ.left (s' j)) hs (fun F _ y v hv => crd_pull _ _ _ _ _ (hcrd F y v hv))
  have key : LBIso (lbPow P.L 1) ((lbPow P'.L 1).pull φ.left) := by
    refine GlobalTheory.T.lbIso_of_associated_germs_flat _ _ (Out.mulA P.A m).left _ _ θ (FieldDescentGen.secPull _ φ.left θ') h1 (LB.isLB_pull h1' _) hθ fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hN y
    obtain ⟨k', hk'⟩ := exists_chart hN' (φ.left y)
    obtain ⟨l, hl⟩ := exists_chart h1 ((Out.mulA P.A m).left y)
    obtain ⟨l', hl'⟩ := exists_chart h1' (φ.left ((Out.mulA P.A m).left y))
    have hl'' : (Out.mulA P'.A m).left (φ.left y) ∈ (lbPow P'.L 1).U l' := by
      rw [← Scheme.Hom.comp_apply, ← hc]; exact hl'
    have hlp : (Out.mulA P.A m).left y ∈ ((lbPow P'.L 1).pull φ.left).U (fun _ => l') := mem_pull.2 hl'
    have hkp : y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') := mem_pull.2 hk'
    refine ⟨l, fun _ => l', hl, hlp, ?_⟩
    have e1 : gs (Out.mulA P.A m).left y _ ((FieldDescentGen.secPull _ φ.left θ').f (fun _ => l')) =
        (φ.left.stalkMap y).hom (gs (Out.mulA P'.A m).left (φ.left y) _ (θ'.f l')) := by
      rw [← gs_comp _ _ _ _ hl'', ← hc]
      exact gs_appLE _ _ _ _ _ _ hlp _
    have e2 : gs (𝟙 P.A.left) y _ ((FieldDescentGen.secPull _ φ.left (s' a)).f (fun _ => k')) =
        (φ.left.stalkMap y).hom (gs (𝟙 P'.A.left) (φ.left y) _ ((s' a).f k')) := by
      rw [← gs_stalkMap _ _ _ hk']
      exact (gs_appLE _ _ _ _ _ _ hkp _).trans (by rw [Category.id_comp])
    obtain ⟨w, hw⟩ := hw k (fun _ => k')
    have hx : (𝟙 P.A.left : _ ⟶ _) y ∈ ((lbPow P'.L N).pull φ.left).U (fun _ => k') ⊓ (lbPow P.L N).U k :=
      ⟨hkp, hk⟩
    have e := congrArg (gs (𝟙 P.A.left) y _) (hw a)
    rw [gs_mul _ _ _ hx, gs_res _ _ _ hx, gs_res _ _ _ hx, gs_unit _ _ _ hx, e2] at e
    have a1 := (hP' (φ.left y) k' l' hk' hl'').map (φ.left.stalkMap y).hom
    rw [e1]
    refine (hP y k l hk hl).symm.trans (Associated.trans ?_ a1)
    exact ⟨_, (_root_.mul_comm _ _).trans e.symm⟩
  have oneIso {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) : LBIso (lbPow L 1) L := by
    apply CechPic.iso_of_chart hL
    refine ⟨fun j => j PUnit.unit, fun _ _ hy => Set.mem_iInter.1 hy PUnit.unit, ?_⟩
    intro y p q hp hq
    refine (gm_linComb L _ _ (𝟙 X) y p q hp hq).trans ?_
    simp
  have pullOne {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : Y ⟶ X) :
      LBIso ((lbPow L 1).pull f) (L.pull f) := by
    apply CechPic.iso_of_chart (LB.isLB_pull hL f)
    refine ⟨fun j _ => j PUnit.unit PUnit.unit, fun _ _ hy => mem_pull.2 (Set.mem_iInter.1 (mem_pull.1 hy) PUnit.unit), ?_⟩
    intro y p q hp hq
    refine (gm_pull_g (lbPow L 1) f (𝟙 Y) y p q hp hq).trans ?_
    refine (gm_linComb L _ _ (𝟙 Y ≫ f) y _ _ (mem_pull.1 hp) (mem_pull.1 hq)).trans ?_
    simpa using (gm_pull_g L f (𝟙 Y) y (fun _ => p PUnit.unit PUnit.unit) (fun _ => q PUnit.unit PUnit.unit) (mem_pull.2 (Set.mem_iInter.1 (mem_pull.1 hp) PUnit.unit)) (mem_pull.2 (Set.mem_iInter.1 (mem_pull.1 hq) PUnit.unit))).symm
  have e := (CechPic.cls_eq_iff h1 (LB.isLB_pull h1' _)).2 key
  have e1 := (CechPic.cls_eq_iff h1 hL).2 (oneIso P.L hL)
  have e2 := (CechPic.cls_eq_iff (LB.isLB_pull h1' _) (LB.isLB_pull hL' _)).2 (pullOne P'.L hL' φ.left)
  rw [e1, e2] at e
  exact (CechPic.cls_eq_iff (LB.isLB_pull hL' _) hL).1 e.symm

end GlobalTheory.ZH.PolAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.LbIsoPullOfHomPreservingCoordinatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_pull_of_hom_preserving_coordinates : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (s' : J → (lbPow P'.L N).Sec) (a : J) (θ : (lbPow P.L 1).Sec) (θ' : (lbPow P'.L 1).Sec) (φ : P.A ⟶ P'.A), 1 ≤ m → IsMonHom φ → ⨆ j, Out.nonzeroLocus (s j) = ⊤ → (∀ (F : Type) [Field F] (y : Sp F ⟶ P.A.left) (v : J → F), Crd (lbPow P.L N) s y v → Crd (lbPow P'.L N) s' (y ≫ φ.left) v) → (∃ l, θ.f l ≠ 0) → (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s a).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((θ).f l))) → (∀ (y : P'.A.left) k l, y ∈ (lbPow P'.L N).U k → (Out.mulA P'.A m).left y ∈ (lbPow P'.L 1).U l → Associated (gs (𝟙 P'.A.left) y ((lbPow P'.L N).U k) ((s' a).f k)) (gs (Out.mulA P'.A m).left y ((lbPow P'.L 1).U l) ((θ').f l))) → LBIso (P'.L.pull φ.left) P.L := by
  first | exact @GlobalTheory.ZH.PolAgree.lbIso_pull | exact GlobalTheory.ZH.PolAgree.lbIso_pull | (intros; apply GlobalTheory.ZH.PolAgree.lbIso_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionForm


open TorsionZero in
theorem exists_sec_of_form {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp K) {L : LB X}
    (hL : L.IsLB) {N d : ℕ} {J : Type} (s : J → (lbPow L N).Sec) {F : MvPolynomial J K}
    (hF : F.IsHomogeneous d) :
    ∃ u : (lbPow L (N * d)).Sec, ∀ (z : Sp K ⟶ X) (v : J → K), z ≫ p = 𝟙 _ → Crd (lbPow L N) s z v →
      (⊤ ≤ z ⁻¹ᵁ Out.nonzeroLocus u ↔ MvPolynomial.eval v F ≠ 0) := by
  obtain ⟨R, _, _, _, 𝒜, _, Φ, -, -, -, hρ⟩ := SectionRing.exists_sectionRing K X p L hL
  have hm := aeval_mem_of_isHomogeneous 𝒜 (fun j => (Φ N (s j)).2) hF
  obtain ⟨u, hu⟩ := (Φ (N * d)).surjective ⟨_, hm⟩
  have hu' : (Φ _ u : R) = MvPolynomial.aeval (fun j => (Φ N (s j) : R)) F := congrArg Subtype.val hu
  refine ⟨u, ?_⟩
  rintro z v hz ⟨l, c, hl, hv⟩
  obtain ⟨ρ, hρc, hρ⟩ := hρ l
  let ev : R →ₐ[K] K :=
    { (TorsionZero.val z ((lbPow L 0).U l) hl).comp ρ with
      commutes' := fun a => (congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρc a)).trans
        (val_const p z hz _ hl a) }
  have e₁ : ev (Φ _ u) = TorsionZero.val z ((lbPow L (N * d)).U l) hl (u.f l) :=
    congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρ _ u)
  have e₂ : v = fun j => ev (Φ N (s j)) * c := funext fun j => by
    rw [hv, _root_.mul_comm, CrdCalc.valR_eq z _ hl]
    exact congrArg (· * (c : K)) (congrArg (TorsionZero.val z ((lbPow L 0).U l) hl) (hρ _ (s j))).symm
  rw [EndOnTorsion.le_nonzeroLocus_iff u z l hl, ← e₁, hu', MvPolynomial.comp_aeval_apply,
    ← MvPolynomial.coe_aeval_eq_eval]
  change _ ↔ MvPolynomial.aeval v F ≠ 0
  rw [e₂, aeval_mul_of_isHomogeneous _ _ hF, mul_ne_zero_iff]
  exact (and_iff_left (pow_ne_zero _ c.ne_zero)).symm

theorem mem_vanishingIdeal_of_vanish_on_torsion :
    Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (F : MvPolynomial J K), 4 ≤ N → (k : K) ≠ 0 → N ^ P.g * P.g.factorial * d < k ^ 2 → F.IsHomogeneous d → (∀ x : (Out.baseOver (Sp K)) ⟶ P.A, x ^ k = 1 → ∃ v : J → K, Crd (lbPow P.L N) s (x.left : Sp K ⟶ P.A.left) v ∧ MvPolynomial.eval v F = 0) → F ∈ MvPolynomial.vanishingIdeal K (cone P.A.hom (lbPow P.L N) s) := by
  intro h K _ _ P N d k J s F hN hk hd hF hx
  have := polAV_isIntegral_of_isAlgClosed K P
  obtain ⟨u, hu⟩ := exists_sec_of_form P.A.hom P.isLB s hF
  have h₅ : ∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ¬ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus u := fun x e hx' => by
    obtain ⟨v, hv, h0⟩ := hx x e
    exact (hu x.left v (Over.w x) hv).1 hx' h0
  rintro v ⟨z, hz, hv⟩
  by_contra hne
  have hzu := (hu z v hz hv).2 hne
  rcases Nat.eq_zero_or_pos P.g with hg | hg
  · let x : Out.baseOver (Sp K) ⟶ P.A := Over.homMk z hz
    have e : 𝟙 P.A = 1 := EndOnTorsion.eq_of_dim_zero P P hg _ _ (by rw [Category.comp_id, MonObj.comp_one])
    have e' : x = 1 := by rw [← Category.comp_id x, e, MonObj.comp_one]
    exact h₅ x (by rw [e', one_pow]) hzu
  · obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 ((TorsionZero.top_le_iff z _).1 hzu)
    have hM1 : 1 ≤ k := Nat.pos_of_ne_zero fun e => hk (by rw [e, Nat.cast_zero])
    have hcard := (h.mulN (Sp K) P _ hM1).2.2.2.2 K (𝟙 _) hk
    have h₄ := card_zeros_on_torsion_coset_le h.mulN SectionRing.exists_sectionRing
      (PowSec.exists_basis_sections h.globalSectionsRank) (veryAmple_lbPow h.ample) (exists_mulPull_sec h.mulPull)
      SmoothDim.ringKrullDim_affineOpen polAV_isIntegral_of_isAlgClosed isIntegral_adjoin_of_mul_pow_mem
      graded_bezout_bound K P N d k 1 hg hN hk u
      ⟨j, fun e => by rw [e, Scheme.basicOpen_zero] at hj; exact hj⟩
    have e : k ^ (2 * P.g) = k ^ 2 * k ^ (2 * P.g - 2) := by rw [← pow_add]; congr 1; omega
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun x => and_iff_left_of_imp (h₅ x)), hcard, e] at h₄
    exact absurd (Nat.le_of_mul_le_mul_right h₄ (pow_pos hM1 _)) (not_le.2 hd)

end GlobalTheory.TorsionForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.MemVanishingIdealOfFormVanishingTorsionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_vanishingIdeal_of_form_vanishing_torsion : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N d k : ℕ) (J : Type) (s : J → (lbPow P.L N).Sec) (F : MvPolynomial J K), 4 ≤ N → (k : K) ≠ 0 → N ^ P.g * P.g.factorial * d < k ^ 2 → F.IsHomogeneous d → (∀ x : (Out.baseOver (Sp K)) ⟶ P.A, x ^ k = 1 → ∃ v : J → K, Crd (lbPow P.L N) s (x.left : Sp K ⟶ P.A.left) v ∧ MvPolynomial.eval v F = 0) → F ∈ MvPolynomial.vanishingIdeal K (cone P.A.hom (lbPow P.L N) s) := by
  first | exact @GlobalTheory.TorsionForm.mem_vanishingIdeal_of_vanish_on_torsion | exact GlobalTheory.TorsionForm.mem_vanishingIdeal_of_vanish_on_torsion | (intros; apply GlobalTheory.TorsionForm.mem_vanishingIdeal_of_vanish_on_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplication
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplication
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGerm

theorem associated_gs_down {X Y Z : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)
    (b : (LB.LinComb L (K := Fin 1) (fun _ => σ) (fun _ => n)).Sec) (r : Z ⟶ X) (z : Z) (j : PUnit → L.ι)
    (hj : r z ∈ LB.wchart L (fun _ : PUnit => 𝟙 X) j) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Associated (gs r z (LB.wchart L (fun _ : PUnit => 𝟙 X) j) ((PowSec.down L σ ρ e n b).f j))
      (sval b (r ≫ ρ) z J) := by
  have hle := (PowSec.chart_eq L σ ρ e j).le
  have h₁ : gs r z (LB.wchart L (fun _ : PUnit => 𝟙 X) j) ((PowSec.down L σ ρ e n b).f j) =
      gs (r ≫ ρ) z (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) (b.f (fun _ => j PUnit.unit)) :=
    (gs_res r z hle hj _).trans (gs_pull r ρ z _ (hle hj) _)
  rw [h₁, sec_trans b (r ≫ ρ) z (j := fun _ => j PUnit.unit) (hle hj) (hJ.mem (fun _ : Fin 1 => σ) (r ≫ ρ))]
  exact associated_unit_mul_left _ _ (Units.isUnit _)

theorem germ_origin : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  intro hLaw K _ _ P N m J x th t ρ e a hth H hx
  let π : P.A ⟶ Out.baseOver (Sp K) := Over.homMk P.A.hom (Category.comp_id _)
  let ρ' : P.A ⟶ Out.baseOver (Sp K) ⊗ P.A := lift π (𝟙 _)
  have ρ₂ : ρ'.left ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_snd _ _ : ρ' ≫ _ = _)
  have ρ₁ : ρ'.left ≫ (fst (Out.baseOver (Sp K)) P.A).left = P.A.hom :=
    congrArg (fun q => q.left) (lift_fst _ _ : ρ' ≫ _ = _)
  have ρ₃ : (snd (Out.baseOver (Sp K)) P.A).left ≫ ρ'.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  obtain rfl : ρ = ρ'.left := by
    rw [← Category.comp_id ρ, ← ρ₃, ← Category.assoc, e, Category.id_comp]
  haveI : IsIso ρ'.left := ⟨_, ρ₂, ρ₃⟩
  refine ⟨?_, fun y k l hk hl => ?_⟩
  · by_contra hne
    push_neg at hne
    have hz : Out.SecM.ofSec P.A th = 0 := by
      refine Subtype.ext (funext fun j => ?_)
      obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
      exact PowSec.appLE_injective ρ'.left _ _
        (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ'.left ρ₂ (fun _ => k))
        ((hne fun _ => k).trans (map_zero _).symm)
    have : Subsingleton (Out.SecM P.A P.L (1 : ℕ) (Out.baseOver (Spec (CommRingCat.of K)))) :=
      subsingleton_of_forall_eq 0 fun y => by
        obtain ⟨r, hr⟩ := hth (Out.SecM.toSec P.A y)
        have e : y = r • Out.SecM.ofSec P.A th := Subtype.ext (funext hr)
        exact e.trans ((congrArg (r • ·) hz).trans (smul_zero r))
    have hnt : Nontrivial Γ((Out.baseOver (Spec (CommRingCat.of K))).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    have := hLaw.globalSectionsRank K P 1 le_rfl
    rw [Module.finrank_zero_of_subsingleton, one_pow] at this
    exact zero_ne_one this
  · obtain ⟨s, α, U, -, hs, hU, ht⟩ := H
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ y)
    have hI' : Good P.L y I := hI
    have b₁ := ThetaCoord.sv_act ((hU a).pt_eq.trans hx) (ht a) π hI' (𝟙 _)
    have b₂ := ThetaCoord.sv_mulPull hs π hI' (𝟙 _)
    rw [MonObj.comp_one, _root_.one_mul, b₂] at b₁
    have e₁ : (Out.mulA P.A m).left ≫ ρ'.left = (lift π (𝟙 P.A ^ m)).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id]
      congr 2
      exact Over.OverMorphism.ext (Over.w (Out.mulA P.A m))
    have a₁ := associated_gs_down P.L _ _ e (N : ℤ) (t a) (𝟙 _) y k hk hI'
    have a₂ := associated_gs_down P.L _ _ e ((1 : ℕ) : ℤ) th (Out.mulA P.A m).left y l hl hI'
    rw [Category.id_comp] at a₁
    rw [e₁] at a₂
    refine a₁.trans (Associated.trans ?_ a₂.symm)
    exact (Associated.of_eq b₁).trans ((associated_unit_mul_left _ _ (Units.isUnit _)).trans
      (associated_unit_mul_left _ _ (Units.isUnit _)))

end GlobalTheory.ThetaGerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ThetaFamilyOriginGermOfMultiplicationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFamily_origin_germ_of_multiplication : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  first | exact @GlobalTheory.ThetaGerm.germ_origin | exact GlobalTheory.ThetaGerm.germ_origin | (intros; apply GlobalTheory.ThetaGerm.germ_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIso
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelPullIso

open ReciprocityTheory.ChartRestriction.G.Out

theorem isThetaPt_of_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P' k (fun i => x i ≫ φ.hom) v) :
    IsThetaPt P k x v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  exact GlobalTheory.ThetaPtUp.isThetaPtOver_down (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q

section Basis

variable {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g)

theorem basis_pow (i : Fin (2 * g)) : levelBasis lev hg i ^ M = 1 := lev.torsion _

theorem basis_indep (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * g) → Fin M)
    (h : linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c' i : ℕ))) : c = c' := by
  subst hg; exact lev.indep K s c c' h

theorem basis_span (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A) (hy : y ^ M = 1) : ∃ c : Fin (2 * g) → Fin M,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c i : ℕ)) = y := by
  subst hg; exact lev.span K s y hy

theorem basis_pairing (i j : Fin (2 * g)) :
    WeilIs P.A P.L M (levelBasis lev hg i) (levelBasis lev hg j) (ze ^ stdSymp g i j) := by
  subst hg; exact lev.pairing i j

end Basis

theorem comp_pow_eq_one_iff {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ≅ B) [IsMonHom φ.hom]
    (x : T ⟶ A) (M : ℕ) : (x ≫ φ.hom) ^ M = 1 ↔ x ^ M = 1 := by
  let F : (T ⟶ A) →* (T ⟶ B) := IsMonHom.monoidHom φ.hom T
  have hF : Function.Injective F := fun a b h => (cancel_mono φ.hom).1 h
  have e : F (x ^ M) = (x ≫ φ.hom) ^ M := map_pow F x M
  rw [← e]
  exact map_eq_one_iff F hF

theorem exists_level (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] {P P' : PolAV S} (hg' : P'.g = P.g)
    (φ : P.A ≅ P'.A) [IsMonHom φ.hom] (hw : LBIso P.L (P'.L.pull φ.hom.left)) {M : ℕ} {ze : Γ(S, ⊤)ˣ}
    (lev' : Level P' M ze) : ∃ lev : Level P M ze, ∀ i, lev.pt i ≫ φ.hom = levelBasis lev' hg' i := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), ∀ i, x i ≫ φ.hom = levelBasis lev' hg' i :=
    ⟨fun i => levelBasis lev' hg' i ≫ φ.inv, fun i => by simp⟩
  have ht : ∀ i, x i ^ M = 1 := fun i => by
    rw [← comp_pow_eq_one_iff φ, hx]; exact basis_pow lev' hg' i
  have hc : ∀ {T : Over S} (h : T ⟶ baseOver S) (a : Fin (2 * P.g) → ℕ),
      linComb (fun i => h ≫ x i) a ≫ φ.hom = linComb (fun i => h ≫ levelBasis lev' hg' i) a := fun h a => by
    rw [ThetaPtDet.linComb_comp]
    exact congrArg (linComb · a) (funext fun i => by rw [Category.assoc, hx])
  refine ⟨⟨x, lev'.prim, ht, fun K _ _ s c c' e => ?_, fun K _ _ s y hy => ?_, fun i j => ?_⟩, hx⟩
  · exact basis_indep lev' hg' K s c c' ((hc _ _).symm.trans ((congrArg (· ≫ φ.hom) e).trans (hc _ _)))
  · obtain ⟨c, e⟩ := basis_span lev' hg' K s (y ≫ φ.hom) ((comp_pow_eq_one_iff φ y M).2 hy)
    exact ⟨c, (cancel_mono φ.hom).1 ((hc _ _).trans e)⟩
  · rw [← weilIs_iso_iff hL.globalFns hL.cube P P' φ w hw M _ _ (ht i) (ht j), hx, hx]
    exact basis_pairing lev' hg' i j

end GlobalTheory.LevelPullIso


open GlobalTheory.LevelPullIso in
theorem GlobalTheory.exists_level_thetaPt_of_polIso : Out.Laws → ∀ (g N' : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (hg : P.g = g) (hg' : P'.g = g) (φ : P.A ≅ P'.A), IsPolIso P P' φ → ∀ (ze : Γ(Sp K, ⊤)ˣ) (lev' : Out.Level P' (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P' N' (levelPoint lev' hg') v → ∃ lev : Out.Level P (N' ^ 2) ze, (∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i) ∧ Out.IsThetaPt P N' (levelPoint lev hg) v := by
  intro hL g N' K _ _ P P' hg hg' φ ⟨hφ, t⟩ ze lev' v hv
  subst hg
  have hw : LBIso P.L (P'.L.pull φ.hom.left) := LBIso.symm t
  obtain ⟨lev, hl⟩ := exists_level hL hg' φ hw lev'
  have hp : ∀ a, levelPoint lev rfl a ≫ φ.hom = levelPoint lev' hg' a := fun a => by
    rw [ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (Out.linComb · _) (funext hl)
  refine ⟨lev, hl, isThetaPt_of_iso φ hw (fun a => ThetaPtDet.levelPoint_pow lev rfl a) ?_⟩
  rw [funext hp]
  exact hv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelThetaPtOfPolarisedIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_thetaPt_of_polarisedIso : Out.Laws → ∀ (g N' : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (hg : P.g = g) (hg' : P'.g = g) (φ : P.A ≅ P'.A), IsPolIso P P' φ → ∀ (ze : Γ(Sp K, ⊤)ˣ) (lev' : Out.Level P' (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P' N' (levelPoint lev' hg') v → ∃ lev : Out.Level P (N' ^ 2) ze, (∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i) ∧ Out.IsThetaPt P N' (levelPoint lev hg) v := by
  first | exact @GlobalTheory.exists_level_thetaPt_of_polIso | exact GlobalTheory.exists_level_thetaPt_of_polIso | (intros; apply GlobalTheory.exists_level_thetaPt_of_polIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.DegreeFormsDimensionAbelianConeLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianFormCount

theorem hilb_cone_le_of_span {K : Type} [Field K] {X : Scheme.{0}} (p : X ⟶ Sp K) (L : LB X) (N d m : ℕ)
    {J : Type} [Finite J] (s : J → (lbPow L N).Sec) (b : Fin m → (lbPow L (N * d)).Sec)
    (hb : ∀ t : (lbPow L (N * d)).Sec, ∃ a : Fin m → K, ∀ j, t.f j = ∑ i, constFn p _ (a i) * (b i).f j) :
    hilb (cone p (lbPow L N) s) d ≤ m := by
  have hC : ∀ v : cone p (lbPow L N) s, ∃ (x : Sp K ⟶ X) (l : PUnit → L.ι) (c : K) (_ : x ≫ p = 𝟙 _)
      (h : ⊤ ≤ x ⁻¹ᵁ SectionRing.chart L l),
      ∀ j, v.1 j = TorsionZero.val x _ h ((s j).f l) * c := by
    rintro ⟨v, x, hx, l, c, hl, hv⟩
    exact ⟨x, l, c, hx, hl, fun j => (hv j).trans ((_root_.mul_comm _ _).trans
      (congrArg (· * (c : K)) (dif_pos hl)))⟩
  choose x l c hx hl hv using hC
  let β : Fin m → cone p (lbPow L N) s → K := fun i v =>
    TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) * c v ^ d
  have le : (MvPolynomial.homogeneousSubmodule J K d).map
      (LinearMap.pi fun v : cone p (lbPow L N) s => (MvPolynomial.aeval (R := K) v.1).toLinearMap) ≤
      Submodule.span K (Set.range β) := by
    rintro _ ⟨F, hF, rfl⟩
    have hm := TorsionZero.aeval_mem_of_isHomogeneous (SectionRing.secs p L)
      (x := fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L))
      (fun j => (SectionRing.secEquiv p L N (s j)).2) hF
    obtain ⟨a, ha⟩ := hb ((SectionRing.secEquiv p L (N * d)).symm ⟨_, hm⟩)
    refine (Submodule.mem_span_range_iff_exists_fun K).2 ⟨a, funext fun v => ?_⟩
    let ev : SectionRing.Fam p L →ₐ[K] K :=
      { (TorsionZero.val (x v) _ (hl v)).comp (SectionRing.evalFam p L (l v)) with
        commutes' := fun r => TorsionZero.val_const p (x v) (hx v) _ (hl v) r }
    have h1 : ev (MvPolynomial.aeval (fun j => (SectionRing.secEquiv p L N (s j) : SectionRing.Fam p L)) F) =
        ∑ i, a i * TorsionZero.val (x v) _ (hl v) ((b i).f (l v)) :=
      (congrArg (TorsionZero.val (x v) _ (hl v)) (ha (l v))).trans ((map_sum _ _ _).trans
        (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans
          (congrArg (· * _) (TorsionZero.val_const p (x v) (hx v) _ (hl v) (a i)))))
    rw [MvPolynomial.comp_aeval_apply] at h1
    change _ = MvPolynomial.aeval v.1 F
    rw [show v.1 = _ from funext (hv v), TorsionZero.aeval_mul_of_isHomogeneous _ _ hF]
    refine Eq.trans ?_ (congrArg (· * c v ^ d) h1).symm
    rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have := Module.Finite.span_of_finite K (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

theorem hilb_cone_le : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (s : J → (lbPow P.L N).Sec) (d : ℕ), 1 ≤ N → 1 ≤ d → hilb (cone P.A.hom (lbPow P.L N) s) d ≤ (N * d) ^ P.g := by
  intro h K _ _ P N J _ s d hN hd
  obtain ⟨b, hb⟩ := PowSec.exists_basis_sections h.globalSectionsRank K P (N * d) (Nat.mul_pos hN hd)
  exact hilb_cone_le_of_span P.A.hom P.L N d _ s b fun t => (hb t).exists

end GlobalTheory.AbelianFormCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateCones
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateCones
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.IsoCone
open GlobalTheory.ZH.CrdCalc GlobalTheory.ZH.ImmSep GlobalTheory.ZH.ToImm

theorem dense_points {K : Type} [Field K] [IsAlgClosed K] {Y : Scheme.{0}} (p : Y ⟶ Sp K)
    [LocallyOfFiniteType p] :
    Dense (⋃ a : {x : Sp K ⟶ Y // x ≫ p = 𝟙 _}, Set.range a.1) := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  have hd : Dense (closedPoints Y) := by
    rw [dense_iff_closure_eq, closure_closedPoints]
  refine hd.mono fun c hc => Set.mem_iUnion.2 ⟨⟨_, pointOfClosedPoint_comp p c hc⟩,
    IsLocalRing.closedPoint K, pointOfClosedPoint_apply p c hc _⟩

theorem exists_hom {K : Type} [Field K] [IsAlgClosed K] {X Y : Scheme.{0}} [IsReduced Y] (p : X ⟶ Sp K)
    (p' : Y ⟶ Sp K) [LocallyOfFiniteType p'] {H : LB X} {H' : LB Y} {J : Type} [Fintype J] {s : J → H.Sec}
    {s' : J → H'.Sec} (hH : H.IsLB) (hH' : H'.IsLB) (hI : ImmBy p H s Set.univ) (hI' : ImmBy p' H' s' Set.univ)
    (hc : cone p' H' s' ⊆ cone p H s) :
    ∃ g : Y ⟶ X, g ≫ p = p' ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ Y) (v : J → R),
      Crd H' s' y v → Crd H s (y ≫ g) v := by
  have hx : ∀ a : {x : Sp K ⟶ Y // x ≫ p' = 𝟙 _}, ∃ x' : Sp K ⟶ X, x' ≫ p = a.1 ≫ p' ∧
      ∃ v, Crd H' s' a.1 v ∧ Crd H s x' v := by
    intro a
    obtain ⟨v, hv⟩ := crd_exists hH' s' a.1
    obtain ⟨x', h1, h2⟩ := hc ⟨a.1, a.2, hv⟩
    exact ⟨x', h1.trans a.2.symm, v, hv, h2⟩
  choose x' hx' using hx
  have hcov : ⨆ j, Out.nonzeroLocus (s' j) = ⊤ := by simpa using hI'.1
  obtain ⟨g, h1, -, h3⟩ := exists_factor K X Y p p' H H' J s s' hH hH' hI hcov K _
    (fun a : {x : Sp K ⟶ Y // x ≫ p' = 𝟙 _} => a.1) x' (dense_points p') hx'
  exact ⟨g, h1, h3⟩

theorem eq_id {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) {H : LB X} {J : Type} {s : J → H.Sec}
    (hH : H.IsLB) (hI : ImmBy p H s Set.univ) (g : X ⟶ X) (hg : g ≫ p = p)
    (h : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X) (v : J → R),
      Crd H s y v → Crd H s (y ≫ g) v) : g = 𝟙 X := by
  refine ext_local _ _ fun R _ _ y => ?_
  obtain ⟨v, hv⟩ := crd_exists hH s y
  rw [Category.comp_id]
  exact eq_of_crd_eq k X p H J s _ hH hI R _ _ v (by rw [Category.assoc, hg]) (h R y v hv) hv

theorem exists_iso : ∀ (K : Type) [Field K] [IsAlgClosed K] (X X' : Over (Sp K)) [IsIntegral X.left] [IsIntegral X'.left] [IsProper X.hom] [IsProper X'.hom] (H : LB X.left) (H' : LB X'.left) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy X.hom H s Set.univ → ImmBy X'.hom H' s' Set.univ → cone X.hom H s = cone X'.hom H' s' → ∃ φ : X ≅ X', ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X.left) (v : J → R), Crd H s y v → Crd H' s' (y ≫ φ.hom.left) v := by
  intro K _ _ X X' _ _ _ _ H H' J _ s s' hH hH' hI hI' hc
  obtain ⟨g, h1, h2⟩ := exists_hom X'.hom X.hom hH' hH hI' hI hc.le
  obtain ⟨g', h1', h2'⟩ := exists_hom X.hom X'.hom hH hH' hI hI' hc.ge
  have e : g ≫ g' = 𝟙 _ := eq_id X.hom hH hI _ (by rw [Category.assoc, h1', h1]) fun R _ _ y v hv => by
    rw [← Category.assoc]
    exact h2' R _ v (h2 R y v hv)
  have e' : g' ≫ g = 𝟙 _ := eq_id X'.hom hH' hI' _ (by rw [Category.assoc, h1, h1']) fun R _ _ y v hv => by
    rw [← Category.assoc]
    exact h2 R _ v (h2' R y v hv)
  exact ⟨Over.isoMk ⟨g, g', e, e'⟩ h1, h2⟩

end GlobalTheory.ZH.IsoCone
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsIsoOfEqualCoordinateConesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_of_equal_coordinateCones : ∀ (K : Type) [Field K] [IsAlgClosed K] (X X' : Over (Sp K)) [IsIntegral X.left] [IsIntegral X'.left] [IsProper X.hom] [IsProper X'.hom] (H : LB X.left) (H' : LB X'.left) (J : Type) [Fintype J] (s : J → H.Sec) (s' : J → H'.Sec), H.IsLB → H'.IsLB → ImmBy X.hom H s Set.univ → ImmBy X'.hom H' s' Set.univ → cone X.hom H s = cone X'.hom H' s' → ∃ φ : X ≅ X', ∀ (R : Type) [CommRing R] [IsLocalRing R] (y : Sp R ⟶ X.left) (v : J → R), Crd H s y v → Crd H' s' (y ≫ φ.hom.left) v := by
  first | exact @GlobalTheory.ZH.IsoCone.exists_iso | exact GlobalTheory.ZH.IsoCone.exists_iso | (intros; apply GlobalTheory.ZH.IsoCone.exists_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrame
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.CrdDown

theorem val_of_rel {K : Type} [CommRing K] {X Y : Scheme.{0}} (x : Sp K ⟶ X) (ρ : X ⟶ Y) (p : Sp K ⟶ Y)
    (hp : x ≫ ρ = p) (U : X.Opens) (V : Y.Opens) (W : (Sp K).Opens) (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : U ≤ ρ ⁻¹ᵁ V)
    (hW : ⊤ ≤ W) (hWV : W ≤ p ⁻¹ᵁ V) (u : Γ(Sp K, W)ˣ) :
    ∃ c : Kˣ, ∀ (f : Γ(Y, V)) (w : Γ(Sp K, ⊤)),
      ((Sp K).presheaf.map (homOfLE hWV).op).hom ((p.app V).hom f) =
        ((Sp K).presheaf.map (homOfLE le_top).op).hom w * u.val →
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom w = (c : K) * valR x U ((ρ.appLE V U hV).hom f) := by
  subst hp
  obtain rfl : W = ⊤ := top_le_iff.1 hW
  let φ := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  refine ⟨(Units.map φ.toMonoidHom u)⁻¹, fun f w h => ?_⟩
  have e : ((Sp K).presheaf.map (homOfLE (le_top : (⊤ : (Sp K).Opens) ≤ ⊤)).op).hom w = w :=
    congrArg (fun φ => CommRingCat.Hom.hom φ w) ((Sp K).presheaf.map_id _)
  rw [e] at h
  have h1 : (x.appLE U ⊤ hU).hom ((ρ.appLE V U hV).hom f) = w * u.val :=
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.appLE_comp_appLE x ρ V U ⊤ hV hU)).trans h
  rw [CrdCalc.valR_eq x U hU, Units.eq_inv_mul_iff_mul_eq]
  refine Eq.trans ?_ (congrArg φ h1).symm
  rw [map_mul, _root_.mul_comm]
  rfl

theorem crd_down_of_isValueAt : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  intro K _ _ P N J t ρ e x τ w h
  have hx : (x.left : Sp K ⟶ P.A.left) (IsLocalRing.closedPoint K) ∈ ⨆ i, P.L.U i := by
    rw [P.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hi' := (CrdCalc.top_le_iff (x.left : Sp K ⟶ P.A.left) _).2 hi
  haveI : IsIso (snd (Out.baseOver (Sp K)) P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp K)) P.A.hom))
  have hp : (x.left : Sp K ⟶ P.A.left) ≫ ρ = (Out.ptSecT P.A x).left := by
    rw [← cancel_mono (snd (Out.baseOver (Sp K)) P.A).left]
    refine (Category.assoc _ _ _).trans ((congrArg (x.left ≫ ·) e).trans ((Category.comp_id _).trans ?_))
    exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Out.baseOver (Sp K))) x)).symm
  have hU : ⊤ ≤ (x.left : Sp K ⟶ P.A.left) ⁻¹ᵁ LB.wchart P.L (fun _ : PUnit => 𝟙 P.A.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  have hW : ⊤ ≤ LB.wchart P.L (fun _ : Fin 1 => x.left) (fun _ => i) :=
    fun y hy => Set.mem_iInter.2 fun _ => hi' hy
  obtain ⟨c, hc⟩ := val_of_rel (x.left : Sp K ⟶ P.A.left) ρ _ hp _ _ _ hU
    (PowSec.chart_eq P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (fun _ => i)).le hW
    (Out.val_le P.A P.L x (fun _ => i)) (τ.s (fun _ => i))
  exact ⟨fun _ => i, c, hU, fun a => hc _ _ (h a (fun _ => i))⟩

end GlobalTheory.ZH.CrdDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.HomogeneousCoordsOfIsValueAtFrameStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoords_of_isValueAt_frame : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (x : (Out.baseOver (Sp K)) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (Out.baseOver (Sp K)).left) (K := Fin 1) (fun _ => x.left) (fun _ => (N : ℤ)))) (w : J → Γ((Out.baseOver (Sp K)).left, ⊤)), (∀ a, Out.IsValueAt P.A P.L N (t a) x τ (w a)) → Crd (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) (x.left : Sp K ⟶ P.A.left) (fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (w a)) := by
  first | exact @GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | exact GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt | (intros; apply GlobalTheory.ZH.CrdDown.crd_down_of_isValueAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSections
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowSec


open Out in
theorem immBy_down_of_span : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left), 4 ≤ N → Submodule.span Γ((Out.baseOver (Sp K)).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Out.baseOver (Sp K)))) = ⊤ → ImmBy P.A.hom (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) Set.univ := by
  intro h K _ _ P n J _ t ρ ρ₂ hn hspan
  let T : Over (Sp K) := baseOver (Sp K)
  let c : Γ(T.left, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have ρ₁ : ρ ≫ (fst T P.A).left = P.A.hom :=
    ((congrArg (ρ ≫ ·) ((Category.comp_id _).symm.trans pullback.condition)).trans
      (Category.assoc _ _ _).symm).trans ((congrArg (· ≫ P.A.hom) ρ₂).trans (Category.id_comp _))
  have ρ₃ : (snd T P.A).left ≫ ρ = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ := ⟨_, ρ₂, ρ₃⟩
  let b : J → SecM P.A P.L n T := fun a => SecM.ofSec P.A (t a)
  let D : SecM P.A P.L n T → (lbPow P.L n).Sec := fun v =>
    down P.L (snd T P.A).left ρ ρ₂ n (SecM.toSec P.A v)
  have hlin : ∀ (a : J → K) j,
      (D (∑ i, c.symm (a i) • b i)).f j = ∑ i, constFn P.A.hom _ (a i) * (D (b i)).f j := by
    intro a j
    show (ρ.appLE _ _ (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).hom
      ((∑ i, c.symm (a i) • b i : SecM P.A P.L n T).1 (fun _ => j PUnit.unit)) = _
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.appLE _ _ (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).hom _ _).trans
      (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c.symm (a i))) ((b i).1 fun _ => j PUnit.unit)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (chart_eq P.L (snd T P.A).left ρ ρ₂ j).le).trans (appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c.symm (a i))) h1
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow h.ample K P n hn
  have himm : ImmBy P.A.hom (lbPow P.L n) s Set.univ := by
    refine ⟨by simpa only [Set.mem_univ, iSup_pos] using hcov, fun i _ => ?_⟩
    obtain ⟨haff, r, hr, hsurj⟩ := hs i
    refine ⟨haff, r, hr, (SpanImm.closure_eq_top_iff
      (RingHom.comp (P.A.hom.appLE ⊤ _ le_top).hom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) r).2 fun f => ?_⟩
    obtain ⟨F, hF⟩ := hsurj f
    exact ⟨F, hF.symm⟩
  haveI := P.isAb.proper
  refine SpanImm.immBy_of_span K _ P.A.hom _ (LB.isLB_linComb P.isLB _ _) _ J s _ himm fun i => ?_
  obtain ⟨w, hw⟩ := down_surjective P.L (snd T P.A).left ρ ρ₂ n (s i)
  have hw' : D (SecM.ofSec P.A w) = s i := hw
  have hm : (SecM.ofSec P.A w : SecM P.A P.L n T) ∈ Submodule.span Γ(T.left, ⊤) (Set.range b) :=
    hspan.ge Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hm
  refine ⟨fun i => c (a i), fun j => ?_⟩
  have := hlin (fun i => c (a i)) j
  simp only [RingEquiv.symm_apply_apply] at this
  rw [ha, hw'] at this
  exact this

end GlobalTheory.PowSec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsClosedImmersionOfSpanLinePowerSectionsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_span_linePowerSections : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ) (J : Type) [Fintype J] (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left), 4 ≤ N → Submodule.span Γ((Out.baseOver (Sp K)).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Out.baseOver (Sp K)))) = ⊤ → ImmBy P.A.hom (lbPow P.L N) (fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)) Set.univ := by
  first | exact @GlobalTheory.PowSec.immBy_down_of_span | exact GlobalTheory.PowSec.immBy_down_of_span | (intros; apply GlobalTheory.PowSec.immBy_down_of_span <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDet

theorem cone_subset (h : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) {g N k : ℕ}
    (hg : P.g = g) (hg' : P'.g = g) (hN : 4 ≤ N) (hk : (k : K) ≠ 0) (hb : N ^ g * g.factorial < k) {J : Type}
    [Fintype J] {s : J → (lbPow P.L N).Sec} {s' : J → (lbPow P'.L N).Sec}
    (hs : ImmBy P.A.hom _ s Set.univ) (hs' : ImmBy P'.A.hom _ s' Set.univ)
    (hx : ∀ x : Out.baseOver (Sp K) ⟶ P'.A, x ^ k = 1 →
      ∃ v : J → K, Crd (lbPow P'.L N) s' (x.left : Sp K ⟶ P'.A.left) v ∧ v ∈ cone P.A.hom _ s) :
    cone P'.A.hom _ s' ⊆ cone P.A.hom _ s := by
  intro w hw
  have hLB : (lbPow P.L N).IsLB := isLB_lbPow P.isLB N
  have hsm : SmoothOfRelativeDimension g P.A.hom := by
    rw [← hg]
    exact P.smoothDim
  obtain ⟨hpr, hhom, hX, hdim⟩ := ZH.ConePrime.isPrime_vanishingIdeal_cone K P.A.left P.A.hom (lbPow P.L N) J s
    Set.univ hLB hs (polAV_isIntegral_of_isAlgClosed K P) g hsm
  have hnz : ∃ i ∈ (Set.univ : Set J), w i ≠ 0 := by
    obtain ⟨x, -, hxw⟩ := hw
    have h1 : ⊤ ≤ x ⁻¹ᵁ (⨆ i ∈ (Set.univ : Set J), Out.nonzeroLocus (s' i)) := by
      rw [hs'.1]
      simp
    simp only [Set.mem_univ, iSup_pos] at h1
    have h2 := (ZH.CrdCalc.top_le_iff x _).1 h1
    rw [TopologicalSpace.Opens.mem_iSup] at h2
    obtain ⟨i, hi⟩ := h2
    exact ⟨i, Set.mem_univ _, ((ZH.CrdCalc.crd_isUnit_iff i hxw).2 ((ZH.CrdCalc.top_le_iff x _).2 hi)).ne_zero⟩
  refine ZH.ConeClosed.mem_cone_of_vanishing K P.A.left P.A.hom (lbPow P.L N) J s Set.univ hLB hs w hnz ?_
  intro Pf hPf
  refine ZH.eval_eq_zero_of_hilb_le K J _ g N hpr hhom hX hdim ?_ w ?_ Pf hPf
  · intro d hd
    have := AbelianFormCount.hilb_cone_le h K P N J s d (by omega) hd
    rwa [hg] at this
  · intro d F hd hF hFI
    have hFI' : F ∈ MvPolynomial.vanishingIdeal K (cone P'.A.hom (lbPow P'.L N) s') := by
      refine T.mem_vanishingIdeal_of_form_vanishing_torsion h K P' N d k J s' F hN hk ?_ hF ?_
      · rw [hg']
        calc N ^ g * g.factorial * d ≤ N ^ g * g.factorial * (N ^ g * g.factorial) := Nat.mul_le_mul_left _ hd
          _ < k * k := Nat.mul_self_lt_mul_self hb
          _ = k ^ 2 := (sq k).symm
      · intro x hx1
        obtain ⟨v, hv, hvC⟩ := hx x hx1
        exact ⟨v, hv, MvPolynomial.mem_vanishingIdeal_iff.1 hFI v hvC⟩
    exact MvPolynomial.mem_vanishingIdeal_iff.1 hFI' w hw

theorem levelPoint_zero {S : Scheme.{0}} {P : Out.PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Out.Level P M ze) {g : ℕ}
    (hg : P.g = g) : levelPoint lev hg 0 = 1 := by
  rw [ThetaPtDet.levelPoint_eq]
  simp [ReciprocityTheory.ChartRestriction.G.Out.linComb]

theorem levelPoint_single {S : Scheme.{0}} {P : Out.PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Out.Level P M ze) {g : ℕ}
    (hg : P.g = g) (i : Fin (2 * g)) : levelPoint lev hg (Pi.single i 1) = levelBasis lev hg i := by
  rw [ThetaPtDet.levelPoint_eq, ReciprocityTheory.ChartRestriction.G.Out.linComb, List.prod_ofFn,
    Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
  have ht : levelBasis lev hg i ^ M = 1 := lev.torsion _
  rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]

theorem exists_embedding (h : Out.Laws) {g m r N N' : ℕ} (hN : N = m ^ 2) (hN' : N' = r * m) (h4 : 4 ≤ N) {K : Type}
    [Field K] [IsAlgClosed K] (hK : (N' : K) ≠ 0) [NeZero (N' ^ 2)] (P : Out.PolAV (Sp K)) (hg : P.g = g)
    {ze : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ} (lev : Out.Level P (N' ^ 2) ze)
    {v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)}
    (hv : Out.IsThetaPt P N' (levelPoint lev hg) v) :
    ∃ (s : (Fin (2 * g) → ZMod (N' ^ 2)) → (lbPow P.L N).Sec) (θ : (lbPow P.L 1).Sec),
      ImmBy P.A.hom _ s Set.univ ∧
      (∀ c, Crd (lbPow P.L N) s ((levelPoint lev hg c ^ N').left : Sp K ⟶ P.A.left)
        fun a => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
          ((ze ^ thetaCoordExp m r a c).val * v (thetaCoordIdx m r a c))) ∧
      (∃ l, θ.f l ≠ 0) ∧ ∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l →
        Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((s 0).f k))
          (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) (θ.f l)) := by
  have hodd : Odd N' := hv.1
  obtain ⟨⟨th, t, hth, htf⟩, hform⟩ := (theta_coordinates h g m r N N' hN hN').1 (Sp K) P hg ze lev v hv
  obtain ⟨hcoord, -⟩ := hform th t hth htf
  obtain ⟨-, -, hrest⟩ := (theta_coordinates h g m r N N' hN hN').2 K hodd hK P hg ze lev
  obtain ⟨hspan, -, -⟩ := hrest th t hth htf
  obtain ⟨ρ, e⟩ : ∃ ρ : P.A.left ⟶ (Out.baseOver (Sp K) ⊗ P.A).left,
      ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left :=
    ⟨(lift (Over.homMk P.A.hom (by simp [Out.baseOver])) (𝟙 P.A)).left, by rw [← Over.comp_left, lift_snd]; rfl⟩
  obtain ⟨hθ, hassoc⟩ := T.thetaFamily_origin_germ_of_multiplication h K P N m _ (fun a => levelPoint lev hg a ^ r ^ 2) th t ρ e 0 hth htf
    (by rw [levelPoint_zero, one_pow])
  refine ⟨fun a => PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e (N : ℤ) (t a),
    PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) th,
    T.isClosedImmersion_of_span_linePowerSections h K P N _ t ρ e h4 hspan, ?_, hθ, hassoc⟩
  intro c
  obtain ⟨u, hu⟩ := hcoord c _ (DVR.exists_gen_of_local (V := K) P.L P.isLB _ _).choose_spec
  have hc := T.homogeneousCoords_of_isValueAt_frame K P N _ t ρ e (levelPoint lev hg c ^ N') _ _ hu
  set φ := CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of K)).hom with hφ
  have hu1 : φ ((u⁻¹ : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ) : Γ((Out.baseOver (Sp K)).left, ⊤)) * φ (u : Γ((Out.baseOver (Sp K)).left, ⊤)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  convert ZH.CrdCalc.crd_smul (Units.map φ.toMonoidHom u⁻¹) hc using 1
  ext a
  simp only [Units.coe_map, Units.val_mul, map_mul]
  linear_combination (-(φ ((ze ^ thetaCoordExp m r a c : Γ((Out.baseOver (Sp K)).left, ⊤)ˣ) : Γ((Out.baseOver (Sp K)).left, ⊤)) * φ (v (thetaCoordIdx m r a c)))) * hu1

end GlobalTheory.ThetaDet

namespace GlobalTheory


open ThetaDet in
theorem thetaPt_determines : Out.Laws → ThetaPtDeterminesSt := by
  intro h g n k j N N' hn hodd hk hN hN' hb K _ _ hn0 P P' hg hg' ze lev lev' v hv hv'
  haveI := P.isAb
  haveI := P'.isAb
  haveI : IsProper P.A.hom := IsAbelianScheme.proper
  haveI : IsProper P'.A.hom := IsAbelianScheme.proper
  haveI : AlgebraicGeometry.IsIntegral P.A.left := polAV_isIntegral_of_isAlgClosed K P
  haveI : AlgebraicGeometry.IsIntegral P'.A.left := polAV_isIntegral_of_isAlgClosed K P'
  have hN'' : N' = n ^ j * n ^ k * n ^ k := by rw [hN', hN]; ring
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    have hne : n ≠ 2 := by
      rintro rfl
      exact (by decide : ¬ Odd 2) hodd
    omega
  have h4 : 4 ≤ N := by
    have h1 : 3 ≤ n ^ k := le_trans hn3 (Nat.le_self_pow (by omega) n)
    rw [hN]
    nlinarith
  have hK : ((N' : ℕ) : K) ≠ 0 := by
    rw [hN'']
    push_cast
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn0) (pow_ne_zero _ hn0)) (pow_ne_zero _ hn0)
  have hN'0 : N' ≠ 0 := by
    rintro h0
    rw [h0, Nat.cast_zero] at hK
    exact hK rfl
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero 2 hN'0⟩
  have hoddN' : Odd N' := hv.1
  obtain ⟨s, θ, hs, hcrd, hθ, hass⟩ := ThetaDet.exists_embedding h hN hN'' h4 hK P hg lev hv
  obtain ⟨s', θ', hs', hcrd', hθ', hass'⟩ := ThetaDet.exists_embedding h hN hN'' h4 hK P' hg' lev' hv'
  have hcone1 : cone P'.A.hom _ s' ⊆ cone P.A.hom _ s := by
    refine ThetaDet.cone_subset h P P' hg hg' h4 hK hb hs hs' ?_
    intro x hx
    obtain ⟨c, rfl⟩ := ((theta_coordinates h g (n ^ k) (n ^ j * n ^ k) N N' hN hN'').2 K hoddN' hK P' hg' ze
      lev').2.1 x |>.1 hx
    exact ⟨_, hcrd' c, _, Over.w _, hcrd c⟩
  have hcone2 : cone P.A.hom _ s ⊆ cone P'.A.hom _ s' := by
    refine ThetaDet.cone_subset h P' P hg' hg h4 hK hb hs' hs ?_
    intro x hx
    obtain ⟨c, rfl⟩ := ((theta_coordinates h g (n ^ k) (n ^ j * n ^ k) N N' hN hN'').2 K hoddN' hK P hg ze
      lev).2.1 x |>.1 hx
    exact ⟨_, hcrd c, _, Over.w _, hcrd' c⟩
  obtain ⟨φ, hφ⟩ := T.exists_iso_of_equal_coordinateCones K P.A P'.A (lbPow P.L N) (lbPow P'.L N) _ s s' (isLB_lbPow P.isLB N)
    (isLB_lbPow P'.isLB N) hs hs' (Set.Subset.antisymm hcone2 hcone1)
  have heq : ∀ c, (levelPoint lev hg c ^ N') ≫ φ.hom = levelPoint lev' hg' c ^ N' := by
    intro c
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact ZH.ImmSep.eq_of_crd_eq K P'.A.left P'.A.hom (lbPow P'.L N) _ s' Set.univ (isLB_lbPow P'.isLB N) hs' K
      _ _ _ (by rw [Category.assoc, Over.w φ.hom, Over.w, Over.w]) (hφ K _ _ (hcrd c)) (hcrd' c)
  have hη : η ≫ φ.hom = η := by
    have h0 := heq 0
    rw [ThetaDet.levelPoint_zero, ThetaDet.levelPoint_zero, one_pow, one_pow] at h0
    have e1 : (1 : Out.baseOver (Sp K) ⟶ P.A) = η := Over.OverMorphism.ext rfl
    have e2 : (1 : Out.baseOver (Sp K) ⟶ P'.A) = η := Over.OverMorphism.ext rfl
    rw [e1, e2] at h0
    exact h0
  haveI hmon : IsMonHom φ.hom := h.rigidity (Sp K) P.A P'.A P.isAb P'.isAb φ.hom hη
  have hLBiso := T.lbIso_pull_of_hom_preserving_coordinates h K P P' N (n ^ k) _ s s' 0 θ θ' φ.hom
    (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ (by omega))) hmon
    (by simpa only [Set.mem_univ, iSup_pos] using hs.1) (fun F _ y w hw => hφ F y w hw) hθ hass hass'
  have hpol : IsPolIso P P' φ := ⟨hmon, hLBiso⟩
  obtain ⟨lev'', hb'', hv''⟩ := T.exists_level_thetaPt_of_polarisedIso h g N' K P P' hg hg' φ hpol ze lev' v hv'
  have hnv := T.thetaPt_support_meets_every_coset h g n N' hn.two_le (by rw [hN'']; exact Dvd.dvd.mul_left (pow_dvd_pow n hk) _) K P hg ze
    lev v hv
  have hpowN : N' = n ^ (j + 2 * k) := by rw [hN'']; ring
  have hpw : ∀ i, levelBasis lev hg i ^ N' = levelBasis lev'' hg i ^ N' := by
    intro i
    apply (cancel_mono φ.hom).1
    rw [pow_comp, pow_comp, hb'' i, ← pow_comp, ← ThetaDet.levelPoint_single lev hg i, heq,
      ThetaDet.levelPoint_single]
  refine ⟨φ, hpol, fun i => ?_⟩
  rw [T.levelBasis_eq_of_same_thetaPt h g n (j + 2 * k) N' hodd hpowN K P hg ze lev lev'' v hv hv'' hpw hnv i, hb'' i]

end GlobalTheory
