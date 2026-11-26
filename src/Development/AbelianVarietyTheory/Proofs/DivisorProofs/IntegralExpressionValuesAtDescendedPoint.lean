module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameValueLocalUnitsMulSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfield

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG.ThetaVal

open GlobalTheory.USep.EvG

theorem one_left' {S X : Scheme.{0}} (G : Over S) [GrpObj G] (t : X ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  rw [Hom.one_def]; rfl

theorem toUnit_eta_left {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    (toUnit G ≫ η[G]).left = G.hom ≫ (η[G]).left := by
  rfl

@[reassoc]
theorem spMap_two' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem eta_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) : (toUnit G' ≫ η[G']).left ≫ F = G'.hom ≫ f ≫ (η[G]).left := by
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hF G'.hom (G'.hom ≫ f) rfl
  have h1 := he 1
  rw [map_one, one_left', one_left'] at h1
  rw [toUnit_eta_left, ← h1, Category.assoc]

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

theorem famφB_one (D : DegPre V₁) : D.famφB 0 1 = 𝟙 _ := by
  have h : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0) = 𝟙 D.P.A := by
    rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
    exact mul_one (𝟙 D.P.A)
  show (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = _
  rw [h]; rfl

theorem famφB_two (D : DegPre V₁) : D.famφB 0 2 = D.famφB 0 3 := by
  show (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left
  rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
  rfl

def chartPullCompPull {X X' Y : Scheme.{0}} (L : LB X) (F : X' ⟶ X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X'))
    (ε : K → ℤ) : ChartPull (LB.LinComb L (fun k => φ k ≫ F) ε) (LB.LinComb (L.pull F) φ ε) (𝟙 Y) :=
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart (L.pull F) φ (fun k _ => j k) :=
    fun j y hy => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  { idx := fun j k _ => j k
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun k => φ k ≫ F) ε (𝟙 Y) y j j' hj hj').trans
        (Eq.trans (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_)
          (gm_linComb (L.pull F) φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
        (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).symm
      simp only [Category.assoc] }

theorem gm_linCombIso_pull' {A A₂ Y₂ : Scheme.{0}} {L : LB A} {L₂ : LB A₂} {φ : A₂ ⟶ A} (w : LB.Iso L₂ (L.pull φ))
    {K : Type} [Fintype K] (φ' : K → (Y₂ ⟶ A₂)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y₂) (z : Z) (p : K → L.ι) (q : K → L₂.ι)
    (hm : r z ∈ LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q) :
    gm r z (LB.wchart (L.pull φ) φ' (fun k _ => p k) ⊓ LB.wchart L₂ φ' q)
      ((LB.linCombIso w φ' ε).s (fun k _ => p k, q)) = ∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ' k) z ((L.pull φ).U (fun _ => p k) ⊓ L₂.U (q k))
    ⟨Set.mem_iInter.1 hm.1 k, Set.mem_iInter.1 hm.2 k⟩ _)

theorem exists_conj_fibre_one {V₁ W₀ : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] (D : DegPre V₁) (ib : W₀ →+* V₁)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : D.P.A.left ⟶ B₀.left) (hβ : IsGrpPullback D.P.A B₀ (spMap ib) β)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ib a) ∈ k₀)
    (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt : (Over.mk (spMap ev) ⊗ D.P.A).left ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left,
      σt ≫ (fst (Over.mk (spMap ev)) D.P.A).left = (fst (Over.mk (spMap ev)) D.P.A).left ≫ spMap σ.toRingHom ∧
      σt ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β = (snd (Over.mk (spMap ev)) D.P.A).left ≫ β ∧
      ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left, x ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ →
        DefOver k₀ (x ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ β) → x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E D.P.A).left with hfK
  set q := (snd E D.P.A).left with hq
  have hw : q ≫ D.P.A.hom = fK ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  obtain ⟨Φ₀, hΦ₀⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib)) (by rw [Category.assoc, spMap_two'])
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (fK ≫ spMap σ.toRingHom ≫ spMap ev)
    (fK ≫ spMap (ev.comp ib))
    (by rw [Category.assoc, Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ D.P.A := Over.homMk q hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ D.P.A).left ⟶ (E ⊗ D.P.A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ q = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : σt ≫ q ≫ β = q ≫ β := by
    rw [reassoc_of% hsnd, ← hΦ₁ σD, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, hfst, hproj, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ D.P.A).hom = fK ≫ spMap ev := (Over.w (fst E D.P.A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ D.P.A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ D.P.A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ
        (spMap σ.toRingHom ≫ spMap ev) (spMap (ev.comp ib))
        (by rw [Category.assoc, spMap_two', spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show (x ≫ σt) ≫ q ≫ β = (spMap σ.toRingHom ≫ x) ≫ q ≫ β
      obtain ⟨P₀, hP₀⟩ := hdef
      rw [Category.assoc, hproj, Category.assoc, ← hP₀, ← Category.assoc,
        spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem gm_thetaIso {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) {B₀ : Scheme.{0}} {M₀ : LB B₀}
    (β : D.P.A.left ⟶ B₀) (w : LB.Iso D.P.L (M₀.pull β)) {K : Type} [Field K] (r : Sp K ⟶ D.P.A.left) (z : Sp K)
    (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀) → M₀.ι) (hJ : Good D.P.L z J) (hJ₀ : Good M₀ z J₀) :
    gm r z _ ((GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))).s
        (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)), fun k => J (r ≫ D.famφB 0 k))) = gwx w z J J₀ r := by
  have hz : r z ∈ (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).U (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).U (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨hJ₀.mem (fun k => D.famφB 0 k ≫ β) r, hJ.mem (D.famφB 0) r⟩
  refine (GlobalTheory.PolDeg.TautFrom.gm_isoPull _ _ _ r z _ hz).trans ?_
  rw [Category.comp_id]
  have hm : r z ∈ LB.wchart (M₀.pull β) (D.famφB 0) (fun k _ => J₀ (r ≫ (D.famφB 0 k ≫ β))) ⊓
      LB.wchart D.P.L (D.famφB 0) (fun k => J (r ≫ D.famφB 0 k)) :=
    ⟨Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hz.1 k), hz.2⟩
  refine (gm_linCombIso_pull' w (D.famφB 0) (DegPre.famε 1) r z (fun k => J₀ (r ≫ (D.famφB 0 k ≫ β)))
    (fun k => J (r ≫ D.famφB 0 k)) hm).trans ?_
  have h0 : D.famφB 0 0 = 𝟙 _ := rfl
  rw [Fin.prod_univ_four, h0, famφB_one D, famφB_two D]
  simp only [DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, Nat.cast_one, sub_self, zpow_zero, zpow_one, zpow_neg, one_mul,
    Category.comp_id, Category.id_comp, mul_inv_cancel_right]
  rw [_root_.one_mul, inv_mul_cancel_right]

theorem theta_values : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∃ κ : K, ∀ p : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, DefOver k₀ (spMap ev ≫ p.left ≫ β) → ∃ c ∈ k₀,
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J =
        ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ p.left))⁻¹).val * toStk z (κ * c) := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ θ hθ
  obtain ⟨-, hM₀, hβ, hw, -, -, -⟩ := hFB
  let u := GlobalTheory.PolDeg.TautFrom.isoPull (chartPullId (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (chartPullCompPull M₀ β (D.famφB 0) (DegPre.famε 1)) (LB.linCombIso w (D.famφB 0) (DegPre.famε 1))
  have hu : u.IsGen := GlobalTheory.PolDeg.TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen w hw _ _)
  have hL : (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hM : (LB.LinComb M₀ (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ hM₀ _ _
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_isoRel hL hM hu
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
  let E := Over.mk (spMap ev)
  let q := (snd E D.P.A).left
  have hqw : q ≫ D.P.A.hom = (fst E D.P.A).left ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  let R : (Sp K ⟶ (E ⊗ D.P.A).left) → Prop := fun x => x ≫ (fst E D.P.A).left = 𝟙 _ ∧ DefOver k₀ (x ≫ q ≫ β)
  have hcases : ∀ k : Fin 4, D.famφB 0 k = 𝟙 _ ∨ D.famφB 0 k ≫ β = D.P.A.hom ≫ spMap ib ≫ (η[B₀]).left := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inl (by show D.famφB 0 1 = _; exact famφB_one D)
    · exact Or.inr (by show D.famφB 0 2 ≫ β = _; rw [famφB_two D]; exact eta_push hβ)
    · exact Or.inr (by show D.famφB 0 3 ≫ β = _; exact eta_push hβ)
  obtain ⟨κ, -, hval⟩ := galois_values k₀ hk₀ (fun k => q ≫ (D.famφB 0 k ≫ β)) (DegPre.famε 1)
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s q) R
    (fun t => by
      obtain ⟨c, hc⟩ := fibre_one_dim D ev (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (hθ K ev)
        (fun k => D.famφB 0 k ≫ β) (DegPre.famε 1) hM₀ u hu s hs t
      exact ⟨c, fun x hR z J hJ => hc x hR.1 z J hJ⟩)
    (fun σ hσ => by
      obtain ⟨σt, hfst, hproj, hfix⟩ := exists_conj_fibre_one D ib B₀ β hβ K ev k₀ hk σ hσ
      refine ⟨σt, fun k => ?_, fun x hR => hfix x hR.1 hR.2⟩
      rcases hcases k with h | h
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        rw [h, Category.id_comp]
        exact hproj
      · show σt ≫ q ≫ D.famφB 0 k ≫ β = q ≫ D.famφB 0 k ≫ β
        have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
        rw [h, reassoc_of% hqw, reassoc_of% hfst, spMap_two'_assoc ib ev, reassoc_of% (spMap_conj k₀ _ hf σ hσ)])
  refine ⟨κ, fun p hdef => ?_⟩
  have hr : (spMap ev ≫ p.left) ≫ D.P.A.hom = spMap ev := by
    rw [Category.assoc, Over.w p]
    exact Category.comp_id _
  let a1 : Over.mk (spMap ev) ⟶ E := Over.homMk (𝟙 (Sp K)) (Category.id_comp _)
  let b1 : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (spMap ev ≫ p.left) hr
  let x : Sp K ⟶ (E ⊗ D.P.A).left := (lift a1 b1).left
  have hxf : x ≫ (fst E D.P.A).left = 𝟙 _ :=
    congrArg (fun m : Over.mk (spMap ev) ⟶ E => m.left) (lift_fst a1 b1)
  have hxq : x ≫ q = spMap ev ≫ p.left := congrArg (fun m : Over.mk (spMap ev) ⟶ D.P.A => m.left) (lift_snd a1 b1)
  have hRx : R x := ⟨hxf, by
    show DefOver k₀ (x ≫ q ≫ β)
    rw [reassoc_of% hxq]
    exact hdef⟩
  obtain ⟨c, hc, he⟩ := hval x hRx z J₀ hJ₀
  refine ⟨c, hc, ?_⟩
  have e1 : sval s (spMap ev ≫ p.left) z J₀ = toStk z (κ * c) := by
    rw [← he, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s q x z hJ₀, hxq]
  have e2 := gs_isoRel_at hs _ _ (spMap ev ≫ p.left) z (hJ₀.mem (fun k => D.famφB 0 k ≫ β) (spMap ev ≫ p.left))
    (hJ.mem (D.famφB 0) (spMap ev ≫ p.left))
  rw [gm_thetaIso D β w (spMap ev ≫ p.left) z J J₀ hJ hJ₀] at e2
  have e4 : (gwx w z J J₀ (spMap ev ≫ p.left)).val *
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J = toStk z (κ * c) := by
    rw [← e1]; exact e2.symm
  rw [← e4, Units.inv_mul_cancel_left]

end GlobalTheory.USep.EvG.ThetaVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGeneratorValuesScalarMulLocalUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∃ κ : K, ∀ p : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, DefOver k₀ (spMap ev ≫ p.left ≫ β) → ∃ c ∈ k₀,
      sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ p.left) z J =
        ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ p.left))⁻¹).val * toStk z (κ * c) := by
  first | exact @GlobalTheory.USep.EvG.ThetaVal.theta_values | exact GlobalTheory.USep.EvG.ThetaVal.theta_values | (intros; apply GlobalTheory.USep.EvG.ThetaVal.theta_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfield
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef.Idx

open GlobalTheory.Poinc.Sep.Coef (om exists_transport)

section Galois

variable {Jx V₁ W₀ K : Type} [CommRing V₁] [CommRing W₀] [Field K] {A : Over (Sp V₁)} [GrpObj A] {B₀ : Over (Sp W₀)}
  [GrpObj B₀] (f : W₀ →+* V₁) (q : Jx → (A.left ⟶ B₀.left))

def PowPts : Prop := ∀ (T : Over (Sp V₁)) (g : T.left ⟶ Sp W₀), T.hom ≫ spMap f = g →
  ∃ Φ : (T ⟶ A) ≃* (Jx → (Over.mk g ⟶ B₀)), ∀ x a, (Φ x a).left = x.left ≫ q a

variable (ev : V₁ →+* K) (k₀ : Subfield K)

def IsConj (σ : K ≃+* K) (σt : (Over.mk (spMap ev) ⊗ A).left ⟶ (Over.mk (spMap ev) ⊗ A).left) : Prop :=
  σt ≫ (fst (Over.mk (spMap ev)) A).left = (fst (Over.mk (spMap ev)) A).left ≫ spMap σ.toRingHom ∧
    ∀ a, σt ≫ (snd (Over.mk (spMap ev)) A).left ≫ q a = (snd (Over.mk (spMap ev)) A).left ≫ q a

def RatM (ψ : (Over.mk (spMap ev) ⊗ A).left ⟶ A.left) : Prop :=
  ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ σt, IsConj q ev σ σt → ∀ a, σt ≫ ψ ≫ q a = ψ ≫ q a

def RatP (x : Sp K ⟶ A.left) : Prop := ∀ a, DefOver k₀ (x ≫ q a)

variable {f q ev k₀}

theorem exists_conj (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt, IsConj q ev σ σt ∧ ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ A).left,
      x ≫ (fst (Over.mk (spMap ev)) A).left = 𝟙 _ → RatP q k₀ (x ≫ (snd (Over.mk (spMap ev)) A).left) →
        x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E A).left with hfK
  set s := (snd E A).left with hs
  have hw : s ≫ A.hom = fK ≫ spMap ev := (Over.w (snd E A)).trans (Over.w (fst E A)).symm
  have hf : ∀ a, (ev.comp f) a ∈ k₀ := hk
  have h2 : spMap ev ≫ spMap f = spMap (ev.comp f) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ₀, hΦ₀⟩ := hP (Over.mk (fK ≫ spMap ev)) (fK ≫ spMap (ev.comp f)) (by
    show (fK ≫ spMap ev) ≫ spMap f = _
    rw [Category.assoc, h2])
  obtain ⟨Φ₁, hΦ₁⟩ := hP (Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev)) (fK ≫ spMap (ev.comp f)) (by
    show (fK ≫ spMap σ.toRingHom ≫ spMap ev) ≫ spMap f = _
    rw [Category.assoc, Category.assoc, h2, spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ A := Over.homMk s hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ A).left ⟶ (E ⊗ A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ s = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : ∀ a, σt ≫ s ≫ q a = s ≫ q a := by
    intro a
    rw [reassoc_of% hsnd, ← hΦ₁ σD a, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, ⟨hfst, hproj⟩, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ A).hom = fK ≫ spMap ev := (Over.w (fst E A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := hP T (spMap (ev.comp f)) (by
        show (spMap σ.toRingHom ≫ spMap ev) ≫ spMap f = _
        rw [Category.assoc, h2, spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      funext a
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show ((x ≫ σt) ≫ s) ≫ q a = ((spMap σ.toRingHom ≫ x) ≫ s) ≫ q a
      obtain ⟨P₀, hP₀⟩ := hdef a
      simp only [Category.assoc] at hP₀ ⊢
      rw [hproj, ← hP₀, ← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem ratM_snd : RatM q ev k₀ (snd (Over.mk (spMap ev)) A).left := fun _ _ _ h => h.2

theorem ratM_const (x : Over.mk (spMap ev) ⟶ A) (hx : RatP q k₀ x.left) :
    RatM q ev k₀ (fst (Over.mk (spMap ev)) A ≫ x).left := fun σ hσ σt h a => by
  obtain ⟨P₀, hP₀⟩ := hx a
  show σt ≫ ((fst (Over.mk (spMap ev)) A).left ≫ x.left) ≫ q a = ((fst (Over.mk (spMap ev)) A).left ≫ x.left) ≫ q a
  simp only [Category.assoc]
  rw [reassoc_of% h.1]
  erw [← hP₀]
  congr 1
  rw [← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]

theorem ratM_mul (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) {x y : Over.mk (spMap ev) ⊗ A ⟶ A}
    (hx : RatM q ev k₀ x.left) (hy : RatM q ev k₀ y.left) : RatM q ev k₀ (x * y).left := fun σ hσ σt h a => by
  have hf : ∀ a, (ev.comp f) a ∈ k₀ := hk
  have h2 : spMap ev ≫ spMap f = spMap (ev.comp f) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ := hP (Over.mk (spMap ev) ⊗ A) ((fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)) (by
    rw [← h2, ← Category.assoc]
    exact congrArg (· ≫ spMap f) (Over.w (fst (Over.mk (spMap ev)) A)).symm)
  let τ : Over.mk ((fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)) ⟶
      Over.mk ((fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)) := Over.homMk σt (by
    show σt ≫ (fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f) = (fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)
    rw [reassoc_of% h.1]
    erw [spMap_conj k₀ _ hf σ hσ])
  have e : ∀ {x : Over.mk (spMap ev) ⊗ A ⟶ A}, RatM q ev k₀ x.left → τ ≫ Φ x a = Φ x a := fun {x} hx =>
    Over.OverMorphism.ext (by
      show σt ≫ (Φ x a).left = _
      rw [hΦ]; exact hx σ hσ σt h a)
  rw [← hΦ]
  show (τ ≫ Φ (x * y) a).left = _
  rw [map_mul, Pi.mul_apply, MonObj.comp_mul, e hx, e hy]

theorem ratP_mul (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) {x y : Over.mk (spMap ev) ⟶ A}
    (hx : RatP q k₀ x.left) (hy : RatP q k₀ y.left) : RatP q k₀ (x * y).left := fun a => by
  obtain ⟨Φ, hΦ⟩ := hP (Over.mk (spMap ev)) _ rfl
  erw [← hΦ]
  rw [map_mul, Pi.mul_apply]
  refine defOver_comp k₀ (P := (lift (Φ x a) (Φ y a)).left) (defOver_pullback k₀ ?_ ?_) (μ[B₀]).left
  · have e : (lift (Φ x a) (Φ y a)).left ≫ (fst B₀ B₀).left = x.left ≫ q a :=
      (congrArg (fun m => m.left) (lift_fst (Φ x a) (Φ y a))).trans (hΦ x a)
    exact e ▸ hx a
  · have e : (lift (Φ x a) (Φ y a)).left ≫ (snd B₀ B₀).left = y.left ≫ q a :=
      (congrArg (fun m => m.left) (lift_snd (Φ x a) (Φ y a))).trans (hΦ y a)
    exact e ▸ hy a

theorem ratM_one (h1 : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ A).left) :
    RatM q ev k₀ (1 : Over.mk (spMap ev) ⊗ A ⟶ A).left := by
  have := ratM_const 1 h1
  rwa [MonObj.comp_one] at this

variable {L : LB A.left} {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (A.left ⟶ X₂)} {e : I → ℤ}

theorem galois_sec [IsAlgClosed K] (hk₀ : IsAlgClosed k₀) (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) (hL : L.IsLB)
    (hL₂ : L₂.IsLB) (u : LB.Iso L (LB.LinComb L₂ π e)) (hu : u.IsGen)
    (hπ : ∀ (Z : Scheme.{0}) (x y : Z ⟶ A.left), (∀ a, x ≫ q a = y ≫ q a) → ∀ i, x ≫ π i = y ≫ π i)
    {Ix : Type} [Fintype Ix] (φ : Ix → ((Over.mk (spMap ev) ⊗ A).left ⟶ A.left)) (ε : Ix → ℤ)
    (hφ : ∀ k, RatM q ev k₀ (φ k)) (s : LB.Sec (LB.LinComb L φ ε))
    (h1 : ∀ t : LB.Sec (LB.LinComb L φ ε), ∃ c : K, ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ A).left,
      x ≫ (fst (Over.mk (spMap ev)) A).left = 𝟙 _ → ∀ z J, Good L z J → sval t x z J = toStk z c * sval s x z J) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ p : Over.mk (spMap ev) ⟶ A, RatP q k₀ p.left → ∀ (z : Sp K) J J₂, Good L z J → Good L₂ z J₂ →
      ∃ c ∈ k₀, (∏ k, om (Z := Sp K) u z J J₂ ((lift (𝟙 _) p).left ≫ φ k) ^ ε k).val *
        sval (Z := Sp K) s (lift (𝟙 _) p).left z J = toStk z (κ * c) := by
  obtain ⟨U, hU, vU⟩ := exists_transport u hu φ ε
  have hA := DVR.linComb_isLB L hL φ ε
  have hB := DVR.linComb_isLB L₂ hL₂ (fun p : Ix × I => φ p.1 ≫ π p.2) (fun p => ε p.1 * e p.2)
  obtain ⟨s', hs'⟩ := DVR.FlatBC.exists_isoRel hA hB hU s
  obtain ⟨κ, hκ, hval⟩ := galois_values k₀ hk₀ _ _ s' (fun x => x ≫ (fst (Over.mk (spMap ev)) A).left = 𝟙 _ ∧
      RatP q k₀ (x ≫ (snd (Over.mk (spMap ev)) A).left))
    (fun t' => by
      obtain ⟨t, ht⟩ := GlobalTheory.MBLow.lbIso_sec_onto _ _ _ U hA hB hU t'
      obtain ⟨c, hc⟩ := h1 t
      refine ⟨c, fun x hx z J₂ hJ₂ => ?_⟩
      choose J hJ using fun χ : Sp K ⟶ A.left => exists_chart hL (χ z)
      rw [vU t t' (fun i k => ht (i, k)) _ x z J J₂ hJ hJ₂, vU s s' hs' _ x z J J₂ hJ hJ₂, hc x hx.1 z J hJ]
      exact mul_left_comm _ _ _)
    (fun σ hσ => by
      obtain ⟨σt, hc, hfix⟩ := exists_conj hP hk σ hσ
      refine ⟨σt, fun p => ?_, fun x hx => hfix x hx.1 hx.2⟩
      rw [← Category.assoc]
      exact hπ _ _ _ (fun a => (Category.assoc _ _ _).trans (hφ p.1 σ hσ σt hc a)) p.2)
  refine ⟨κ, hκ, fun p hp z J J₂ hJ hJ₂ => ?_⟩
  obtain ⟨c, hc, he⟩ := hval (lift (𝟙 _) p).left ⟨congrArg (fun m => m.left) (lift_fst (𝟙 _) p), by
    have e : (lift (𝟙 _) p).left ≫ (snd (Over.mk (spMap ev)) A).left = p.left :=
      congrArg (fun m => m.left) (lift_snd (𝟙 _) p)
    exact e ▸ hp⟩ z J₂ hJ₂
  exact ⟨c, hc, (vU s s' hs' _ _ z J J₂ hJ hJ₂).symm.trans he⟩

end Galois

section Normalised

open GlobalTheory.UT

variable {Jx V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Jx → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}

structure Desc (f : W₀ →+* V₁) (q : Jx → (D.P.A.left ⟶ B₀.left)) (ev : V₁ →+* K) (k₀ : Subfield K)
    (u : LB.Iso D.P.L (LB.LinComb L₂ π e)) : Prop where
  hk₀ : IsAlgClosed k₀
  hP : PowPts f q
  hk : ∀ a, ev (f a) ∈ k₀
  hL₂ : L₂.IsLB
  hu : u.IsGen
  hπ : ∀ (Z : Scheme.{0}) (x y : Z ⟶ D.P.A.left), (∀ a, x ≫ q a = y ≫ q a) → ∀ i, x ≫ π i = y ≫ π i
  one : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left

variable {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

theorem galois_gen (H : Desc f q ev k₀ u) {P v} (G : SymFrame.GRep D.P.L (Over.mk (spMap ev) ⊗ D.P.A) P v)
    {Ix : Type} [Fintype Ix] (φ : Ix → ((Over.mk (spMap ev) ⊗ D.P.A).left ⟶ D.P.A.left)) (ε : Ix → ℤ)
    (hφ : ∀ k, RatM q ev k₀ (φ k))
    (hP : ∀ (U : Type) [CommGroup U] (h : _ → U), P U h = ∏ k, h (φ k) ^ ε k)
    (h₀ : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ D.P.A.left) → U),
      P U (fun ψ => h ((lift (𝟙 (Over.mk (spMap ev))) (1 : _ ⟶ D.P.A)).left ≫ ψ)) = 1)
    (h₁ : ∀ z J, Good D.P.L z J → v (Over.mk (spMap ev)) (lift (𝟙 _) 1) z J = 1)
    (p : Over.mk (spMap ev) ⟶ D.P.A) (hp : RatP q k₀ p.left) (z : Sp K) (J J₂) (hJ : Good D.P.L z J) (hJ₂ : Good L₂ z J₂) :
    ∃ c ∈ k₀, (P _ (fun ψ => om (Z := Sp K) u z J J₂ ((lift (𝟙 _) p).left ≫ ψ)) *
      @id ((Sp K).presheaf.stalk z)ˣ (v (Over.mk (spMap ev)) (lift (𝟙 _) p) z J)).val = toStk z c := by
  obtain ⟨t, ht, vt⟩ := G.out D.P.isLB φ ε hP
  obtain ⟨κ, hκ, hval⟩ := galois_sec H.hk₀ H.hP H.hk D.P.isLB H.hL₂ u H.hu H.hπ φ ε hφ (genSec t ht) (fun s => by
    obtain ⟨w, hw⟩ := exists_sec D.P.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
      (fun U _ hh => by simp [Fintype.prod_sum_type, ← Finset.prod_mul_distrib])
      (pullMulSec s (𝟙 _) (LB.invGen D.P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
    have le : (⊤ : (Over.mk (spMap ev) ⊗ D.P.A).left.Opens) ≤
        LB.wchart D.P.L (K := PEmpty) (Y := (Over.mk (spMap ev) ⊗ D.P.A).left) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    obtain ⟨a, ha⟩ := surj_fst GlobalTheory.abelianSchemeLaws_all.1.globalFns D.P.isAb (Over.mk (spMap ev))
      (((Over.mk (spMap ev) ⊗ D.P.A).left.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim))
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, fun x hx z J hJ => ?_⟩
    have e₁ := hw _ x z J hJ
    rw [sval_pullMulSec _ _ _ _ _ z hJ, Category.comp_id, val_inv, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e₁
    rw [sval_genSec _ _ _ z hJ, ← gs_appTop_of_section x _ hx z a]
    erw [ha]
    refine Eq.trans ?_ (congrArg (· * _) ((gs_res x z le trivial _).trans e₁).symm)
    rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one])
  obtain ⟨c₀, hc₀, e₀⟩ := hval 1 H.one z J J₂ hJ hJ₂
  obtain ⟨c, hc, e₁⟩ := hval p hp z J J₂ hJ hJ₂
  rw [sval_genSec _ _ _ z hJ] at e₀ e₁
  have a₀ := (hP _ (fun ψ => om (Z := Sp K) u z J J₂ ((lift (𝟙 (Over.mk (spMap ev))) (1 : _ ⟶ D.P.A)).left ≫ ψ))).symm.trans
    (h₀ _ (om (Z := Sp K) u z J J₂))
  have b₀ := (vt _ (lift (𝟙 _) 1) z J hJ).trans (h₁ z J hJ)
  erw [a₀, b₀] at e₀
  have k1 : κ * c₀ = 1 := (toStk z).injective (by rw [← e₀, map_one]; exact _root_.mul_one _)
  refine ⟨κ * c, k₀.mul_mem (eq_inv_of_mul_eq_one_left k1 ▸ k₀.inv_mem hc₀) hc, ?_⟩
  rw [← e₁, hP, Units.val_mul]
  exact congrArg₂ (· * ·) rfl (congrArg Units.val (vt _ (lift (𝟙 _) p) z J hJ).symm)

theorem cub_mem (H : Desc f q ev k₀ u) (x x' y : Over.mk (spMap ev) ⟶ D.P.A) (hx : RatP q k₀ x.left)
    (hx' : RatP q k₀ x'.left) (hy : RatP q k₀ y.left) (z : Sp K) (J J₂) (hJ : Good D.P.L z J) (hJ₂ : Good L₂ z J₂) :
    ∃ c ∈ k₀, ((om (Z := Sp K) u z J J₂ (x * x' * y).left * (om (Z := Sp K) u z J J₂ (x * x').left)⁻¹ *
      (om (Z := Sp K) u z J J₂ (x * y).left)⁻¹ * (om (Z := Sp K) u z J J₂ (x' * y).left)⁻¹ *
      om (Z := Sp K) u z J J₂ x.left * om (Z := Sp K) u z J J₂ x'.left * om (Z := Sp K) u z J J₂ y.left *
      (om (Z := Sp K) u z J J₂ (1 : Over.mk (spMap ev) ⟶ D.P.A).left)⁻¹) *
      @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x x' y)).val = toStk z c := by
  have r₁ := ratM_const x hx
  have r₂ := ratM_const x' hx'
  have r₃ : RatM q ev k₀ _ := ratM_snd
  have m := fun {a b} => ratM_mul (x := a) (y := b) H.hP H.hk
  have key := galois_gen H (SymFrame.grep_cub (D := D) (fst (Over.mk (spMap ev)) D.P.A ≫ x) (fst _ _ ≫ x') (snd _ _))
    ![((fst (Over.mk (spMap ev)) D.P.A ≫ x) * (fst _ _ ≫ x') * snd _ _).left,
      ((fst (Over.mk (spMap ev)) D.P.A ≫ x) * (fst _ _ ≫ x')).left, ((fst (Over.mk (spMap ev)) D.P.A ≫ x) * snd _ _).left,
      ((fst (Over.mk (spMap ev)) D.P.A ≫ x') * snd _ _).left, (fst (Over.mk (spMap ev)) D.P.A ≫ x).left,
      (fst (Over.mk (spMap ev)) D.P.A ≫ x').left, (snd (Over.mk (spMap ev)) D.P.A).left,
      (1 : Over.mk (spMap ev) ⊗ D.P.A ⟶ D.P.A).left] ![1, -1, -1, -1, 1, 1, 1, -1]
    (fun k => by
      fin_cases k
      exacts [m (m r₁ r₂) r₃, m r₁ r₂, m r₁ r₃, m r₂ r₃, r₁, r₂, r₃, ratM_one H.one])
    (fun U _ h => by simp [Fin.prod_univ_eight])
    (fun U _ h => by
      simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp,
        _root_.mul_one, _root_.one_mul]
      simp)
    (fun z J hJ => by
      simp only [lift_snd]
      exact (isCub_cubV D.cub hJ).face₃ _ _) y hy z J J₂ hJ hJ₂
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp] at key
  exact key

end Normalised

end GlobalTheory.Poinc.Sep.Coef.Idx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

open GlobalTheory.Poinc.Sep.Coef (om tele root_mem prod_mem)

theorem chi_mem : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN a b hb hbdef χ hχ
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  have h2 : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hP : Coef.Idx.PowPts ib (fun _ : PUnit => β) := by
    intro T' g hg
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb T'.hom g hg
    exact ⟨e.trans (MulEquiv.piUnique fun _ : PUnit => (Over.mk g ⟶ B₀)).symm, fun x u => by cases u; exact he x⟩
  have hone : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left := by
    intro _
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb (spMap ev) _ h2
    have e1 := he 1
    rw [map_one] at e1
    rw [← e1]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have H : Coef.Idx.Desc ib (fun _ : PUnit => β) ev k₀ w :=
    ⟨hk₀, hP, hk, hM₀, hw, fun _ _ _ h i => h i, hone⟩
  have pc : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c a).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ GlobalTheory.UChart.cpt D a) ≫ β)
    rw [Category.assoc, hc a, ← Category.assoc, h2]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have pb : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ b).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]; exact hbdef
  have pbi : ∀ i : ℕ, Coef.Idx.RatP (fun _ : PUnit => β) k₀ ((toUnit (Over.mk (spMap ev)) ≫ b) ^ i).left := by
    intro i
    induction i with
    | zero => rw [pow_zero]; exact hone
    | succ i ih => rw [pow_succ]; exact Coef.Idx.ratP_mul hP hk ih pb
  set x := toUnit (Over.mk (spMap ev)) ≫ D.c a with hx
  set y := toUnit (Over.mk (spMap ev)) ≫ b with hy
  have hyN : y ^ N₁ = 1 := by rw [hy, ← MonObj.comp_pow, hb, MonObj.comp_one]
  have hcub := hχ.2 (Over.mk (spMap ev)) z J hJ
  simp only [MonObj.comp_pow] at hcub
  choose c hc' ec using fun i : ℕ => Coef.Idx.cub_mem H x (y ^ i) y pc (pbi i) pb z J J₀ hJ hJ₀
  set h : (Over.mk (spMap ev) ⟶ D.P.A) → ((Sp K).presheaf.stalk z)ˣ := fun p => om (Z := Sp K) w z J J₀ p.left with hh
  set G := h (x * y) * (h x)⁻¹ * (h y)⁻¹ * h 1 with hG
  obtain ⟨c₁, hc₁, e₁⟩ := prod_mem (Finset.range N₁) (fun i => ⟨c i, hc' i, ec i⟩)
  have key : (∏ i ∈ Finset.range N₁, ((h (x * y ^ i * y) * (h (x * y ^ i))⁻¹ * (h (x * y))⁻¹ * (h (y ^ i * y))⁻¹ *
      h x * h (y ^ i) * h y * (h 1)⁻¹) * @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y))) =
      (G⁻¹ * val χ (spMap ev) z J) ^ N₁ := by
    rw [Finset.prod_mul_distrib, tele h x y N₁ hyN]
    have e3 : (∏ i ∈ Finset.range N₁, @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y)) =
        val χ (spMap ev) z J ^ N₁ := hcub
    have e4 : ∀ A B C E : ((Sp K).presheaf.stalk z)ˣ, A⁻¹ * B * C * E⁻¹ = (A * B⁻¹ * C⁻¹ * E)⁻¹ :=
      fun A B C E => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    rw [e3, e4, ← mul_pow]
  rw [key] at e₁
  obtain ⟨c₂, hc₂, e₂⟩ := root_mem hk₀ (z := z) (s := (G⁻¹ * val χ (spMap ev) z J).val) (n := N₁) (by omega) ⟨c₁, hc₁, by rw [← Units.val_pow_eq_pow_val]; exact e₁⟩
  refine ⟨c₂, hc₂, ?_⟩
  have hGe : G = gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
      (gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left) := by
    rw [hG, hh, hx, hy, ← MonObj.comp_mul]
    rfl
  rw [← hGe, ← e₂, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.USep.EvG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterValue_mem_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.chi_mem | exact GlobalTheory.USep.EvG.chi_mem | (intros; apply GlobalTheory.USep.EvG.chi_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpressionValuesAtDescendedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

theorem unit_of_val {K S : Type} [Field K] [CommRing S] [Nontrivial S] (f : K →+* S) {u v : Sˣ} {c : K}
    (h : u.val = v.val * f c) : ∃ m : Kˣ, (m : K) = c ∧ u = v * Units.map f.toMonoidHom m := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_zero] at h
    exact u.ne_zero h
  exact ⟨Units.mk0 c hc, rfl, Units.ext (by rw [h, Units.val_mul]; rfl)⟩

theorem toStk_surj' {K : Type} [Field K] (z : Sp K) : Function.Surjective (toStk z) := fun s => by
  obtain ⟨U, hU, a, rfl⟩ := (Sp K).presheaf.germ_exist s
  exact ⟨_, (toStk_valF_gs (𝟙 _) U z hU a).trans (gs_eq _ _ _ hU _)⟩

theorem units_identity {U : Type} [CommGroup U] (gO gB gP gC gCn R M2 M3 M4 M5 : U) :
    (gO⁻¹ * gB * M2) ^ 2 * (gP * gC⁻¹ * gB⁻¹ * gO * M3) ^ 2 * (gCn⁻¹ * gC * M4) *
        (gO * gC⁻¹ * gCn⁻¹ * gO * M5)⁻¹ * (R ^ 2)⁻¹ =
      gP ^ 2 * (gO⁻¹ ^ 2 * (R ^ 2)⁻¹) * (M2 ^ 2 * M3 ^ 2 * M4 * M5⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem sq_cancel {S : Type} [CommRing S] (a b c d f : S) (h : a * c = 1) :
    (a * b) ^ 2 * (c ^ 2 * d * f) = b ^ 2 * (d * f) := by
  linear_combination (a * c + 1) * b ^ 2 * d * f * h

theorem c_zero_eta {V₁ : Type} [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) : D.c 0 = η[D.P.A] := by
  rw [GlobalTheory.Poinc.ThetaOne.c_zero]
  rfl

theorem ev_values : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  intro N₁ hN V₁ _ _ _ hV hunit D X C _ e τ₀ θ hθ b hb t ht χt hχt G hG K _ _ ev k₀ hk₀ W₀ _ ib hB hib
  obtain ⟨B₀, iG, M₀, c₀, τ₁, β, w, hFB⟩ := (fromBase_iff D τ₀ ib).1 hB
  have hM₀ : M₀.IsLB := hFB.2.1
  let z : Sp K := IsLocalRing.closedPoint K
  choose J hJ using fun ψ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose J₀ hJ₀ using fun ψ : Sp K ⟶ B₀.left => exists_chart hM₀ (ψ z)
  have gJ : Good D.P.L z J := hJ
  have gJ₀ : Good M₀ z J₀ := hJ₀
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.thetaGenerator_values_scalar_mul_localUnit V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ θ hθ
  set r : Sp K ⟶ Sp V₁ := spMap ev with hr
  set U0 : ((Sp K).presheaf.stalk z)ˣ := (gwx w z J J₀ (r ≫ (D.c 0).left))⁻¹ ^ 2 * (rigV D r z J ^ 2)⁻¹ with hU0
  have hO : r ≫ (η[D.P.A]).left = r ≫ (D.c 0).left := by rw [c_zero_eta]
  have key : ∀ mu c, ∃ q ∈ k₀, toStk z (ev (G mu c)) = toStk z (κ ^ 2 * q) * U0.val := by
    intro mu c
    obtain ⟨hBd, -, hPd, -⟩ := GlobalTheory.T.torsionPoints_projections_defined_over_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib N₁ (by omega)
      (b c) (hb c) (e mu)
    obtain ⟨c1, hc1, e1⟩ := hκ (b c * D.c (e mu)) hPd
    obtain ⟨c2, hc2, e2⟩ := GlobalTheory.T.torsionFrame_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (b c) (hb c) hBd (t c) (ht c)
    obtain ⟨c3, hc3, e3⟩ := GlobalTheory.T.characterValue_mem_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ N₁ hN
      (e mu) (b c) (hb c) hBd (χt mu c) (hχt mu c)
    obtain ⟨c4, hc4, e4⟩ := GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀ (e mu)
    obtain ⟨c5, hc5, e5⟩ := GlobalTheory.T.periodGenerators_val_localUnits_mul_subfield V₁ hV hunit D τ₀ W₀ ib B₀ M₀ c₀ τ₁ β w hFB K ev k₀ hk₀ hib z J J₀ gJ gJ₀
      (e mu) (-e mu)
    have hPP : r ≫ (D.c (e mu) * b c).left = r ≫ (b c * D.c (e mu)).left := by rw [mul_comm]
    have h00 : r ≫ (D.c (e mu + -e mu)).left = r ≫ (D.c 0).left := by rw [add_neg_cancel]
    rw [hO] at e2 e3
    rw [hPP] at e3
    rw [h00] at e5
    obtain ⟨m2, rfl, u2⟩ := unit_of_val (toStk z) e2
    obtain ⟨m3, rfl, u3⟩ := unit_of_val (toStk z) e3
    obtain ⟨m4, rfl, u4⟩ := unit_of_val (toStk z) e4
    obtain ⟨m5, rfl, u5⟩ := unit_of_val (toStk z) e5
    have h1 := hG mu c (Sp K) r z J gJ
    rw [u2, u3, u4, u5, e1, units_identity, ← hU0] at h1
    have hL : gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) = toStk z (ev (G mu c)) := by
      have := GlobalTheory.RatioVal.gs_specMap ev z ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c))
      rw [Iso.inv_hom_id_apply] at this
      exact this
    refine ⟨c1 ^ 2 * ((m2 : K) ^ 2 * (m3 : K) ^ 2 * (m4 : K) * (m5 : K)⁻¹),
      k₀.mul_mem (k₀.pow_mem hc1 2) (k₀.mul_mem (k₀.mul_mem (k₀.mul_mem (k₀.pow_mem hc2 2) (k₀.pow_mem hc3 2)) hc4)
        (k₀.inv_mem hc5)), ?_⟩
    rw [← hL, h1, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val,
      sq_cancel _ _ _ _ _ (Units.inv_mul _)]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← map_inv, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Units.val_inv_eq_inv_val, map_mul, map_pow]
    ring
  obtain ⟨lam, hlam⟩ := toStk_surj' z U0.val
  refine ⟨κ ^ 2 * lam, fun mu c => ?_⟩
  obtain ⟨q, hq, eq⟩ := key mu c
  refine ⟨q, hq, (toStk z).injective ?_⟩
  rw [eq, ← hlam, ← map_mul]
  congr 1
  ring

end GlobalTheory.USep.EvG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralExpressionValuesAtDescendedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_expression_values_at_descended_point : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X)
    (τ₀ : GlobalTheory.UChart.Gens D) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)), (∀ c, b c ^ N₁ = 1) →
    ∀ (t : ∀ c, LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, (b c).left] (DegPre.lineε 1))),
      (∀ c, (t c).IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val (t c) r z J ^ (N₁ ^ 2) * val κ (r ≫ (b c).left) z J = 1) →
    ∀ (χt : ∀ (mu : X) (c : C), LB.Gen (LB.LinComb D.P.L
        ![(D.c (e mu) * b c).left, (D.c (e mu)).left, (b c).left, (η[D.P.A]).left] DegPre.gtε)),
      (∀ mu c, (χt mu c).IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c (e mu)) (toUnit T ≫ b c ^ i) (toUnit T ≫ b c) =
          val (χt mu c) T.hom z J ^ N₁) →
    ∀ (G : X → C → V₁),
      (∀ mu c (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom (G mu c)) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c * D.c (e mu)).left) z J ^ 2 *
            (val (t c) r z J ^ 2 * val (χt mu c) r z J ^ 2 * val D.sym (r ≫ (D.c (e mu)).left) z J *
              (val (τ₀ (e mu) (-e mu)) r z J)⁻¹ * (rigV D r z J ^ 2)⁻¹).val) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) →
    ∃ Λ : K, ∀ mu c, ∃ r ∈ k₀, ev (G mu c) = Λ * r := by
  first | exact @GlobalTheory.USep.EvG.ev_values | exact GlobalTheory.USep.EvG.ev_values | (intros; apply GlobalTheory.USep.EvG.ev_values <;> assumption)
end
