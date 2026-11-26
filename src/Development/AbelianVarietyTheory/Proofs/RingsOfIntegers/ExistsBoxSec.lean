module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxPhi

section Gen

variable {X X' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

def om (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → M.ι)
    (J' : (Z ⟶ X') → M'.ι) (ψ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  bw w ψ z (fun i => J (ψ ≫ pr i)) (J' ψ)

theorem box_sec_val' (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {p : Fin j → (Y' ⟶ Y)} (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (s' : LB.Sec (LB.LinComb M' φ' ε)) (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε))
    (hle : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι) i, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
      p i ⁻¹ᵁ LB.wchart M (φ i) (fun a => jN a i))
    (H : ∀ (jN : K → Fin j → M.ι) (jM : K → M'.ι),
      (@id (Γ(Y', LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
        ((LB.linCombIso w φ' ε).s (jN, jM))).val * rs inf_le_right (s'.f jM) =
        ∏ i, rs (hle jN jM i) (((p i).app _).hom ((s i).f (fun a => jN a i))))
    {Z : Scheme.{0}} (q : Z ⟶ Y') (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, om w y J J' (q ≫ φ' a) ^ ε a).val * sval s' q y J' = ∏ i, sval (s i) (q ≫ p i) y J := by
  have hm : q y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((q ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (q ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((q ≫ φ' a) ≫ pr i), hJ'.mem _ q⟩
  have E := congrArg (gs q y _) (H (fun a i => J ((q ≫ φ' a) ≫ pr i)) (fun a => J' (q ≫ φ' a)))
  refine ((gs_mul q y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit q y _ hm _).trans (congrArg Units.val
    (gm_linCombIso w φ' ε q y _ _ hm))) (gs_res q y _ hm _))).symm.trans (E.trans ((gs_prod q y _ hm _ _).trans
    (Finset.prod_congr rfl fun i _ => ?_)))
  rw [sval_of (s i) _ y J (fun a => J ((q ≫ φ' a) ≫ pr i)) (fun a => by rw [Category.assoc, ← hφ, Category.assoc])]
  exact (gs_res q y (hle _ _ i) hm _).trans (gs_pull q (p i) y _ (hle _ _ i hm) _)

theorem exists_box_sec (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {p : Fin j → (Y' ⟶ Y)} (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (s : ∀ i, LB.Sec (LB.LinComb M (φ i) ε)) : ∃ s' : LB.Sec (LB.LinComb M' φ' ε),
      ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (y : Z) (J) (J'), Good M y J → Good M' y J' →
        (∏ a, om w y J J' (q ≫ φ' a) ^ ε a).val * sval s' q y J' = ∏ i, sval (s i) (q ≫ p i) y J := by
  have hu := linCombIso_isGen w hw φ' ε
  have hA := linComb_isLB M' hM' φ' ε
  have hB := linComb_isLB _ (linComb_isLB M hM pr (fun _ => 1)) φ' ε
  refine ⟨secOfIso (boxSecGen M pr φ' ε p φ hφ s) hu hA hB, fun Z q y J J' hJ hJ' =>
    box_sec_val' w hφ _ s (fun jN jM i => inf_le_left.trans (box_le_of_comp M pr φ' (φ i) (p i) i (hφ i) jN))
      (fun jN jM => ?_) q y hJ hJ'⟩
  have hV : LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM ≤
      LB.wchart M' φ' jM ⊓ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN := fun _ hy => ⟨hy.2, hy.1⟩
  have h₁ := congrArg (rs hV) (secOfIso_spec (boxSecGen M pr φ' ε p φ hφ s) hu hA hB jM jN)
  have h₂ := ((rs_rs _ _ _).symm.trans h₁).trans (isoCand_rs (LB.linCombIso w φ' ε) (boxSecGen M pr φ' ε p φ hφ s) jM jN hV)
  refine (unit_cancel _ _ _ _ h₂ (res_refl' _)).trans ?_
  simp only [boxSecGen, boxSecGenF]
  refine (map_prod ((Y'.presheaf.map (homOfLE _).op).hom) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
  exact rs_rs _ _ _

theorem exists_box_gen (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen)
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')}
    {φ : Fin j → K → (Y ⟶ X)} {ε : K → ℤ} {p : Fin j → (Y' ⟶ Y)} (hφ : ∀ i a, φ' a ≫ pr i = p i ≫ φ i a)
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) : ∃ t' : LB.Gen (LB.LinComb M' φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (y : Z) (J) (J'), Good M y J → Good M' y J' →
        (∏ a, om w y J J' (q ≫ φ' a) ^ ε a) * val t' q y J' = ∏ i, val (t i) (q ≫ p i) y J := by
  obtain ⟨s, hs⟩ := exists_box_sec hM hM' w hw hφ (fun i => Geo.Tor.genSec (t i) (ht i))
  have hs' : ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (y : Z) (J) (J'), Good M y J → Good M' y J' →
      sval s q y J' = ((∏ a, om w y J J' (q ≫ φ' a) ^ ε a)⁻¹ * ∏ i, val (t i) (q ≫ p i) y J).val := by
    intro Z q y J J' hJ hJ'
    rw [Units.val_mul, Units.eq_inv_mul_iff_mul_eq, hs Z q y J J' hJ hJ', Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => sval_genSec _ _ _ _ hJ
  have hu : ∀ jj, IsUnit (s.f jj) := fun jj => Y'.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J', hJ', e⟩ := sval_trans hM' s y jj hy
    choose J hJ using fun χ : Y' ⟶ X => exists_chart hM (χ y)
    rw [hs' _ _ y J J' hJ hJ', ← Units.val_mul] at e
    exact (congrArg IsUnit ((gs_eq (𝟙 Y') y (LB.wchart M' φ' jj) hy _).symm.trans e)).mpr (Units.isUnit _)
  refine ⟨⟨fun jj => (hu jj).unit⟩, fun i j => Units.ext (s.compat i j), fun Z r z J J' hJ hJ' => ?_⟩
  rw [← eq_inv_mul_iff_mul_eq]
  exact Units.ext ((gs_unit r z _ (hJ'.mem φ' r) _).symm.trans (hs' Z r z J J' hJ hJ'))

end Gen

section Main

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem zF_pr (i : Fin j) : DegPre.zF D' F ≫ (TF (R := R) F ◁ pD.pw.pr i) = DegPre.zF D F := by
  have := pD.pw.hom i
  rw [DegPre.zF, DegPre.zF, lift_whiskerLeft, Category.assoc, IsMonHom.one_hom]

theorem trPt_pr (i : Fin j) (b' : TF (R := R) F ⟶ D'.P.A) :
    DegPre.trPt D' F b' ≫ (TF (R := R) F ◁ pD.pw.pr i) =
      (TF (R := R) F ◁ pD.pw.pr i) ≫ DegPre.trPt D F (b' ≫ pD.pw.pr i) := by
  have := pD.pw.hom i
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, tr_fst, Category.assoc, tr_fst, whiskerLeft_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc, tr_pr, Category.assoc, tr_pr, MonObj.comp_mul,
      MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc]

theorem line_pr (i : Fin j) (b' : TF (R := R) F ⟶ D'.P.A) (b : TF (R := R) F ⟶ D.P.A) (hb : b' ≫ pD.pw.pr i = b)
    (a : Fin 2) : DegPre.lineφ D' F b' a ≫ (pD.pw.pr i).left = 𝟙 _ ≫ DegPre.lineφ D F b a := by
  have := pD.pw.hom i
  rw [Category.id_comp]
  fin_cases a
  · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left)
      ((Category.assoc (toUnit _) η[D'.P.A] (pD.pw.pr i)).trans (by rw [IsMonHom.one_hom]))
  · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) hb

variable (D') in
theorem form_zero (k : ℕ) (y α : D'.X) (b : TF (R := R) F ⟶ D'.P.A) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D'.P.A.left) → U) :
    ∏ a, h ((DegPre.zF D' F).left ≫ DegPre.phiφ D' F y α b a) ^ DegPre.deltaε k a =
      (∏ a, h (DegPre.gtφ D' F b α a) ^ DegPre.gtε a) * ∏ a, h (DegPre.lineφ D' F b a) ^ DegPre.lineε k a := by
  have p₃ := prod_fam D' F (DegPre.zF D' F) (α + y) k h
  have p₄ := prod_fam D' F (DegPre.zF D' F ≫ DegPre.trPt D' F b) α k h
  have z₁ : DegPre.zF D' F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D' F ≫ DegPre.prB D' F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D' F ≫ DegPre.trPt D' F b) ≫ DegPre.prB D' F = b := by
    rw [Category.assoc, tr_pr, MonObj.comp_mul, z₂, ← Category.assoc, z₁, Category.id_comp, _root_.one_mul]
  rw [z₂, _root_.mul_one] at p₃
  rw [z₃] at p₄
  simp only [Over.comp_left, Category.assoc] at p₄
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).trans ?_
  rw [Fin.prod_univ_four, Fin.prod_univ_two]
  show _ = h (cP D' _ α * b).left ^ (-1 : ℤ) * h (cP D' _ α).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
      h (1 : TF (R := R) F ⟶ D'.P.A).left ^ (-1 : ℤ) *
      (h (1 : TF (R := R) F ⟶ D'.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)))
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem fam_val {k : ℕ} {S : Fam D' F k} {s : Fin j → Fam D F k} (h : IsBoxFam pD F k S s) (α' : D'.X)
    {Z : Scheme.{0}} (q : Z ⟶ (DegPre.BF D' F).left) (y : Z) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' (q ≫ DegPre.famφ D' F α' a) ^ DegPre.famε k a).val * sval (S.s α') q y J' =
      ∏ i, sval ((s i).s (pD.xe α' i)) (q ≫ prB pD F i) y J := by
  obtain ⟨hφ, H⟩ := h α'
  exact box_sec_val' pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H q y hJ hJ'

end Main

theorem alg_fin {A : Type} [CommRing A] {a b c : Aˣ} {x y : A} (h : a.val * x = (b.val * y) * (a * b⁻¹ * c).val) :
    x = y * c.val := by
  refine (Units.mul_right_inj a).1 (h.trans ?_)
  rw [Units.val_mul, Units.val_mul]
  linear_combination (a.val * y * c.val) * b.mul_inv

theorem phiRel_box : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (p' : QkPt D' F k) (p : Fin j → QkPt D F k), IsBoxQk pD F k p' p → ∀ w : ∀ i, LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F (p i).g.b) (DegPre.lineε k)), (∀ i, (w i).IsGen) → ∃ w' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p'.g.b) (DegPre.lineε k)), w'.IsGen ∧ ∀ (s s₁ : Fin j → Fam D F k) (S S₁ : Fam D' F k), (∀ i, PhiRel D F k (p i) (w i) (s i) (s₁ i)) → IsBoxFam pD F k S s → IsBoxFam pD F k S₁ s₁ → PhiRel D' F k p' w' S S₁ := by
  intro hG R _ _ j D D' pD F _ _ k p' p hp w hw
  obtain ⟨hy, hb, hg⟩ := hp
  obtain ⟨w', hw', vw⟩ := exists_box_gen D.P.isLB D'.P.isLB pD.w pD.w_gen
    (fun i => line_pr pD i p'.g.b (p i).g.b (hb i)) w hw
  refine ⟨w', hw', fun s s₁ S S₁ hs hS hS₁ α' u' hu' hc' => ?_⟩
  choose u hu hc using fun i => (gen_phi hG (p i) (w i) (hw i) (pD.xe α' i)).1
  have hx : ∀ i, pD.xe (α' + p'.y) i = pD.xe α' i + (p i).y := fun i => by rw [map_add (f := _), hy]; rfl
  have ht : ∀ i, (DegPre.trPt D' F p'.g.b).left ≫ prB pD F i = prB pD F i ≫ (DegPre.trPt D F (p i).g.b).left := fun i => by
    have := congrArg (fun q => q.left) (trPt_pr pD i p'.g.b)
    rw [hb i] at this
    exact this
  have hφ : ∀ i a, DegPre.phiφ D' F p'.y α' p'.g.b a ≫ (pD.pw.pr i).left =
      prB pD F i ≫ DegPre.phiφ D F (p i).y (pD.xe α' i) (p i).g.b a := by
    rintro i (a | a)
    · exact ((hS (α' + p'.y)).choose i a).trans (by rw [hx]; rfl)
    · show ((DegPre.trPt D' F p'.g.b).left ≫ DegPre.famφ D' F α' a) ≫ _ =
        _ ≫ (DegPre.trPt D F (p i).g.b).left ≫ DegPre.famφ D F (pD.xe α' i) a
      rw [Category.assoc, (hS α').choose i a, ← Category.assoc, ht, Category.assoc]
  obtain ⟨v, hv, vv⟩ := exists_box_gen D.P.isLB D'.P.isLB pD.w pD.w_gen hφ u hu
  have z₁ : DegPre.zF D' F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have huv := gen_unique D'.P.isLB (fst (TF (R := R) F) D'.P.A).left (DegPre.zF D' F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D' F hG) hu' hv (fun y J' hJ' => by
      choose J hJ using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
      have hJ : Good D.P.L y J := hJ
      have e₁ := val_corr hJ' hc' (𝟙 _)
      rw [val_pull hJ', Category.id_comp, val_mul hJ'] at e₁
      have e₂ := vv _ (DegPre.zF D' F).left y J J' hJ hJ'
      have e₃ := vw _ (𝟙 _) y J J' hJ hJ'
      obtain ⟨hψ, H⟩ := hg α'
      have e₄ : (∏ a, om pD.w y J J' (DegPre.gtφ D' F p'.g.b α' a) ^ DegPre.gtε a) * val (p'.g.s α') (𝟙 _) y J' =
          ∏ i, val ((p i).g.s (pD.xe α' i)) (𝟙 _) y J :=
        box_gen_val pD.w hψ _ (fun i => (p i).g.s (pD.xe α' i)) H y hJ hJ'
      have e₅ : ∀ i, val (u i) ((DegPre.zF D' F).left ≫ prB pD F i) y J =
          val ((p i).g.s (pD.xe α' i)) (𝟙 _) y J * val (w i) (𝟙 _) y J := fun i => by
        have := val_corr hJ (hc i) (𝟙 _)
        rw [val_pull hJ, Category.id_comp, val_mul hJ] at this
        have z : (DegPre.zF D' F).left ≫ prB pD F i = (DegPre.zF D F).left := congrArg (fun q => q.left) (zF_pr (F := F) pD i)
        rw [z]
        exact this
      simp only [Category.id_comp] at e₃
      rw [form_zero, Finset.prod_congr rfl (fun i _ => e₅ i), Finset.prod_mul_distrib, ← e₄, ← e₃,
        _root_.mul_mul_mul_comm, ← e₁] at e₂
      exact (mul_left_cancel e₂).symm)
  refine (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').2 fun y J' hJ' => ?_
  choose J hJ using fun χ : (DegPre.BF D' F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ
  have e₁ := fam_val pD hS₁ (α' + p'.y) (𝟙 _) y hJ hJ'
  have e₂ := fam_val pD hS α' (𝟙 _ ≫ (DegPre.trPt D' F p'.g.b).left) y hJ hJ'
  have e₃ := vv _ (𝟙 _) y J J' hJ hJ'
  have e₄ : ∀ i, sval ((s₁ i).s (pD.xe (α' + p'.y) i)) (𝟙 _ ≫ prB pD F i) y J =
      sval ((s i).s (pD.xe α' i)) ((𝟙 _ ≫ (DegPre.trPt D' F p'.g.b).left) ≫ prB pD F i) y J *
        (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
    rw [hx, Category.assoc, ht, ← Category.assoc]
    exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 (hs i _ (u i) (hu i) (hc i)) _ _ y J hJ
  have e₅ : ∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.phiφ D' F p'.y α' p'.g.b a) ^ DegPre.deltaε k a =
      (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F (α' + p'.y) a) ^ DegPre.famε k a) *
      (∏ a, om pD.w y J J' ((𝟙 _ ≫ (DegPre.trPt D' F p'.g.b).left) ≫ DegPre.famφ D' F α' a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  rw [Finset.prod_congr rfl (fun i _ => e₄ i), Finset.prod_mul_distrib, ← e₂, ← Units.coe_prod, ← e₃, e₅,
    ← huv _ _ y J' hJ'] at e₁
  exact alg_fin e₁

end GlobalTheory.BoxPhi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtOfSucc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)


omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in
theorem thickMap_comp_fGl (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ fGl I G (e + 1) = fGl I G e := by
  unfold thickMap fGl fstG
  simp only [Over.homMk_left, pullback.map, pullback.lift_fst, Category.comp_id]

private lemma mem_pull_U_of_mem_U {X Y : Scheme.{0}} {M : LB X} (f : Y ⟶ X) (j : PUnit → M.ι) (y : Y)
    (h : f y ∈ M.U (j ⟨⟩)) : y ∈ (M.pull f).U j := by
  unfold LB.pull LB.LinComb
  simp only [LB.wchart]
  simpa using fun i : PUnit => (show i = ⟨⟩ from rfl) ▸ h

private lemma gm_res_eq_gm {Z : Scheme.{0}} (z : Z) {V W : Z.Opens} (h : V ≤ W) (hz : z ∈ V) (x : Γ(Z, W)ˣ) :
    gm (𝟙 Z) z V (res h x) = gm (𝟙 Z) z W x := by
  rw [← gm_rp₁ (𝟙 Z) z W V h hz x]
  unfold pullU
  congr 2

theorem wv_thickMap (e : ℕ) (y : (thickObj R I e G).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : pGl U e y ∈ D.toPre.P.L.U jM) (hL : fGl I G e y ∈ U.LG.L.U jL) :
    wv U (e + 1) (thickMap R I e G) y jM jL = wv U e (𝟙 _) y jM jL := by
  have hq := U.gt_q e
  have hf := thickMap_comp_fGl I e G
  have h3 : (pGl U (e + 1)) ((thickMap R I e G) y) = (pGl U e) y := congrArg (fun g => g.base y) hq
  have h4 : (fGl I G (e + 1)) ((thickMap R I e G) y) = (fGl I G e) y := congrArg (fun g => g.base y) hf
  have hy : y ∈ ((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL :=
    ⟨mem_pull_U_of_mem_U _ _ _ hM, mem_pull_U_of_mem_U _ _ _ hL⟩
  have hy' : y ∈ thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) :=
    ⟨mem_pull_U_of_mem_U _ _ _ (h3 ▸ hM), mem_pull_U_of_mem_U _ _ _ (h4 ▸ hL)⟩
  have hle : thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) ≤
      thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL) := inf_le_left
  have hV : y ∈ (thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL)) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) := ⟨hy', hy⟩
  unfold wv
  refine (gm_rp₁ (thickMap R I e G) y _ _ hle hV ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))).symm.trans ?_
  exact (congrArg (gm (𝟙 _) y _) (U.w_compat e (fun _ => jM, fun _ => jL) _ hle inf_le_right)).trans
    (gm_res_eq_gm y (inf_le_right : (thickMap R I e G ⁻¹ᵁ (((D.toPre.P.L.pull (pGl U (e + 1))).U fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G (e + 1))).U fun _ => jL)) ⊓
      (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL) ≤ (((D.toPre.P.L.pull (pGl U e)).U fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U fun _ => jL)) hV _)

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemBasicOpenIffGs
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.SectionRatio

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem mem_basicOpen_iff_gs {Y : Scheme.{0}} {U : Y.Opens} (f : Γ(Y, U)) (y : Y) (hy : y ∈ U) :
    y ∈ Y.basicOpen f ↔ IsUnit (gs (𝟙 Y) y U f) := by
  rw [gs_eq (𝟙 Y) y U hy f, Scheme.mem_basicOpen Y f y hy]
  exact Iff.rfl

theorem exists_quot {Y : Scheme.{0}} {U : Y.Opens} (a b : Γ(Y, U)) :
    ∃ q : Γ(Y, Y.basicOpen b), ∀ y ∈ Y.basicOpen b,
      gs (𝟙 Y) y _ q * gs (𝟙 Y) y U b = gs (𝟙 Y) y U a := by
  have hD : Y.basicOpen b ≤ U := Y.basicOpen_le b
  have hu : IsUnit ((Y.presheaf.map (homOfLE hD).op).hom b) := Y.toRingedSpace.isUnit_res_basicOpen b
  obtain ⟨w, hw⟩ := hu
  refine ⟨(Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹, fun y hy => ?_⟩
  have key : ((Y.presheaf.map (homOfLE hD).op).hom a * ↑w⁻¹) * (Y.presheaf.map (homOfLE hD).op).hom b =
      (Y.presheaf.map (homOfLE hD).op).hom a := by
    have hw' : (Y.presheaf.map (homOfLE hD).op).hom b = ↑w := hw.symm
    rw [hw', _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [← gs_res (𝟙 Y) y hD hy b, ← gs_mul (𝟙 Y) y _ hy, key, gs_res (𝟙 Y) y hD hy a]

private theorem exists_global_unit_of_compatible_of_iSup_eq {Y : Scheme.{0}} {P : Type} (W : P → Y.Opens) (hW : ∀ y, ∃ p, y ∈ W p)
    (q : ∀ p, Γ(Y, W p))
    (hq : ∀ p p' (y : Y), y ∈ W p → y ∈ W p' → gs (𝟙 Y) y (W p) (q p) = gs (𝟙 Y) y (W p') (q p')) :
    ∃ c : Γ(Y, ⊤), ∀ p (y : Y), y ∈ W p → gs (𝟙 Y) y ⊤ c = gs (𝟙 Y) y (W p) (q p) := by
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ => by
    obtain ⟨p, hp⟩ := hW y
    exact Opens.mem_iSup.2 ⟨p, hp⟩
  have hcomp : TopCat.Presheaf.IsCompatible Y.sheaf.1 W q := by
    intro p p'
    apply fn_ext
    intro y hy
    exact (gs_res (𝟙 Y) y inf_le_left hy (q p)).trans
      ((hq p p' y hy.1 hy.2).trans (gs_res (𝟙 Y) y inf_le_right hy (q p')).symm)
  obtain ⟨c, hc, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf W ⊤ (fun p => homOfLE le_top) hcov q hcomp
  refine ⟨c, fun p y hy => ?_⟩
  rw [← hc p]
  exact (gs_res (𝟙 Y) y le_top hy c).symm

private theorem gs_id_linComb_eq_trF_mul_sval {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (j : K → L.ι) (y : Y) (hy : y ∈ (LB.LinComb L φ ε).U j)
    (J : (Y ⟶ X) → L.ι) (hJ : Good L y J) :
    gs (𝟙 Y) y ((LB.LinComb L φ ε).U j) (s.f j) =
      (trF φ ε (𝟙 Y) y j (fun k => J (𝟙 Y ≫ φ k))).val * sval s (𝟙 Y) y J :=
  sec_trans s (𝟙 Y) y hy (hJ.mem φ (𝟙 Y))

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {Ix : Type} (a b : Ix → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ (y : Y) (J), Good L y J → ∃ i, IsUnit (sval (b i) (𝟙 Y) y J))
    (hab : ∀ i i' (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J * sval (b i') (𝟙 Y) y J = sval (a i') (𝟙 Y) y J * sval (b i) (𝟙 Y) y J) :
    ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Good L y J →
      sval (a i) (𝟙 Y) y J = gs (𝟙 Y) y ⊤ c * sval (b i) (𝟙 Y) y J := by

  let W : Ix × (K → L.ι) → Y.Opens := fun p => Y.basicOpen ((b p.1).f p.2)
  choose q hq using fun p : Ix × (K → L.ι) => exists_quot ((a p.1).f p.2) ((b p.1).f p.2)
  have goodAt : ∀ y : Y, ∃ J, Good L y J := fun y => by
    obtain ⟨J, hJ, -⟩ := exists_good L hL y (K := Empty) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim)
    exact ⟨J, hJ⟩

  have loc : ∀ p (y : Y), y ∈ W p → ∀ J, Good L y J →
      gs (𝟙 Y) y (W p) (q p) * sval (b p.1) (𝟙 Y) y J = sval (a p.1) (𝟙 Y) y J ∧
        IsUnit (sval (b p.1) (𝟙 Y) y J) := by
    intro p y hy J hJ
    have hyc : y ∈ (LB.LinComb L φ ε).U p.2 := Y.basicOpen_le _ hy
    have e := hq p y hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ, gs_id_linComb_eq_trF_mul_sval (a p.1) p.2 y hyc J hJ] at e
    have hu := (mem_basicOpen_iff_gs ((b p.1).f p.2) y hyc).1 hy
    rw [gs_id_linComb_eq_trF_mul_sval (b p.1) p.2 y hyc J hJ] at hu
    set T := trF φ ε (𝟙 Y) y p.2 (fun k => J (𝟙 Y ≫ φ k))
    refine ⟨?_, isUnit_of_mul_isUnit_right hu⟩
    apply T.isUnit.mul_left_cancel
    linear_combination e
  obtain ⟨c, hc⟩ := exists_global_unit_of_compatible_of_iSup_eq W (fun y => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨i, hi⟩ := hb y J hJ
      exact ⟨(i, fun k => J (𝟙 Y ≫ φ k)),
        (mem_basicOpen_iff_gs ((b i).f _) y (hJ.mem φ (𝟙 Y))).2 hi⟩) q
    (fun p p' y hy hy' => by
      obtain ⟨J, hJ⟩ := goodAt y
      obtain ⟨e1, u1⟩ := loc p y hy J hJ
      obtain ⟨e2, u2⟩ := loc p' y hy' J hJ
      have e3 := hab p.1 p'.1 y J hJ
      apply (u1.mul u2).mul_right_cancel
      linear_combination sval (b p'.1) (𝟙 Y) y J * e1 + e3 - sval (b p.1) (𝟙 Y) y J * e2)
  refine ⟨c, fun i y J hJ => ?_⟩
  obtain ⟨i₀, h₀⟩ := hb y J hJ
  have hy₀ : y ∈ W (i₀, fun k => J (𝟙 Y ≫ φ k)) :=
    (mem_basicOpen_iff_gs ((b i₀).f _) y (hJ.mem φ (𝟙 Y))).2 h₀
  obtain ⟨e1, -⟩ := loc _ y hy₀ J hJ
  rw [hc _ y hy₀]
  apply h₀.mul_right_cancel
  linear_combination hab i i₀ y J hJ - sval (b i) (𝟙 Y) y J * e1

theorem ratio_glue : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ K₃ : Type) [Fintype K₁] [Fintype K₂] [Fintype K₃] (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (φ₃ : K₃ → (Y ⟶ X)) (ε₃ : K₃ → ℤ) (h : Y ⟶ Y), Geo.Tor.FormEq φ₁ ε₁ (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) → ∀ (u : LB.Gen (LB.LinComb L φ₃ ε₃)), u.IsGen → ∀ (Ix : Type) (s'' : Ix → LB.Sec (LB.LinComb L φ₁ ε₁)) (s : Ix → LB.Sec (LB.LinComb L φ₂ ε₂)), (∀ (y : Y) (J), Geo.Tor.Good L y J → ∃ i, IsUnit (Geo.Tor.sval (s i) h y J)) → (∀ i i' (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J * Geo.Tor.sval (s i') h y J = Geo.Tor.sval (s'' i') (𝟙 Y) y J * Geo.Tor.sval (s i) h y J) → ∃ c : Γ(Y, ⊤), ∀ i (y : Y) (J), Geo.Tor.Good L y J → Geo.Tor.sval (s'' i) (𝟙 Y) y J = Geo.Tor.gs (𝟙 Y) y ⊤ c * (Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val) := by
  intro X Y L hL K₁ K₂ K₃ _ _ _ φ₁ ε₁ φ₂ ε₂ φ₃ ε₃ h hF u hu Ix s'' s hs hx
  have hF' : Geo.Tor.FormEq (Sum.elim (fun k => h ≫ φ₂ k) φ₃) (Sum.elim ε₂ ε₃) φ₁ ε₁ :=
    fun U _ g => (hF U g).symm
  choose b hb using fun i => Geo.Tor.exists_sec hL hF' (Geo.Tor.pullMulSec (s i) h u hu)
  have key : ∀ i (y : Y) (J), Geo.Tor.Good L y J →
      Geo.Tor.sval (b i) (𝟙 Y) y J = Geo.Tor.sval (s i) h y J * (Geo.Tor.val u (𝟙 Y) y J).val := by
    intro i y J hJ
    rw [hb i Y (𝟙 Y) y J hJ, Geo.Tor.sval_pullMulSec (s i) h u hu (𝟙 Y) y hJ, Category.id_comp]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SectionRatio.exists_ratio hL s'' b
    (fun y J hJ => by
      obtain ⟨i, hi⟩ := hs y J hJ
      exact ⟨i, by rw [key i y J hJ]; exact hi.mul (Geo.Tor.val u (𝟙 Y) y J).isUnit⟩)
    (fun i i' y J hJ => by
      rw [key i y J hJ, key i' y J hJ]
      linear_combination (Geo.Tor.val u (𝟙 Y) y J).val * hx i i' y J hJ)
  refine ⟨c, fun i y J hJ => ?_⟩
  rw [hc i y J hJ, key i y J hJ]

end GlobalTheory.SectionRatio
end
