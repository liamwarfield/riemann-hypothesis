module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayProjectiveFormsThroughPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsProjCoordRepresentationHomogeneousIdealFla
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoOfProjectiveCoordinateRepresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActCommOfClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g k : ℕ} {J : Type}
  {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {o : Type} [CommRing o] {b : TBase o k} {S S' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

def Under (t : SAB H S) (lv : D.La → (𝟙_ (Over S) ⟶ t.G)) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (T : TObj g k J b s) : Prop :=
  ∃ φ : t.G ≅ T.A, IsMonHom φ.hom ∧ LBIso t.PP.L (T.L.pull φ.hom.left) ∧
    (∀ j, t.act.act (a j) ≫ φ.hom = φ.hom ≫ T.act j) ∧
    ∀ i, (lv (bas (Pi.single i 1))).left ≫ φ.hom.left = (T.pt i).left

theorem lbIso_of_sabMap {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem inv_hom_left {A B : Over S} (φ : A ≅ B) : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]

theorem hom_inv_left {A B : Over S} (φ : A ≅ B) : φ.hom.left ≫ φ.inv.left = 𝟙 _ := inv_hom_left φ.symm

theorem lbIso_inv {A B : Over S} (φ : A ≅ B) {L : LB A.left} {M : LB B.left}
    (h : LBIso L (M.pull φ.hom.left)) : LBIso M (L.pull φ.inv.left) :=
  (LBIso.chartPull (chartPullId _) (chartPullUnpull M (𝟙 _) rfl)
    (PELPull.lbIso_pull h φ.inv.left (inv_hom_left φ).symm)).symm

theorem tmap_of_sabMap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') {f : S' ⟶ S} (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    TMap T' T f := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  have : IsMonHom ψ.symm.hom := inferInstanceAs (IsMonHom ψ.inv)
  refine ⟨ψ.inv.left ≫ m.φ ≫ φ.hom.left, ?_, ?_, fun i => ?_, fun j => ?_⟩
  · exact ((isGrpPullback_of_iso ψ.symm).comp (m.cart.comp (isGrpPullback_of_iso φ))).congr (by simp) rfl
  · refine (lbIso_inv ψ hψL).trans T'.isLB (pull_isLB t'.PP.isLB _) (pull_isLB T.isLB _) (PELPull.lbIso_pull ?_ _ rfl)
    exact (lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)
  · rw [← hψp, ← hφp, Category.assoc, reassoc_of% hom_inv_left ψ, reassoc_of% hl]
  · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left := congrArg (fun z => z.left) (hφa j)
    have h₂ : (T'.act j).left ≫ ψ.inv.left = ψ.inv.left ≫ (t'.act.act (a j)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      rw [Iso.comp_inv_eq, Category.assoc, hψa, Iso.inv_hom_id_assoc]
    have h₃ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
    rw [reassoc_of% h₂, reassoc_of% h₃, h₁, Category.assoc, Category.assoc]

theorem under_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    {f : S' ⟶ S} (h' : TMap T' T f) (m : SABMap t' t f) (hl : ∀ x, (lv' x).left ≫ m.φ = f ≫ (lv x).left) :
    Under t' lv' a bas T' := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hpt, hact⟩ := h'
  have hc : IsGrpPullback t'.G T.A f (m.φ ≫ φ.hom.left) :=
    (IsGrpPullback.comp m.cart (isGrpPullback_of_iso φ)).congr (Category.comp_id f) rfl
  obtain ⟨e, he, heF⟩ := grpPullback_iso hc hψ
  refine ⟨e, he, ?_, fun j => ?_, fun i => ?_⟩
  · exact ((lbIso_of_sabMap m).trans t'.PP.isLB (pull_isLB t.PP.isLB _) (pull_isLB T.isLB _)
      (PELPull.lbIso_pull hφL m.φ rfl)).trans
      t'.PP.isLB (pull_isLB T.isLB _) (pull_isLB T'.isLB _) (PELPull.lbIso_pull hψL e.hom.left heF.symm).symm
  · apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · have h₁ : (t.act.act (a j)).left ≫ φ.hom.left = φ.hom.left ≫ (T.act j).left :=
        congrArg (fun z => z.left) (hφa j)
      have h₂ : (t'.act.act (a j)).left ≫ m.φ = m.φ ≫ (t.act.act (a j)).left := m.act _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, heF, hact, ← Category.assoc, h₂,
        Category.assoc, h₁, ← Category.assoc, ← heF, Category.assoc]
    · rw [Over.w, Over.w]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, heF, reassoc_of% hl, hφp, hpt]
    · rw [Category.assoc, Over.w, Over.w, Over.w]; rfl

theorem act_zero {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) : act.act 0 = 1 := by
  have := act.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem act_neg {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (c : O) :
    act.act (-c) = (act.act c)⁻¹ := by
  have := act.add (-c) c
  rw [neg_add_cancel, act_zero] at this
  exact eq_inv_of_mul_eq_one_left this.symm

theorem act_comm_of_closure {O : Type} [CommRing O] {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] (act : OAct O G)
    (act' : OAct O G') {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {a : J → O}
    (ha : Subring.closure (Set.range a) = ⊤) (hj : ∀ j, (act'.act (a j)).left ≫ φ = φ ≫ (act.act (a j)).left) (c : O) :
    (act'.act c).left ≫ φ = φ ≫ (act.act c).left := by
  let u : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have key : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left ↔ pushHom h G' (act'.act c) = preHom u (act.act c) :=
    fun c => ⟨fun e => Over.OverMorphism.ext e, fun e => congrArg (fun z => z.left) e⟩
  have hc : c ∈ Subring.closure (Set.range a) := ha ▸ Subring.mem_top c
  induction hc using Subring.closure_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hj j
  | zero => rw [key, act_zero, act_zero, map_one, map_one]
  | one => rw [act.one, act'.one, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
  | add x y _ _ hx hy => rw [key] at hx hy ⊢; rw [act.add, act'.add, map_mul, map_mul, hx, hy]
  | neg x _ hx => rw [key] at hx ⊢; rw [act_neg, act_neg, map_inv, map_inv, hx]
  | mul x y _ _ hx hy => rw [act.mul, act'.mul, Over.comp_left, Over.comp_left, Category.assoc, hy, reassoc_of% hx]

theorem eq_of_basis {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u v : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (hv : ∀ x y, v (x + y) = v x * v y)
    (h : ∀ i, u (bas (Pi.single i 1)) = v (bas (Pi.single i 1))) (x : D.La) : u x = v x := by
  let u' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (u x)) fun x y => by rw [hu]; rfl
  let v' : D.La →+ Additive A := AddMonoidHom.mk' (fun x => Additive.ofMul (v x)) fun x y => by rw [hv]; rfl
  have : u'.comp bas.toLinearMap.toAddMonoidHom = v'.comp bas.toLinearMap.toAddMonoidHom := by
    refine AddMonoidHom.functions_ext' _ _ _ fun i => AddMonoidHom.ext_int ?_
    exact congrArg Additive.ofMul (h i)
  have e := DFunLike.congr_fun this (bas.symm x)
  simpa [u', v'] using e

theorem sabMap_of_tmap {t : SAB H S} {t' : SAB H S'} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)}
    {lv' : D.La → (𝟙_ (Over S') ⟶ t'.G)} {T : TObj g k J b s} {T' : TObj g k J b s'} (h : Under t lv a bas T)
    (h' : Under t' lv' a bas T') (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hlv' : ∀ x y, lv' (x + y) = lv' x * lv' y)
    (ha : Subring.closure (Set.range a) = ⊤) (hS : IsReduced S') (hp : IsProper t'.G.hom) {f : S' ⟶ S}
    (m : TMap T' T f) : ∃ ν : SABMap t' t f, ∀ x, (lv' x).left ≫ ν.φ = f ≫ (lv x).left := by
  obtain ⟨φ, hφ, hφL, hφa, hφp⟩ := h
  obtain ⟨ψ, hψ, hψL, hψa, hψp⟩ := h'
  obtain ⟨χ, hχ, hχL, hpt, hact⟩ := m
  have : IsMonHom φ.symm.hom := inferInstanceAs (IsMonHom φ.inv)
  have hc : IsGrpPullback t'.G t.G f (ψ.hom.left ≫ χ ≫ φ.inv.left) :=
    ((isGrpPullback_of_iso ψ).comp (hχ.comp (isGrpPullback_of_iso φ.symm))).congr (by simp) rfl
  obtain ⟨ν, hν⟩ := exists_sabMap_of_lbIso E H S S' t t' f _ ⟨hS, fun _ _ _ _ _ _ _ => inferInstance⟩ hc
    (act_comm_of_closure t.act t'.act hc ha fun j => by
      have h₁ : (t'.act.act (a j)).left ≫ ψ.hom.left = ψ.hom.left ≫ (T'.act j).left :=
        congrArg (fun z => z.left) (hψa j)
      have h₂ : (T.act j).left ≫ φ.inv.left = φ.inv.left ≫ (t.act.act (a j)).left := by
        rw [← Over.comp_left, ← Over.comp_left]
        congr 1
        rw [Iso.comp_inv_eq, Category.assoc, hφa, Iso.inv_hom_id_assoc]
      rw [reassoc_of% h₁, reassoc_of% hact, h₂, Category.assoc, Category.assoc])
    (hψL.trans t'.PP.isLB (pull_isLB T'.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull
      (hχL.trans T'.isLB (pull_isLB T.isLB _) (pull_isLB t.PP.isLB _) (PELPull.lbIso_pull (lbIso_inv φ hφL) χ rfl)) _ rfl))
  refine ⟨ν, fun x => ?_⟩
  have e := eq_of_basis bas lv' (fun x => ObjPull.secPull hc (lv x)) hlv' (fun x y => by rw [hlv, map_mul])
    (fun i => Over.OverMorphism.ext (hc.1.hom_ext (by
      rw [ObjPull.secPull_left, reassoc_of% hψp, reassoc_of% hpt, ← hφp, Category.assoc, hom_inv_left,
        Category.comp_id]) (by rw [Over.w, Over.w]))) x
  rw [hν, e, ObjPull.secPull_left]

end GlobalTheory.TripleTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquare
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SecMove

section General

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem gs_comp {Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [gs_eq (r ≫ g) z U h, gs_eq g (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r (g ⁻¹ᵁ U) z h _).symm

theorem exists_up_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (ε : K → ℤ) (g : Y ⟶ Y') (a : LB.Sec (LB.LinComb L' φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L (fun k => (g ≫ φ' k) ≫ F) ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p → r z ∈ LB.wchart L' (fun k => g ≫ φ' k) q →
        gs r z (LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p) (s.f p) =
          (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) := by
  choose u hu using fun p q => exists_pw w (fun k => g ≫ φ' k) ε p q
  have tr : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (q q' : K → L'.ι),
      trF φ' ε (r ≫ g) z q q' = trF (fun k => g ≫ φ' k) ε r z q q' := fun r z q q' => by
    simp only [trF, Category.assoc]
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p → r z ∈ LB.wchart L' (fun k => g ≫ φ' k) q →
      gs r z _ s = (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q =>
      LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p ⊓ LB.wchart L' (fun k => g ≫ φ' k) q
    have le : ∀ q, W q ≤ g ⁻¹ᵁ LB.wchart L' φ' q := fun q y hy =>
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w (fun k => g ≫ φ' k) ε r z p q).val * gs (r ≫ g) z (LB.wchart L' φ' q) (a.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (le q)).op).hom ((g.app _).hom (a.f q)),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz)))
          ((gs_res r z (le q) hz _).trans (gs_pull r g z _ (le q hz) _)))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => (g ≫ φ' k) ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' ((g ≫ φ' k) y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, sec_trans a (𝟙 Y ≫ g) y (le q hy.1) (le q' hy.2), tr,
          pw_trans hw _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2, trF_self hL _ ε (𝟙 Y) y hy.1.1, _root_.one_mul,
          ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_comm])
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W q)) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' ((g ≫ φ' k) y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun k => g ≫ φ' k) q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw _ ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, _root_.mul_one, Units.val_mul,
    _root_.mul_assoc]
  rfl

def Rel (w : LB.Iso L' (L.pull F)) (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)
    (a : LB.Sec (LB.LinComb L' φ' ε)) (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q)

theorem exists_equiv (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) [IsIso h] (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) :
    ∃ e : LB.Sec (LB.LinComb L' φ' ε) ≃ LB.Sec (LB.LinComb L φ ε), ∀ a, Rel w φ' φ ε h a (e a) := by
  have H := fun s => GlobalTheory.SecPull.existsUnique_secPull X X' Y Y' L L' F hL hL' w hw K φ' φ ε h hc s
  choose d hd hd' using H
  obtain rfl : φ = fun k => (inv h ≫ φ' k) ≫ F := funext fun k => by
    rw [Category.assoc, hc, IsIso.inv_hom_id_assoc]
  have inj : Function.Injective d := fun s s' e => by
    have e : s.f = s'.f := funext fun p => fn_ext fun y hy => by
      choose q hq using fun k => exists_chart hL' (φ' k (inv h y))
      have h₁ := hd s _ (inv h) y p q (Set.mem_iInter.1 hy) hq
      have h₂ := hd s' _ (inv h) y p q (Set.mem_iInter.1 hy) hq
      rw [IsIso.inv_hom_id] at h₁ h₂
      rw [e] at h₁
      exact h₁.trans h₂.symm
    cases s; cases s'; cases e; rfl
  have surj : Function.Surjective d := fun a => by
    obtain ⟨s, hs⟩ := exists_up_sec ((isGen_iff w).1 hw) hL hL' φ' ε (inv h) a
    refine ⟨s, (hd' s a fun Z r z p q hp hq => ?_).symm⟩
    have e : ∀ k, (r ≫ h) ≫ inv h ≫ φ' k = r ≫ φ' k := fun k => by simp
    rw [hs Z (r ≫ h) z p q (Set.mem_iInter.2 fun k => by
        show F (((r ≫ h) ≫ inv h ≫ φ' k) z) ∈ L.U (p k)
        rw [e]; exact hp k) (Set.mem_iInter.2 fun k => by
        show ((r ≫ h) ≫ inv h ≫ φ' k) z ∈ L'.U (q k)
        rw [e]; exact hq k), Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp only [pw, e]
  refine ⟨(Equiv.ofBijective d ⟨inj, surj⟩).symm, fun a => ?_⟩
  have := hd ((Equiv.ofBijective d ⟨inj, surj⟩).symm a)
  rw [show d ((Equiv.ofBijective d ⟨inj, surj⟩).symm a) = a from (Equiv.ofBijective d ⟨inj, surj⟩).apply_symm_apply a]
    at this
  exact this

def LinAt {Y₁ Y₂ T Z : Scheme.{0}} (L : LB X) (N : ℤ) (σ₁ : Y₁ ⟶ X) (σ₂ : Y₂ ⟶ X) (m : Y₂ ⟶ Y₁) (π : Y₂ ⟶ T) {n : ℕ}
    (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))) (c : Fin n → Γ(T, ⊤))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))) (r : Z ⟶ Y₂) (z : Z) (p : L.ι) : Prop :=
  gs r z (LB.wchart L (fun _ : Fin 1 => σ₂) (fun _ => p)) (s.f (fun _ => p)) =
    ∑ i, gs (r ≫ π) z ⊤ (c i) * gs (r ≫ m) z (LB.wchart L (fun _ : Fin 1 => σ₁) (fun _ => p)) ((b i).f (fun _ => p))

theorem val_iff {Y₁ Y₂ T : Scheme.{0}} (hL : L.IsLB) (N : ℤ) (σ₁ : Y₁ ⟶ X) (σ₂ : Y₂ ⟶ X) (m : Y₂ ⟶ Y₁) (π : Y₂ ⟶ T)
    (hm : m ≫ σ₁ = σ₂) {n : ℕ}
    (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))) (c : Fin n → Γ(T, ⊤))
    (s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))) :
    (∀ (z : Y₂) (J), Good L z J → sval s (𝟙 _) z J = ∑ i, gs π z ⊤ (c i) * sval (b i) m z J) ↔
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₂) (z : Z) (p : L.ι), σ₂ (r z) ∈ L.U p → LinAt L N σ₁ σ₂ m π b c s r z p := by
  constructor
  · intro H Z r z p hp
    obtain ⟨J, hJ, e⟩ := exists_good L hL (r z) (fun _ : Fin 1 => σ₂) (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
    have := congrArg (r.stalkMap z).hom (H (r z) J hJ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sval_of s _ _ J (fun _ => p) (fun k => by rw [Category.id_comp]; exact e k), map_sum] at this
    have e₀ := gs_comp r (𝟙 Y₂) z (LB.wchart L (fun _ : Fin 1 => σ₂) (fun _ => p)) (Set.mem_iInter.2 fun _ => hp)
      (s.f fun _ => p)
    rw [Category.comp_id] at e₀
    refine e₀.trans (this.trans (Finset.sum_congr rfl fun i _ => ?_))
    rw [map_mul, sval_of (b i) _ _ J (fun _ => p) (fun k => by rw [hm]; exact e k)]
    exact congrArg₂ (· * ·) (gs_comp r π z ⊤ trivial _).symm
      (gs_comp r m z (LB.wchart L (fun _ : Fin 1 => σ₁) (fun _ => p)) (Set.mem_iInter.2 fun _ => by
        show (m ≫ σ₁) (r z) ∈ L.U p
        rw [hm]; exact hp) _).symm
  · intro H z J hJ
    have := H _ (𝟙 _) z (J σ₂) (hJ σ₂)
    rw [LinAt, Category.id_comp, Category.id_comp] at this
    rw [sval_of s _ _ J (fun _ => J σ₂) (fun k => by rw [Category.id_comp])]
    refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [sval_of (b i) _ _ J (fun _ => J σ₂) (fun k => by rw [hm])]

theorem linAt_iff {Y₁ Y₂ T Y₁' Y₂' T' Z : Scheme.{0}} (w : LB.Iso L' (L.pull F)) (N : ℤ)
    {σ₁ : Y₁ ⟶ X} {σ₂ : Y₂ ⟶ X} {m : Y₂ ⟶ Y₁} {π : Y₂ ⟶ T}
    {σ₁' : Y₁' ⟶ X'} {σ₂' : Y₂' ⟶ X'} {m' : Y₂' ⟶ Y₁'} {π' : Y₂' ⟶ T'}
    {h₁ : Y₁' ⟶ Y₁} {h₂ : Y₂' ⟶ Y₂} {u : T' ⟶ T} (hm' : m' ≫ σ₁' = σ₂') (hh : m' ≫ h₁ = h₂ ≫ m)
    (hπ : π' ≫ u = h₂ ≫ π) {n : ℕ}
    {b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₁) (fun _ => N))} (c : Fin n → Γ(T, ⊤))
    {s : LB.Sec (LB.LinComb L (fun _ : Fin 1 => σ₂) (fun _ => N))}
    {b' : Fin n → LB.Sec (LB.LinComb L' (fun _ : Fin 1 => σ₁') (fun _ => N))}
    {s' : LB.Sec (LB.LinComb L' (fun _ : Fin 1 => σ₂') (fun _ => N))}
    (hb : ∀ i, Rel w _ _ _ h₁ (b' i) (b i)) (hs : Rel w _ _ _ h₂ s' s) (r : Z ⟶ Y₂') (z : Z) (p : L.ι) (q : L'.ι)
    (hp : F (σ₂' (r z)) ∈ L.U p) (hq : σ₂' (r z) ∈ L'.U q) :
    LinAt L' N σ₁' σ₂' m' π' b' (fun i => u.appTop.hom (c i)) s' r z q ↔ LinAt L N σ₁ σ₂ m π b c s (r ≫ h₂) z p := by
  subst hm'
  have e₁ := hs Z r z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
  have e₂ := fun i => hb i Z (r ≫ m') z (fun _ => p) (fun _ => q) (fun _ => hp) (fun _ => hq)
  have e₃ : pw w (fun _ : Fin 1 => σ₁') (fun _ => N) (r ≫ m') z (fun _ => p) (fun _ => q) =
      pw w (fun _ : Fin 1 => m' ≫ σ₁') (fun _ => N) r z (fun _ => p) (fun _ => q) := by
    simp only [pw, Category.assoc]
  have e₄ : ∀ i, gs (r ≫ π') z ⊤ (u.appTop.hom (c i)) = gs ((r ≫ h₂) ≫ π) z ⊤ (c i) := fun i =>
    (gs_pull (r ≫ π') u z ⊤ trivial (c i)).trans (by rw [Category.assoc, hπ, Category.assoc])
  have e₅ : (r ≫ h₂) ≫ m = (r ≫ m') ≫ h₁ := by rw [Category.assoc, ← hh, Category.assoc]
  unfold LinAt
  rw [e₁, e₅]
  simp only [e₂, e₃, e₄, mul_left_comm _ (Units.val _), ← Finset.mul_sum, Units.mul_right_inj]

end General

def totMap {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    (hp : IsPullback φ G'.hom G.hom f) {T' : Over Z'} {T : Over Z} (u : T'.left ≅ T.left)
    (hu : u.hom ≫ T.hom = T'.hom ≫ f) : (T' ⊗ G').left ⟶ (T ⊗ G).left :=
  pullback.lift ((fst T' G').left ≫ u.hom) ((snd T' G').left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hu, hp.w, ← Category.assoc, ← Category.assoc, Over.w, Over.w])

section
variable {Z Z' : Scheme.{0}} {G : Over Z} {G' : Over Z'} {f : Z' ⟶ Z} {φ : G'.left ⟶ G.left}
    (hp : IsPullback φ G'.hom G.hom f) {T' : Over Z'} {T : Over Z} (u : T'.left ≅ T.left)
    (hu : u.hom ≫ T.hom = T'.hom ≫ f)

theorem totMap_fst : totMap hp u hu ≫ (fst T G).left = (fst T' G').left ≫ u.hom := pullback.lift_fst _ _ _

theorem totMap_snd : totMap hp u hu ≫ (snd T G).left = (snd T' G').left ≫ φ := pullback.lift_snd _ _ _

theorem totMap_isIso : IsIso (totMap hp u hu) := by
  have p₁ : IsPullback (snd T' G').left (fst T' G').left G'.hom T'.hom := (IsPullback.of_hasPullback T'.hom G'.hom).flip
  have p₂ : IsPullback (snd T G).left (fst T G).left G.hom T.hom := (IsPullback.of_hasPullback T.hom G.hom).flip
  have p₃ := p₁.paste_horiz hp
  rw [← totMap_snd hp u hu, ← hu] at p₃
  have p₄ := IsPullback.of_right p₃ (totMap_fst hp u hu) p₂
  exact p₄.isIso_fst_of_isIso

end

theorem transport : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → ∀ N : ℕ, ∃ e : ∀ (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left), u.hom ≫ T.hom = T'.hom ≫ f → (LB.Sec (Out.LPow G' L' (N : ℤ) T') ≃ LB.Sec (Out.LPow G L (N : ℤ) T)), ∀ (T₁' T₂' : Over Z') (T₁ T₂ : Over Z) (u₁ : T₁'.left ≅ T₁.left) (u₂ : T₂'.left ≅ T₂.left) (h₁ : u₁.hom ≫ T₁.hom = T₁'.hom ≫ f) (h₂ : u₂.hom ≫ T₂.hom = T₂'.hom ≫ f) (k' : T₂' ⟶ T₁') (k : T₂ ⟶ T₁), k'.left ≫ u₁.hom = u₂.hom ≫ k.left → ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) T₁')) (c : Fin n → Γ(T₂.left, ⊤)) (s : LB.Sec (Out.LPow G' L' (N : ℤ) T₂')), GlobalTheory.LN.Lin G' L' N k' b (fun i => u₂.hom.appTop.hom (c i)) s ↔ GlobalTheory.LN.Lin G L N k (fun i => e T₁' T₁ u₁ h₁ (b i)) c (e T₂' T₂ u₂ h₂ s) := by
  intro Z Z' G G' f φ L L' hL hL' hp ⟨w, hw⟩ N
  have H := fun (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left) (hu : u.hom ≫ T.hom = T'.hom ≫ f) =>
    haveI := totMap_isIso hp u hu
    exists_equiv hL hL' w hw (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T G).left) (fun _ => (N : ℤ))
      (totMap hp u hu) (fun _ => (totMap_snd hp u hu).symm)
  choose e he using H
  refine ⟨e, fun T₁' T₂' T₁ T₂ u₁ u₂ h₁ h₂ k' k hk n b c s => ?_⟩
  have hm : (k ▷ G).left ≫ (snd T₁ G).left = (snd T₂ G).left := by rw [← Over.comp_left, whiskerRight_snd]
  have hm' : (k' ▷ G').left ≫ (snd T₁' G').left = (snd T₂' G').left := by rw [← Over.comp_left, whiskerRight_snd]
  have hf : (k ▷ G).left ≫ (fst T₁ G).left = (fst T₂ G).left ≫ k.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have hf' : (k' ▷ G').left ≫ (fst T₁' G').left = (fst T₂' G').left ≫ k'.left := by
    rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have hh : (k' ▷ G').left ≫ totMap hp u₁ h₁ = totMap hp u₂ h₂ ≫ (k ▷ G).left := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst T₁ G).left = (_ ≫ _) ≫ (fst T₁ G).left
      rw [Category.assoc, Category.assoc, totMap_fst, hf, reassoc_of% hf', hk, ← Category.assoc, ← Category.assoc,
        totMap_fst]
    · show (_ ≫ _) ≫ (snd T₁ G).left = (_ ≫ _) ≫ (snd T₁ G).left
      rw [Category.assoc, Category.assoc, totMap_snd, hm, reassoc_of% hm', totMap_snd]
  have key := fun (W : Scheme.{0}) (r : W ⟶ (T₂' ⊗ G').left) =>
    linAt_iff w (N : ℤ) hm' hh (totMap_fst hp u₂ h₂).symm c (fun i => he T₁' T₁ u₁ h₁ (b i)) (he T₂' T₂ u₂ h₂ s) r
  refine (val_iff hL' _ _ _ _ _ hm' b _ s).trans (Iff.trans ?_ (val_iff hL _ _ _ _ _ hm _ c _).symm)
  constructor
  · intro H W r z p hz
    haveI := totMap_isIso hp u₂ h₂
    obtain ⟨r', rfl⟩ : ∃ r', r = r' ≫ totMap hp u₂ h₂ := ⟨r ≫ inv (totMap hp u₂ h₂), by simp⟩
    obtain ⟨q, hq⟩ := exists_chart hL' ((snd T₂' G').left (r' z))
    refine (key W r' z p q ?_ hq).1 (H W r' z q hq)
    show ((snd T₂' G').left ≫ φ) (r' z) ∈ L.U p
    rw [← totMap_snd hp u₂ h₂]; exact hz
  · intro H W r z q hq
    obtain ⟨p, hz⟩ := exists_chart hL (φ ((snd T₂' G').left (r z)))
    refine (key W r z p q hz hq).2 (H W _ z p ?_)
    show (totMap hp u₂ h₂ ≫ (snd T₂ G).left) (r z) ∈ L.U p
    rw [totMap_snd]; exact hz

end GlobalTheory.SecMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionPowerTransportCartesianSquareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sectionPower_transport_cartesian_square : ∀ (Z Z' : Scheme.{0}) (G : Over Z) (G' : Over Z') (f : Z' ⟶ Z) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsPullback φ G'.hom G.hom f → LBIso L' (L.pull φ) → ∀ N : ℕ, ∃ e : ∀ (T' : Over Z') (T : Over Z) (u : T'.left ≅ T.left), u.hom ≫ T.hom = T'.hom ≫ f → (LB.Sec (Out.LPow G' L' (N : ℤ) T') ≃ LB.Sec (Out.LPow G L (N : ℤ) T)), ∀ (T₁' T₂' : Over Z') (T₁ T₂ : Over Z) (u₁ : T₁'.left ≅ T₁.left) (u₂ : T₂'.left ≅ T₂.left) (h₁ : u₁.hom ≫ T₁.hom = T₁'.hom ≫ f) (h₂ : u₂.hom ≫ T₂.hom = T₂'.hom ≫ f) (k' : T₂' ⟶ T₁') (k : T₂ ⟶ T₁), k'.left ≫ u₁.hom = u₂.hom ≫ k.left → ∀ (n : ℕ) (b : Fin n → LB.Sec (Out.LPow G' L' (N : ℤ) T₁')) (c : Fin n → Γ(T₂.left, ⊤)) (s : LB.Sec (Out.LPow G' L' (N : ℤ) T₂')), GlobalTheory.LN.Lin G' L' N k' b (fun i => u₂.hom.appTop.hom (c i)) s ↔ GlobalTheory.LN.Lin G L N k (fun i => e T₁' T₁ u₁ h₁ (b i)) c (e T₂' T₂ u₂ h₂ s) := by
  first | exact @GlobalTheory.SecMove.transport | exact GlobalTheory.SecMove.transport | (intros; apply GlobalTheory.SecMove.transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardPulledSectionsFormBasisEqPowDim
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardPulledSectionsFormBasisEqPowDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.SecRank

theorem card_eq_of_basisAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {T₁ T₂ T' : Over S} [Nontrivial Γ(T'.left, ⊤)] (h₁ : T' ⟶ T₁) (h₂ : T' ⟶ T₂) {n m : ℕ}
    {a : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T₁)} {b : Fin m → LB.Sec (Out.LPow G L (N : ℤ) T₂)}
    (ha : BasisAlong G L N h₁ a) (hb : BasisAlong G L N h₂ b) : n = m := by
  choose a' ha' _ using fun i => PolFrames.exists_pullSec G L N h₁ (a i)
  choose b' hb' _ using fun i => PolFrames.exists_pullSec G L N h₂ (b i)
  obtain ⟨l₁, s₁⟩ := (PolFrames.basisAlong_iff G L N h₁ hL ha').1 ha
  obtain ⟨l₂, s₂⟩ := (PolFrames.basisAlong_iff G L N h₂ hL hb').1 hb
  have e₁ := Module.finrank_eq_card_basis (Module.Basis.mk l₁ s₁.ge)
  have e₂ := Module.finrank_eq_card_basis (Module.Basis.mk l₂ s₂.ge)
  simpa using e₁.symm.trans e₂

theorem card_basis_eq_pow : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  intro _ hL R _ _ P N n b hN hb
  obtain ⟨V, hV, c, hc⟩ := hL.secBaseChangeAny (Sp R) P N hN (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (IsLocalRing.specializes_closedPoint x).mem_open V.isOpen hV
  subst hV'
  let χ : Sp R ⟶ (⊤ : (Sp R).Opens).toScheme := (Sp R).topIso.inv
  choose c' hc' _ using fun i => PolFrames.exists_pullSec P.A P.L N (Out.homAt χ) (c i)
  have H := (PolFrames.basisAlong_iff P.A P.L N (Out.homAt χ) P.isLB hc').2 (hc R χ c' hc')
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R)) : Over (Sp R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have key : ∀ (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (T : Over (Sp R)) (h : Over.mk f ⟶ T)
      (d : Fin (N ^ P.g) → LB.Sec (Out.LPow P.A P.L (N : ℤ) T)), BasisAlong P.A P.L N h d → n = N ^ P.g := by
    rintro _ rfl T h d hd
    exact card_eq_of_basisAlong P.A P.L P.isLB N _ h hb hd
  refine key (Out.baseAt χ).hom ?_ _ (Out.homAt χ) c H
  exact (congrArg (χ ≫ ·) (Category.comp_id (⊤ : (Sp R).Opens).ι)).trans (Sp R).toIso_inv_ι

end GlobalTheory.LN.SecRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardPulledSectionsFormBasisEqPowDimStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  first | exact @GlobalTheory.LN.SecRank.card_basis_eq_pow | exact GlobalTheory.LN.SecRank.card_basis_eq_pow | (intros; apply GlobalTheory.LN.SecRank.card_basis_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FibresSplitOfOpenImmersionCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FibresSplitOfOpenImmersionCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory

theorem splitFibre_of_isOpenImmersion {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsOpenImmersion f] (G : Over Z) [GrpObj G]
    (G' : Over Y) [GrpObj G'] (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) (h : SplitFib G') (y : Y) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField (f y)) k), FiniteDimensional (Z.residueField (f y)) k ∧
      Algebra.IsSeparable (Z.residueField (f y)) k ∧ ∃ S : SplitExt (Sp k),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫
          Z.fromSpecResidueField (f y))).obj G) := by
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := h y
  let ε : Z.residueField (f y) ≃+* Y.residueField y := (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv
  let A : Algebra (Z.residueField (f y)) k :=
    ((algebraMap (Y.residueField y) k).comp (f.residueFieldMap y).hom).toAlgebra
  have hc : (algebraMap (Z.residueField (f y)) k).comp (ε.symm : Y.residueField y →+* Z.residueField (f y)) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (Y.residueField y) k) := by
    ext a
    exact congrArg (algebraMap (Y.residueField y) k) (ε.apply_symm_apply a)
  refine ⟨k, inferInstance, A, Module.Finite.of_equiv_equiv ε.symm (RingEquiv.refl k) hc,
    Algebra.IsSeparable.of_equiv_equiv ε.symm (RingEquiv.refl k) hc, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Y.fromSpecResidueField y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫ Z.fromSpecResidueField (f y) := by
    have a₁ : Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Spec.map (f.residueFieldMap y) := by
      rw [← Spec.map_comp]
      rfl
    rw [a₁, Category.assoc, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← key]
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y)).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₀ := isGt_of_iso ((Over.pullback _).mapIso e) hGt
  have : IsMonHom (pullCompIso (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y) f G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  exact isGt_of_iso (pullCompIso _ f G).symm h₀

theorem splitFib_of_openCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  intro E _ _ _ H Z t I Y f u m ho hc hs z
  obtain ⟨i, y, rfl⟩ := hc z
  have := ho i
  exact splitFibre_of_isOpenImmersion (f i) t.G (u i).G _ (m i).cart (hs i) y

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FibresSplitOfOpenImmersionCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibresSplit_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  first | exact @GlobalTheory.splitFib_of_openCover | exact GlobalTheory.splitFib_of_openCover | (intros; apply GlobalTheory.splitFib_of_openCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAwayFlatProjRep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearCut


open MvPolynomial in
theorem homogeneousComponent_mem_vanIdeal {R σ Hh : Type} [CommRing R] (d : ℕ) (p : Hh → σ → R)
    (F : MvPolynomial σ R) (hF : F ∈ vanIdeal d p) (e : ℕ) : homogeneousComponent e F ∈ vanIdeal d p := by
  classical
  letI := (MvPolynomial.gradedAlgebra : GradedAlgebra (homogeneousSubmodule σ R))
  have h : (vanIdeal d p).IsHomogeneous (homogeneousSubmodule σ R) :=
    Ideal.homogeneous_span _ _ fun x hx => ⟨d, hx.1⟩
  have := h e hF
  rwa [show ((DirectSum.decompose (homogeneousSubmodule σ R) F e : homogeneousSubmodule σ R e) : MvPolynomial σ R)
    = homogeneousComponent e F from MvPolynomial.decomposition.decompose'_apply F e] at this


open MvPolynomial in
theorem eval₂_eq_zero_of_forms_le {K σ : Type} [CommRing K] {I J : Ideal (MvPolynomial σ K)} {d : ℕ}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I)
    (hle : ∀ e ≥ d, ∀ F : MvPolynomial σ K, F.IsHomogeneous e → F ∈ I → F ∈ J)
    {T : Type} [CommRing T] (β : K →+* T) (v : σ → T) (hv : Ideal.span (Set.range v) = ⊤)
    (hJ : ∀ F ∈ J, eval₂ β v F = 0) : ∀ F ∈ I, eval₂ β v F = 0 := by
  intro F hF
  have key : ∀ e, eval₂ β v (homogeneousComponent e F) = 0 := by
    intro e
    have h1 : ∀ i, v i ^ d * eval₂ β v (homogeneousComponent e F) = 0 := by
      intro i
      have := hJ _ (hle (d + e) (by omega) (X i ^ d * homogeneousComponent e F)
        ((isHomogeneous_X_pow i d).mul (homogeneousComponent_isHomogeneous e F)) (I.mul_mem_left _ (hI F hF e)))
      rwa [eval₂_mul, eval₂_pow, eval₂_X] at this
    have h2 := Ideal.span_pow_eq_top _ hv d
    have h3 : Ideal.span ((fun x => x ^ d) '' Set.range v) ≤
        LinearMap.ker (LinearMap.toSpanSingleton T T (eval₂ β v (homogeneousComponent e F))) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact h1 i
    rw [h2] at h3
    simpa using h3 (Submodule.mem_top (x := (1 : T)))
  rw [← sum_homogeneousComponent F, eval₂_sum]
  exact Finset.sum_eq_zero fun e _ => key e

theorem exists_away_flat_projRep : ∀ (R σ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ] [Finite Hh] (p : Hh → σ → R) (Q : Polynomial ℚ) (d : ℕ) (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (I : Ideal (MvPolynomial σ K)), RingHom.ker x = q ∧ CutBy I Q d (fun h i => x (p h i))) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ (Z : Over (Sp (Localization.Away f))) (M : LB Z.left) (th : σ → M.Sec), ProjRep (vanIdeal d (fun h i => loc f (p h i))) Z.hom M th ∧ Flat Z.hom ∧ ∀ (K : Type) [Field K] (x : Localization.Away f →+* K) (I : Ideal (MvPolynomial σ K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : σ → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (loc f (p h i))) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : σ → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w := by
  intro R σ Hh _ _ _ _ _ p Q d P hP hcutP q₀ hq₀
  obtain ⟨f, hf, hproj, hmap⟩ := GlobalTheory.T.exists_away_projective_forms_through_points R σ Hh p Q d P hP hcutP q₀ hq₀
  obtain ⟨Z, s, M, th, -, hrep, -, hflat⟩ := GlobalTheory.T.exists_projCoordRepresentation_homogeneousIdeal_flat (Localization.Away f) σ
    (vanIdeal d (fun h i => loc f (p h i))) d (homogeneousComponent_mem_vanIdeal d _)
  refine ⟨f, hf, Over.mk s, M, th, hrep, hflat fun e he => by have := hproj e he; infer_instance, ?_⟩
  intro K _ x I X s' M' th' hI hcut hrep'
  have hpb := IsPullback.of_hasPullback s (spMap x)
  obtain ⟨th₁, hrep₁, hc₁⟩ := GlobalTheory.T.projective_representation_pullback_coordinates _ K σ x _ Z _ s _ _ M th hrep hpb
  rw [hmap K x] at hrep₁
  obtain ⟨e, he, hiso, hc⟩ := GlobalTheory.T.exists_iso_of_projectiveCoordinateRepresentation K σ I _ X _ s' _ M' _ th' th₁ hrep' hrep₁ fun T _ β v hv =>
    ⟨eval₂_eq_zero_of_forms_le (homogeneousComponent_mem_vanIdeal d _) (fun e he F hF h => ((hcut e he).2 F hF).2 h) β v hv,
      eval₂_eq_zero_of_forms_le hI (fun e he F hF h => ((hcut e he).2 F hF).1 h) β v hv⟩
  refine ⟨e.hom ≫ pullback.fst s (spMap x), ?_, ?_, fun T _ y w => ?_⟩
  · have h0 : IsPullback e.hom s' (pullback.snd s (spMap x)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩
    simpa using h0.paste_horiz hpb
  · exact LBIso.trans hrep'.1 (pull_isLB hrep₁.1 _) (pull_isLB hrep.1 _) hiso
      (LBIso.chartPull (Geo.Tor.chartPullPull _ e.hom e.hom rfl) (chartPullSame M _ _ _ e.hom fun _ => rfl)
        ⟨_, idIso_isGen hrep₁.1⟩)
  · rw [hc T y w, hc₁ T _ w, Category.assoc]

end GlobalTheory.ZM.NearCut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechData
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum


open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in
theorem lin_of_isEmpty {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} [hT : IsEmpty T'.left]
    (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T')) : Lin G L N h b c s := by
  intro z
  exact isEmptyElim ((fst T' G).left z)

theorem isEmpty_of_eq_bot {Z : Scheme.{0}} {U : Z.Opens} (h : U = ⊥) : IsEmpty U.toScheme := by
  subst h
  exact ⟨fun x => by simpa using x.2⟩

theorem subsingleton_sections_of_isEmpty {X : Scheme.{0}} [IsEmpty X] : Subsingleton Γ(X, ⊤) := by
  refine CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)
  ext x
  exact isEmptyElim x


open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in
theorem trans_of_inf_eq_bot {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) {n : ℕ} (r s : ℤ) {U V : Z.Opens}
    (hUV : U ⊓ V = ⊥) (thU : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk U.ι)))
    (thV : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk V.ι)))
    (bU : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))) (bV : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk V.ι)))
    (g : Γ(Z, U ⊓ V)) :
    ∃ (c : Γ((U ⊓ V).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((U ⊓ V).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => thU) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        (fun _ : Fin 1 => thV) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => bU k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        bV (fun k' => M.val k k') t) ∧
    (U ⊓ V).topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val := by
  have hE : IsEmpty (U ⊓ V).toScheme := isEmpty_of_eq_bot hUV
  have := subsingleton_sections_of_isEmpty (X := (U ⊓ V).toScheme)
  have sec : ∀ M : ℕ, LB.Sec (LPow G L (M : ℤ) (Over.mk (U ⊓ V).ι)) := fun M =>
    { f := fun _ => 0
      compat := fun _ _ => fn_ext fun y _ => (hE.false ((fst (Over.mk (U ⊓ V).ι) G).left y)).elim }
  refine ⟨1, 1, ⟨sec 1, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _⟩,
    fun k => ⟨sec N, lin_of_isEmpty (hT := hE) G L N _ _ _ _, lin_of_isEmpty (hT := hE) G L N _ _ _ _⟩,
    Subsingleton.elim _ _⟩

theorem hasFrames_sumLB : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  intro Z G L N A B n r s hAB hA hB
  obtain ⟨thA, bA, hAt, hAb⟩ := hA
  obtain ⟨thB, bB, hBt, hBb⟩ := hB
  refine ⟨fun | .inl i => thA i | .inr j => thB j, fun | .inl i => bA i | .inr j => bB j, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · exact hAt i j
    · exact trans_of_inf_eq_bot G L N r s (hAB i j) (thA i) (thB j) (bA i) (bB j) _
    · exact trans_of_inf_eq_bot G L N r s (by rw [inf_comm]; exact hAB j i) (thB i) (thA j) (bB i) (bA j) _
    · exact hBt i j
  · rintro (i | i) W _ _ _ hW χ hχ
    · exact hAb i W hW χ hχ
    · exact hBb i W hW χ hχ

end GlobalTheory.ModelSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFrames_disjointUnionCechData : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_sumLB | exact GlobalTheory.ModelSum.hasFrames_sumLB | (intros; apply GlobalTheory.ModelSum.hasFrames_sumLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8Form
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8Form
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PowerForm

theorem diag_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (h : IsE8 W) (u : Fin 8) : 0 < W u u := by
  have h₁ := h.1.diag_pos (i := u)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Int.cast_pos] at h₁
  omega

theorem sum_single {G M : Type*} [Group G] [AddCommGroup M] (B : G → G → M)
    (h₁ : ∀ x x' y, B (x * x') y = B x y + B x' y) (h₂ : ∀ x x' y, B y (x * x') = B y x + B y x')
    (W : Matrix (Fin 8) (Fin 8) ℤ) (x : G) :
    ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • B (if uv.1 = 0 then x else 1) (if uv.2 = 0 then x else 1) =
      W 0 0 • B x x := by
  have z₁ : ∀ y, B 1 y = 0 := fun y => by simpa using h₁ 1 1 y
  have z₂ : ∀ y, B y 1 = 0 := fun y => by simpa using h₂ 1 1 y
  rw [Finset.sum_eq_single (0, 0) (fun b _ hb => ?_) (by simp)]
  · simp
  · by_cases a₁ : b.1 = 0
    · have a₂ : b.2 ≠ 0 := fun a₂ => hb (Prod.ext a₁ a₂)
      rw [if_neg a₂, z₂, smul_zero]
    · rw [if_neg a₁, z₁, smul_zero]


#check GlobalTheory.CechPic.cls_linComb_add
#check GlobalTheory.CechPic.cls_linComb_single
#check GlobalTheory.CechPic.cls_pull
#check GlobalTheory.CechPic.pull_id
#check GlobalTheory.CechPic.pull_comp
open GlobalTheory.CechPic in
theorem relAmple_diag : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  intro W S _ G A _ _ _ _ pr L P hW hG hA _ hpr hL hP hbi hiso hamp
  obtain ⟨j, hj, -⟩ := hpr A fun v => if v = 0 then 𝟙 A else 1
  have := hG.proper
  have hcl : IsClosedImmersion j.left := GlobalTheory.Retract.isClosedImmersion_section (r := (pr 0).left)
    (by rw [← Over.comp_left, hj, if_pos rfl, Over.id_left]) (Over.w (pr 0))
  have hpos := diag_pos hW 0
  have hn : 0 < (W 0 0).toNat := by omega
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := LB.isLB_pull hP _
  have hfin : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have c₁ := (relAmple_finite_pow_iso S A G j L 1 one_pos hA hG hL inferInstance).1 hamp
  refine (relAmple_finite_pow_iso S A A (𝟙 A) _ _ hn hA hA hD hfin).2.1.1
    ((relAmple_finite_pow_iso S A A (𝟙 A) _ 1 one_pos hA hA (LB.isLB_pull hL _) hfin).2.2.2 _
      (LB.isLB_linComb hD _ _) ?_ c₁)
  refine (cls_eq_iff (LB.isLB_pull hL _) (LB.isLB_linComb hD _ _)).1 ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cls_linComb hD, Fintype.sum_unique, pull_id, cls_pull hL, (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hiso, cls_linComb hP, map_sum,
    cls_pull hP, Int.toNat_of_nonneg hpos.le]
  refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_)
    (sum_single (G := A ⟶ A) (fun a b => pull (lift a b).left (cls P hP)) (fun a a' b => ?_) (fun a a' b => ?_)
      W (𝟙 A))
  · rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hj, hj]
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi A a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi A a a' b).2
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel

end GlobalTheory.PowerForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleDiagonalBiadditiveOfE8FormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) [IsLocallyNoetherian S] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), IsE8 W → IsAbelianScheme G → IsAbelianScheme A → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.RelAmple G L → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  first | exact @GlobalTheory.PowerForm.relAmple_diag | exact GlobalTheory.PowerForm.relAmple_diag | (intros; apply GlobalTheory.PowerForm.relAmple_diag <;> assumption)
end
end
