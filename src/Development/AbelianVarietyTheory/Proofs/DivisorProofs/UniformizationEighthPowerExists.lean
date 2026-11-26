module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8Power
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjMumfordTensorPowerOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfPowQuotient
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.PowQuotient

variable {S S' : Scheme.{0}}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {n : ℕ} (a : Fin n → (G ⟶ H))
    (ha : ∀ i, IsMonHom (a i)) : IsMonHom (∏ i, a i) :=
  Finset.prod_induction a (fun z => IsMonHom z) (fun x y _ _ => isMonHom_mul x y) isMonHom_one fun i _ => ha i

end GlobalTheory.PowQuotient

namespace GlobalTheory

open PowQuotient

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerLiftCompProjection
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Pow8

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

abbrev G8 : Over S := powObj G 8

abbrev pr8 (i : Fin 8) : G8 G ⟶ G := powPr G i

def mk8 {T : Over S} (x : Fin 8 → (T ⟶ G)) : T ⟶ G8 G := (powIsLimit G 8).lift (Fan.mk T x)

theorem eighthPowerLift_comp_projection {T : Over S} (x : Fin 8 → (T ⟶ G)) (i : Fin 8) : mk8 G x ≫ pr8 G i = x i :=
  (powIsLimit G 8).fac (Fan.mk T x) ⟨i⟩

theorem eighthPowerGroupObj_hom_ext {T : Over S} {x y : T ⟶ G8 G} (h : ∀ i, x ≫ pr8 G i = y ≫ pr8 G i) : x = y :=
  (powIsLimit G 8).hom_ext fun ⟨i⟩ => h i

def matAct (a : Matrix (Fin 8) (Fin 8) ℤ) : G8 G ⟶ G8 G := mk8 G fun i => ∏ j, pr8 G j ^ a i j

theorem matAct_pr (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) : matAct G a ≫ pr8 G i = ∏ j, pr8 G j ^ a i j :=
  eighthPowerLift_comp_projection G _ i

theorem matAct_hom (a : Matrix (Fin 8) (Fin 8) ℤ) : IsMonHom (matAct G a) :=
  Serre.isMonHom_of_mul_comp _ fun T x y => eighthPowerGroupObj_hom_ext G fun k => by
    have hc : IsMonHom (∏ j, pr8 G j ^ a k j) :=
      PowQuotient.isMonHom_prod _ fun j => Serre.isMonHom_zpow _ _
    rw [MonObj.mul_comp _ _ (pr8 G k), Category.assoc, Category.assoc, Category.assoc, matAct_pr,
      MonObj.mul_comp _ _ (∏ j, pr8 G j ^ a k j)]

theorem matAct_one : matAct G 1 = 𝟙 (G8 G) := eighthPowerGroupObj_hom_ext G fun i => by
  rw [matAct_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Matrix.one_apply_ne' hj]
  · simp

end GlobalTheory.Mum.Pow8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

open GlobalTheory.Mum.Pow8

section Pairing

theorem comp_matAct_pr {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {X : Over S}
    (x : X ⟶ powObj G₀ 8) (a : Matrix (Fin 8) (Fin 8) ℤ) (i : Fin 8) :
    (x ≫ matAct G₀ a) ≫ powPr G₀ i = ∏ j, (x ≫ powPr G₀ j) ^ a i j := by
  rw [Category.assoc, matAct_pr]
  exact GlobalTheory.Mum.TensAct.comp_prod_zpow x _ _

variable {S : Scheme.{0}} {G₀ : Over S} [GrpObj G₀] [IsCommMonObj G₀] {L : LB G₀.left} (hL : L.IsLB)

def formPair (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) : GlobalTheory.CechPic.Pic X.left :=
  ∑ i, ∑ j, M i j • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ i) (y ≫ powPr G₀ j)

theorem cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) :
    GlobalTheory.CechPic.cls _ h = formPair hL W (𝟙 _) (𝟙 _) := by
  refine (GlobalTheory.CechPic.cls_linComb hL _ _ h).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  unfold formPair
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.sum_univ_four, lamPts, negε, GlobalTheory.CechPic.lam, Category.id_comp]
  simp [smul_add, sub_eq_add_neg]

theorem pull_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S} (u : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.pull u.left (GlobalTheory.CechPic.cls _ h) = formPair hL W u u := by
  rw [cls_e8LB hL W h]
  unfold formPair
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, GlobalTheory.CechPic.pull_lam, Category.id_comp]

variable (hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ L), t.IsGen)
include hΘ

theorem formPair_mul (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (u v : X ⟶ powObj G₀ 8) :
    formPair hL M (u * v) (u * v) = formPair hL M u u + formPair hL M v v + formPair hL (M + M.transpose) u v := by
  have hm : ∀ i, (u * v) ≫ powPr G₀ i = (u ≫ powPr G₀ i) * (v ≫ powPr G₀ i) := fun i => MonObj.mul_comp _ _ _
  have e1 : ∀ i j, GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) ((u * v) ≫ powPr G₀ i) ((u * v) ≫ powPr G₀ j) =
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (u ≫ powPr G₀ j) +
        GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (v ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
        (GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ i) (v ≫ powPr G₀ j) +
          GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (u ≫ powPr G₀ j) (v ≫ powPr G₀ i)) := by
    intro i j
    rw [hm, hm, GlobalTheory.CechPic.lam_mul_left hL hΘ, GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ,
      GlobalTheory.Mum.RosatiTens.lam_mul_right hL hΘ, GlobalTheory.CechPic.lam_comm _ (v ≫ powPr G₀ i) (u ≫ powPr G₀ j)]
    abel
  unfold formPair
  simp only [e1, smul_add, Finset.sum_add_distrib, Matrix.add_apply, add_smul, Matrix.transpose_apply]
  congr 2
  exact Finset.sum_comm

theorem formPair_one (M : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} :
    formPair hL M (1 : X ⟶ powObj G₀ 8) 1 = 0 := by
  unfold formPair
  simp [MonObj.one_comp, GlobalTheory.CechPic.lam_one_left]

theorem lam_cls_e8LB (W : Matrix (Fin 8) (Fin 8) ℤ) (h : (e8LB G₀ L W).IsLB) {X : Over S}
    (x y : X ⟶ powObj G₀ 8) :
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls _ h) x y = formPair hL (W + W.transpose) x y := by
  unfold GlobalTheory.CechPic.lam
  simp only [pull_cls_e8LB hL W h]
  rw [formPair_mul hL hΘ, formPair_one hL hΘ]
  abel

theorem formPair_act_left (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M (x ≫ matAct G₀ a) y = formPair hL (a.transpose * M) x y := by
  have s3 : ∀ F : Fin 8 → Fin 8 → Fin 8 → GlobalTheory.CechPic.Pic X.left,
      ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := fun F =>
    calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, F i j k := Finset.sum_comm
      _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_left hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul]
  refine (s3 (fun i j k => (M i j * a i k) •
    GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ≫ powPr G₀ k) (y ≫ powPr G₀ j))).trans ?_
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [mul_comm]

theorem formPair_act_right (M a : Matrix (Fin 8) (Fin 8) ℤ) {X : Over S} (x y : X ⟶ powObj G₀ 8) :
    formPair hL M x (y ≫ matAct G₀ a) = formPair hL (M * a) x y := by
  unfold formPair
  simp only [comp_matAct_pr, GlobalTheory.Mum.RosatiTens.lam_prod_right hL hΘ, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end Pairing

theorem unimodular_symmetrised_matrix_adjugate_identities {W : Matrix (Fin 8) (Fin 8) ℤ} (hB : (W + W.transpose).det = 1) :
    (W + W.transpose) * ((W + W.transpose).adjugate * W) = W ∧
      (W + W.transpose).adjugate * W + (W + W.transpose).adjugate * W.transpose = 1 ∧
      ((W + W.transpose).adjugate * W).transpose * (W + W.transpose) =
        (W + W.transpose) * ((W + W.transpose).adjugate * W.transpose) := by
  have hBt : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by
    rw [Matrix.mul_adjugate, hB, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by
    rw [Matrix.adjugate_mul, hB, one_smul]
  have hAt : (W + W.transpose).adjugate.transpose = (W + W.transpose).adjugate := by
    rw [Matrix.adjugate_transpose, hBt]
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  · rw [← Matrix.mul_add, h2]
  · rw [Matrix.transpose_mul, hAt, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hypW_e8LB : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀)
    (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  intro S G₀ _ _ P W hW
  have hL : P.L.L.IsLB := P.L.isLB
  have hΘ : ∃ t : LB.Gen (ReciprocityTheory.ChartRestriction.G.Semi.Theta G₀ P.L.L), t.IsGen := ⟨P.c.1, P.c.2⟩
  have hE : (e8LB G₀ P.L.L W).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨h1, h2, h3⟩ := unimodular_symmetrised_matrix_adjugate_identities hW.2
  refine ⟨matAct G₀ ((W + W.transpose).adjugate * W), matAct G₀ ((W + W.transpose).adjugate * W.transpose),
    matAct_hom G₀ _, matAct_hom G₀ _, ?_, ?_, ?_⟩
  · rw [← matAct_one G₀, ← h2]
    refine eighthPowerGroupObj_hom_ext G₀ fun i => ?_
    rw [MonObj.mul_comp, matAct_pr, matAct_pr, matAct_pr, ← Finset.prod_mul_distrib]
    simp only [Matrix.add_apply, zpow_add]
  · have hC : (cubeLB (powObj G₀ 8) ![𝟙 (powObj G₀ 8), matAct G₀ ((W + W.transpose).adjugate * W)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hE hC).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC, lam_cls_e8LB hL hΘ W hE, cls_e8LB hL W hE]
    have e := formPair_act_right hL hΘ (W + W.transpose) ((W + W.transpose).adjugate * W)
      (𝟙 (powObj G₀ 8)) (𝟙 (powObj G₀ 8))
    rw [Category.id_comp, h1] at e
    exact e.symm
  · have hC1 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W),
        snd (powObj G₀ 8) (powObj G₀ 8)] (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    have hC2 : (cubeLB (powObj G₀ 8) ![fst (powObj G₀ 8) (powObj G₀ 8),
        snd (powObj G₀ 8) (powObj G₀ 8) ≫ matAct G₀ ((W + W.transpose).adjugate * W.transpose)]
        (e8LB G₀ P.L.L W)).IsLB := LB.isLB_linComb hE _ _
    refine (GlobalTheory.CechPic.cls_eq_iff hC1 hC2).1 ?_
    rw [GlobalTheory.CechPic.cls_cube_two hE _ _ hC1, GlobalTheory.CechPic.cls_cube_two hE _ _ hC2, lam_cls_e8LB hL hΘ W hE,
      lam_cls_e8LB hL hΘ W hE, formPair_act_left hL hΘ, formPair_act_right hL hΘ, h3]

end GlobalTheory.PowE8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypW_e8LB_powObj : ∀ (S : Scheme.{0}) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] (P : GlobalTheory.UU.CP G₀) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → GlobalTheory.LN.HypW (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ P.L.L W) := by
  first | exact @GlobalTheory.PowE8.hypW_e8LB | exact GlobalTheory.PowE8.hypW_e8LB | (intros; apply GlobalTheory.PowE8.hypW_e8LB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8MumfordBundlePowerSectionNonvanishingClosedFib
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8CubicalEvenPolarization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8CubicalEvenPolarization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8


set_option maxHeartbeats 2000000 in
theorem exists_cp_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  intro hL _ _ V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  let P₁ : GlobalTheory.UU.CP G₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₁ W
  refine ⟨Pc, hPc, ?_⟩
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegData.main hL.globalFns V₁ _ D₀ 8
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ A₀ 8
  obtain ⟨U', -⟩ := GlobalTheory.PowUnif.main hL.globalFns V₁ _ 8 D₀ D' A₀ A' G₀ (powObj G₀ 8) pD pA (powIsPowGrp G₀ 8)
    U₀.toUnifPre
  have hp : IsProper (pullback.snd (powObj G₀ 8).hom (jK V₁)) := by
    have := A'.isAb.proper
    have e : pullback.snd (powObj G₀ 8).hom (jK V₁) = U'.gen.hom.left ≫ A'.A.hom := (Over.w U'.gen.hom).symm
    have : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper
  have h3 := GlobalTheory.EvenTriv.surjective_cube_of_generic (powObj G₀ 8) hS8 hp
  obtain ⟨w, -, hw, -, -, hwL, -⟩ := GlobalTheory.PowE8.hypW_e8LB _ G₀ P₁ W hW
  have hwL' : LBIso Pc.L.L (cubeLB (powObj G₀ 8) ![𝟙 _, w] Pc.L.L) := by rw [hPc]; exact hwL
  obtain ⟨P₀, v, hv⟩ := GlobalTheory.UU.exists_isLevelCP (maximalIdeal V₁) 0 Pc
  have hB' : IsAbelianScheme (thickObj V₁ (maximalIdeal V₁) 0 D'.toPre.P.A) :=
    by
      have h := D'.toPre.P.isAb
      have := h.comm
      have := h.smooth
      have := h.proper
      have := h.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
      · change IsProper (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
      · change GeometricallyConnected (pullback.snd D'.toPre.P.A.hom (thick V₁ (maximalIdeal V₁) 0))
        infer_instance
  let Q₀ := GlobalTheory.Mum.tqOfGtCoord (U'.gt 0) hB'
  have hm : (maximalIdeal V₁ ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI : Field (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) := Ideal.Quotient.field _
  have : Smooth (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)).hom := by
    have := hS8.smooth
    change Smooth (pullback.snd (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0))
    infer_instance
  have : GeometricallyConnected (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)).hom := by
    have := hS8.geomConnected
    change GeometricallyConnected (pullback.snd (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0))
    infer_instance
  have := Q₀.i_hom
  letI := D'.toPre.addX
  haveI := D'.toPre.freeX
  haveI := D'.toPre.finX
  obtain ⟨s⟩ := GlobalTheory.BiextTriv.main (V₁ ⧸ maximalIdeal V₁ ^ (0 + 1)) D'.toPre.X
    (thickObj V₁ (maximalIdeal V₁) 0 (powObj G₀ 8)) P₀.L P₀.c Q₀.i Q₀.i_hom
  haveI := hw
  obtain ⟨σ, hσ⟩ := GlobalTheory.EvenTriv.exists_even_of_surjective h3 Pc w hwL' P₀
    (IsPullback.of_hasPullback (powObj G₀ 8).hom (thick V₁ (maximalIdeal V₁) 0)) hv Q₀.i s
  exact ⟨D'.toPre.X, D'.toPre.addX, D'.toPre.freeX, D'.toPre.finX, Q₀, P₀, ⟨v, hv⟩, σ, hσ⟩

end GlobalTheory.PowE8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8CubicalEvenPolarizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cubical_e8LB_evenOn : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ Pc : GlobalTheory.UU.CP (powObj G₀ 8), Pc.L.L = GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W ∧ GlobalTheory.Mum.EvenOn Pc := by
  first | exact @GlobalTheory.PowE8.exists_cp_evenOn | exact GlobalTheory.PowE8.exists_cp_evenOn | (intros; apply GlobalTheory.PowE8.exists_cp_evenOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.E8LatticePullbackGeneric

open GlobalTheory.CechPic

theorem sum_lamPts {S : Scheme.{0}} {G T : Over S} [GrpObj G] (x y : T ⟶ G) (c : Pic G.left) (w : ℤ) :
    ∑ k : Fin 4, (-(w * GlobalTheory.PolDeg.negε k)) • pull (GlobalTheory.PolDeg.lamPts x y k) c = w • lam c x y := by
  simp only [Fin.sum_univ_four, GlobalTheory.PolDeg.lamPts, GlobalTheory.PolDeg.negε, lam, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [smul_add, smul_sub, mul_neg, mul_one, neg_neg, neg_smul]
  all_goals first
  | (norm_num; done)
  | (norm_num; abel)
  | (push_cast; abel)
  | (rw [sub_eq_add_neg, sub_eq_add_neg]; congr 1 <;> [congr 1; skip] <;> norm_num)

theorem lam_pull_hom {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] (φ : G' ⟶ G) [IsMonHom φ]
    (c : Pic G.left) (x y : T ⟶ G') : lam (pull φ.left c) x y = lam c (x ≫ φ) (y ≫ φ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem pull_fst_lam {S S' : Scheme.{0}} (f : S' ⟶ S) {X G : Over S} [GrpObj G] (c : Pic G.left) (x x' : X ⟶ G) :
    GlobalTheory.CechPic.pull (pullback.fst X.hom f) (lam c x x') =
      lam (GlobalTheory.CechPic.pull (pullback.fst G.hom f) c) ((Over.pullback f).map x) ((Over.pullback f).map x') := by
  have hfst : ∀ z : X ⟶ G, pullback.fst X.hom f ≫ z.left = ((Over.pullback f).map z).left ≫ pullback.fst G.hom f :=
    fun z => by simp [pullback.lift_fst]
  simp only [lam, map_add (f := _), map_sub, ← pull_comp, hfst, Functor.map_mul, Functor.map_one]


open GlobalTheory.E8LatticePullbackGeneric GlobalTheory.CechPic in
theorem exists_polAV_gen : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro hL₁ _ _ V₁ _ _ _ _ D₀ G₀ _ _ A₀ U₀ _ W hW
  have := A₀.isAb.comm

  let c := GlobalTheory.EighthPowerFactor.siegOne hL₁.globalFns A₀.isAb A₀.isLB A₀.g
  have hc1 : RelAmple c.A c.diag := GlobalTheory.EighthPowerFactor.relAmple_diag_lam A₀.isAb A₀.isLB
    (GlobalTheory.Moduli.cube_of_isLB _ A₀ A₀.L A₀.isLB) A₀.ample
  have hb := GlobalTheory.EighthPower.isSymBilin hL₁.globalFns c hc1
  have hpw := GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp A₀.A 8)
  have hu : ∀ (T : Over (Sp (FractionRing V₁))) (y : Fin 8 → (T ⟶ A₀.A)),
      ∃! x : T ⟶ powObj A₀.A 8, ∀ u, x ≫ powPr A₀.A u = y u := fun T y =>
    ⟨(powIsLimit A₀.A 8).lift (Fan.mk T y), fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩,
      fun x hx => (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by rw [(powIsLimit A₀.A 8).fac]; exact hx u⟩
  let Q : PolAV (Sp (FractionRing V₁)) :=
    { A := powObj A₀.A 8, isAb := hpw.2.2.2.1 A₀.isAb, g := 8 * A₀.g, smoothDim := hpw.2.2.1 _ A₀.smoothDim
      L := GlobalTheory.MatrixBundle.matLB c.P (powPr A₀.A) W, isLB := LB.isLB_linComb c.isLB _ _
      rigid := GlobalTheory.MatrixBundle.rigidified_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      sym := GlobalTheory.MatrixBundle.sym_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u)
      ample := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hL₁.globalFns _ _ 8 _ _ _ _ c _ (powPr A₀.A) W
        (fun u => powPr.isMonHom A₀.A u) hu hc1 hW.1
      ktriv := GlobalTheory.MatrixBundle.kTriv_matLB c.isLB hb (fun u => powPr.isMonHom A₀.A u) hu hW.2
        (fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam A₀.isLB A₀.ktriv x hx) }

  let F := Over.pullback (jK V₁)
  have hP : IsLimit (Fan.mk (F.obj (powObj G₀ 8)) fun u => F.map (powPr G₀ u)) :=
    isLimitFanMkObjOfIsLimit F _ _ (powIsLimit G₀ 8)
  let y : Fin 8 → (F.obj (powObj G₀ 8) ⟶ A₀.A) := fun u => F.map (powPr G₀ u) ≫ U₀.gen.hom
  let gen : F.obj (powObj G₀ 8) ≅ Q.A :=
    { hom := (powIsLimit A₀.A 8).lift (Fan.mk _ y)
      inv := hP.lift (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv)
      hom_inv_id := hP.hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp only [Fan.mk_π_app]
        erw [(powIsLimit A₀.A 8).fac_assoc (Fan.mk _ y) ⟨u⟩]
        simp [y]
      inv_hom_id := (powIsLimit A₀.A 8).hom_ext fun ⟨u⟩ => by
        simp only [Fan.mk_pt, Fan.mk_π_app, Category.assoc, Category.id_comp]
        erw [(powIsLimit A₀.A 8).fac (Fan.mk _ y) ⟨u⟩]
        simp only [Fan.mk_π_app, y]
        rw [← Category.assoc]
        erw [hP.fac (Fan.mk Q.A fun u => powPr A₀.A u ≫ U₀.gen.inv) ⟨u⟩]
        simp }
  have hgen : ∀ u, gen.hom ≫ powPr A₀.A u = y u := fun u => (powIsLimit A₀.A 8).fac _ ⟨u⟩
  have := U₀.gen_hom
  refine ⟨Q, gen, ?_, ?_⟩
  · refine GlobalTheory.EighthPowerFactor.isMonHom_of_coord (fun u => powPr.isMonHom A₀.A u) hu fun u => ?_
    rw [hgen u]
    infer_instance
  · have hA := A₀.isLB
    have hLG := U₀.LG.isLB
    have hQ : Q.L.IsLB := Q.isLB
    have hE : (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).IsLB := LB.isLB_linComb hLG _ _
    have hext : pull (pullback.fst G₀.hom (jK V₁)) (cls _ hLG) = pull U₀.gen.hom.left (cls _ hA) := by
      obtain ⟨w, hw⟩ := U₀.ext
      have e := (cls_eq_iff (pull_isLB hA _) (pull_isLB hLG _)).2 ⟨w, hw⟩
      rw [cls_pull hA, cls_pull hLG] at e
      exact e.symm
    have key : ∀ x x' : powObj G₀ 8 ⟶ G₀, pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (lam (cls _ hLG) x x') =
        lam (cls _ hA) (F.map x ≫ U₀.gen.hom) (F.map x' ≫ U₀.gen.hom) := by
      intro x x'
      rw [pull_fst_lam, hext, lam_pull_hom]
    have hlam : cls c.P c.isLB = lam (cls _ hA) (fst A₀.A A₀.A) (snd A₀.A A₀.A) := cls_cube_two hA _ _ c.isLB
    have eL : pull gen.hom.left (cls Q.L hQ) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [show cls Q.L hQ = _ from cls_linComb c.isLB
        (fun uv : Fin 8 × Fin 8 => (lift (powPr A₀.A uv.1) (powPr A₀.A uv.2)).left) (fun uv => W uv.1 uv.2) hQ, map_sum]
      refine Finset.sum_congr rfl fun uv _ => ?_
      rw [map_zsmul, hlam]
      erw [pull_lam, pull_lam]
      rw [lift_fst, lift_snd]
      erw [hgen, hgen]
    have eR : pull (pullback.fst (powObj G₀ 8).hom (jK V₁)) (cls _ hE) =
        ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • lam (cls _ hA) (y uv.1) (y uv.2) := by
      rw [show cls _ hE = _ from cls_linComb hLG (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => GlobalTheory.PolDeg.lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * GlobalTheory.PolDeg.negε k.2)) hE, Fintype.sum_prod_type]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [sum_lamPts, map_sum, map_zsmul, key, y]
    refine (cls_eq_iff (pull_isLB hQ _) (pull_isLB hE _)).1 ?_
    rw [cls_pull hQ, cls_pull hE, eL, eR]

end GlobalTheory.E8LatticePullbackGeneric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerPolarizedGenericFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polAV_generic_fibre_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ (A : PolAV (Sp (FractionRing V₁))) (gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  first | exact @GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen | exact GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen | (intros; apply GlobalTheory.E8LatticePullbackGeneric.exists_polAV_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8MumfordBundlePowerSectionNonvanishingClosedFib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem thetaNZ_e8LB : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  intro hL hL2 hE V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ hS W hW
  have hB : GlobalTheory.Mum.Base V₁ := by
    obtain ⟨h1, h2, h3, h4⟩ := hCN
    exact ⟨⟨h1, inferInstance, h2, h3⟩, h4⟩
  obtain ⟨Pc, hPc, hEv⟩ := GlobalTheory.T.exists_cubical_e8LB_evenOn hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  obtain ⟨A, gen, hgen, hA⟩ := GlobalTheory.T.exists_polAV_generic_fibre_e8LB hL hL2 hE V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hS8 : IsSemiAbelian (powObj G₀ 8) := GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS
  obtain ⟨D, U, hU, -⟩ := GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal V₁ hB _ Pc hS8 hEv A gen hgen (hPc ▸ hA)
  have h := GlobalTheory.T.preUniformised_fibrewise_nonvanishing_section V₁ hB D A _ U (hU ▸ hEv)
  rw [hU, hPc] at h
  exact h

end GlobalTheory.PowE8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8MumfordBundlePowerSectionNonvanishingClosedFibStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaNZ_e8LB_powObj : Laws → Laws2 → GlobalTheory.LN.Ega → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → GlobalTheory.LN.ThetaNZ (powObj G₀ 8) (GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W) := by
  first | exact @GlobalTheory.PowE8.thetaNZ_e8LB | exact GlobalTheory.PowE8.thetaNZ_e8LB | (intros; apply GlobalTheory.PowE8.thetaNZ_e8LB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitPow

theorem splitExtensionModuloIdeal_eighth_power : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R),
    GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  intro R _ G₀ _ _ I ⟨E, ⟨D⟩⟩
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  obtain ⟨p, -⟩ := GlobalTheory.isPowGrp_baseChange _ _ (spMap (Ideal.Quotient.mk I)) (powObj G₀ 8) G₀ 8 (powIsPowGrp G₀ 8)
  obtain ⟨pT, -⟩ := GlobalTheory.exists_isPowGrp_splitTorus (Sp (R ⧸ I)) E.X (Fin 8 → E.X) 8 (AddEquiv.refl _)
  obtain ⟨q', hq, hq1, hq2, hq3, hq4, -⟩ :=
    GlobalTheory.PowMap.main _ _ _ (powObj E.B 8) E.B 8 p (powIsPowGrp E.B 8) D.q
  obtain ⟨i', hi, hi1, -⟩ := GlobalTheory.PowMap.main _ _ _ _ _ 8 pT p D.i
  have hB : IsAbelianScheme (powObj E.B 8) := (GlobalTheory.PowGrp.powers _ _ _ 8 (powIsPowGrp E.B 8)).2.2.2.1 E.isAbelian
  have hk := GlobalTheory.PowKernel.main _ _ _ _ _ _ _ 8 pT p (powIsPowGrp E.B 8) D.i D.q i' q' hi hq D.isKernel
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj G₀) := inferInstance
  haveI : IsCommMonObj ((Over.pullback (spMap (Ideal.Quotient.mk I))).obj (powObj G₀ 8)) := inferInstance
  have hqc : QuasiCompact D.q.left := by
    have := D.q_affine
    infer_instance
  obtain ⟨O, h₁, h₂, h₃, h⟩ := GlobalTheory.exists_gtDatum_of_splitTorus_extension _ (Fin 8 → E.X) _ (powObj E.B 8) hB q' i'
    (hq1 D.q_hom) (hi1 D.i_hom) (hq2 D.q_flat) (hq3 D.q_surjective) (hq4 hqc) hk
  obtain ⟨d, -, -⟩ := h hB
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory.SplitPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitOver_powObj_eight : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R), GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  first | exact @GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power | exact GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power | (intros; apply GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SplitRed

theorem splitOver_of_unif : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  intro V₁ _ _ _ _ D₀ G₀ _ _ A₀ U _
  obtain ⟨E, -, -, -, -, hE⟩ := GlobalTheory.gtCoord_isGt V₁ (IsLocalRing.maximalIdeal V₁) D₀.toPre 0 G₀ ⟨U.gt 0⟩
  have key : ∀ J : Ideal V₁, J = IsLocalRing.maximalIdeal V₁ →
      ∀ S : SplitExt (Spec (CommRingCat.of (V₁ ⧸ J))),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G₀) →
        GlobalTheory.LN.SplitOver G₀ (IsLocalRing.maximalIdeal V₁) := by
    rintro J rfl S hS
    exact ⟨S, hS⟩
  exact key _ (pow_one _) E hE

end GlobalTheory.SplitRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))), Unif (maximalIdeal V₁) D₀ A₀ G₀ → IsSemiAbelian G₀ → GlobalTheory.LN.SplitOver G₀ (maximalIdeal V₁) := by
  first | exact @GlobalTheory.SplitRed.splitOver_of_unif | exact GlobalTheory.SplitRed.splitOver_of_unif | (intros; apply GlobalTheory.SplitRed.splitOver_of_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpGen
open GlobalTheory.PowE8

theorem exists_gen {S T : Scheme.{0}} (f : T ⟶ S) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] {B C : Over T}
    [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a)
    (u : (Over.pullback f).obj G₀ ≅ C) [IsMonHom u.hom] :
    ∃ gen : (Over.pullback f).obj (powObj G₀ 8) ≅ B, IsMonHom gen.hom ∧
      ∀ a, gen.hom ≫ pr a = (Over.pullback f).map (powPr G₀ a) ≫ u.hom := by
  let hl := isLimitOfPreserves (Over.pullback f) (powIsLimit G₀ 8)
  let ρ : Fin 8 → ((Over.pullback f).obj (powObj G₀ 8) ⟶ (Over.pullback f).obj G₀) :=
    fun a => (Over.pullback f).map (powPr G₀ a)
  choose x hx hxu using fun (T' : Over T) (y : Fin 8 → (T' ⟶ C)) => huniq T' y
  let inv : B ⟶ (Over.pullback f).obj (powObj G₀ 8) :=
    hl.lift ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩
  have hinv : ∀ a, inv ≫ ρ a = pr a ≫ u.inv := fun a => hl.fac ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩ ⟨a⟩
  let hom := x _ (fun a => ρ a ≫ u.hom)
  have hhom : ∀ a, hom ≫ pr a = ρ a ≫ u.hom := hx _ _
  refine ⟨⟨hom, inv, ?_, ?_⟩, ?_, hhom⟩
  · refine hl.hom_ext fun ⟨a⟩ => ?_
    show (hom ≫ inv) ≫ ρ a = 𝟙 _ ≫ ρ a
    rw [Category.assoc, hinv, ← Category.assoc, hhom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · have h1 := hxu B (fun a => pr a) (inv ≫ hom) (fun a => by
      rw [Category.assoc, hhom, ← Category.assoc, hinv, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have h2 := hxu B (fun a => pr a) (𝟙 B) (fun a => Category.id_comp _)
    exact h1.trans h2.symm
  · have hm : ∀ a, IsMonHom (hom ≫ pr a) := fun a => by rw [hhom]; infer_instance
    constructor
    · have h1 := hxu _ (fun a => η[C]) (η ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.one_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => η[C]) η (fun a => by haveI := hpr a; exact IsMonHom.one_hom (pr a))
      exact h1.trans h2.symm
    · have h1 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) (μ ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.mul_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) ((hom ⊗ₘ hom) ≫ μ) (fun a => by
        haveI := hpr a; rw [Category.assoc, IsMonHom.mul_hom (pr a), ← Category.assoc, tensorHom_comp_tensorHom])
      exact h1.trans h2.symm

theorem lift_lamφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (x y : T ⟶ B)
    (I : ULift.{0} (Finset (Fin 2))) :
    (lift x y).left ≫ GlobalTheory.PrimCocycle.lamφ B I = (psum B ![x, y] I.down).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
    (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))

theorem psum_comp_hom {S : Scheme.{0}} {B C T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
    (u : B ⟶ C) [IsMonHom u] (x y : T ⟶ B) (I : Finset (Fin 2)) :
    psum C ![x ≫ u, y ≫ u] I = psum B ![x, y] I ≫ u :=
  ((congrArg (fun q => psum C q I) (funext fun i => by fin_cases i <;> rfl)).trans
    (psum_hom (MonoidHom.mk' (fun z : T ⟶ B => z ≫ u) fun a b => MonObj.mul_comp a b u) ![x, y] I).symm)

theorem zpow_lam {U : Type} [CommGroup U] (a b c d : U) (w : ℤ) :
    (a * b⁻¹ * c⁻¹ * d) ^ w = a ^ (-(w * negε 0)) * b ^ (-(w * negε 1)) * c ^ (-(w * negε 2)) * d ^ (-(w * negε 3)) := by
  simp only [negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_zpow, inv_zpow', mul_neg, mul_one, neg_neg]
  norm_num

theorem gen_eighthPower : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  set_option maxSynthPendingDepth 10 in
    classical
    let trivialSums (X : Scheme.{0}) (L : LB X) (Y : Scheme.{0}) : Subgroup (Group.Abelianization (FreeGroup (Y ⟶ X))) := {
      carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), GlobalTheory.MulPull.HasGen L φ ε ∧
        ∏ k, Group.Abelianization.of (FreeGroup.of (φ k)) ^ ε k = s}
      one_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ⟨LB.oneGen L, fun _ _ => (map_one _).trans
        ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm⟩,
        Fintype.prod_empty _⟩
      mul_mem' := by
        rintro _ _ ⟨K, _, φ, ε, h, rfl⟩ ⟨K', _, φ', ε', h', rfl⟩
        exact ⟨K ⊕ K', inferInstance, _, _, h.mul h', Fintype.prod_sum_type _⟩
      inv_mem' := by
        rintro _ ⟨K, _, φ, ε, h, rfl⟩
        exact ⟨K, inferInstance, _, _, h.inv, by simp only [zpow_neg, Finset.prod_inv_distrib]⟩ }

    let cls {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Group.Abelianization (FreeGroup (Y ⟶ X)) ⧸ trivialSums X L Y := QuotientGroup.mk' _ (Group.Abelianization.of (FreeGroup.of ψ))

    have hasGen_iff {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
        GlobalTheory.MulPull.HasGen L φ ε ↔ ∏ k, cls L (φ k) ^ ε k = 1 := by
      have e : ∏ k, cls L (φ k) ^ ε k =
          QuotientGroup.mk' (trivialSums X L Y) (∏ k, Group.Abelianization.of (FreeGroup.of (φ k)) ^ ε k) := by
        simp only [map_prod, map_zpow, cls]
      rw [e, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      refine ⟨fun h => ⟨K, inferInstance, φ, ε, h, rfl⟩, ?_⟩
      rintro ⟨K', _, φ', ε', h, e⟩
      refine h.of_formEq hL fun U _ f => ?_
      simpa only [map_prod, map_zpow, Group.Abelianization.lift_apply_of, FreeGroup.lift_apply_of] using
        congrArg (Group.Abelianization.lift (FreeGroup.lift f)) e

    have lbIso_iff {X Y : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) :
        LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔ ∏ k, cls L (φ k) ^ ε k = ∏ k, cls L (φ' k) ^ ε' k := by
      have e : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε') ↔ GlobalTheory.MulPull.HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) :=
        ⟨fun ⟨w, hw⟩ => gen_chartPull (GlobalTheory.PrimNorm.chartDivIn L φ ε φ' ε') w hw,
          fun ⟨w, hw⟩ => gen_chartPull (GlobalTheory.PrimNorm.chartDivOut L φ ε φ' ε') w hw⟩
      rw [e, hasGen_iff hL]
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_eq_one]
      exact eq_comm

    have prod_flat {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ) :
        ∏ p : K' × K, cls L (ψ p.1 ≫ φ p.2) ^ (ε p.2 * δ p.1) = ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k := by
      simp only [Fintype.prod_prod_type, ← Finset.prod_zpow, zpow_mul]

    have lbIso_nested {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (ψ : K' → (Z ⟶ Y)) (δ : K' → ℤ)
        {K₃ : Type} [Fintype K₃] (χ : K₃ → (Z ⟶ X)) (κ : K₃ → ℤ)
        (h : ∏ k, (∏ l, cls L (ψ k ≫ φ l) ^ ε l) ^ δ k = ∏ k, cls L (χ k) ^ κ k) :
        LBIso (LB.LinComb (LB.LinComb L φ ε) ψ δ) (LB.LinComb L χ κ) :=
      ((lbIso_iff hL _ _ χ κ).2 ((prod_flat φ ε ψ δ).trans h)).chartPull (GlobalTheory.PrimNorm.chartFlat L φ ε ψ δ) (chartPullId _)

    intro g n o _ ζ F W V₁ _ _ _ D₀ G₀ _ _ A₀ U₀ y α α₂ hcart hsq hlb P hP
    obtain ⟨c, ⟨φ, φ₂, hφ, hφsq, hφlb, -⟩, pr, prh, prl, hPL⟩ := hP
    obtain ⟨e, he, heα⟩ := grpPullback_iso hcart hφ
    haveI := he
    haveI := U₀.gen_hom
    haveI : IsMonHom (U₀.gen ≪≫ e).hom := by rw [Iso.trans_hom]; infer_instance
    obtain ⟨gen, hgen, hcoord⟩ := exists_gen (jK V₁) G₀ pr prh prl (U₀.gen ≪≫ e)
    refine ⟨gen, hgen, ?_⟩
    have hA0 := A₀.isLB
    have hc := c.isLB
    have hLG := U₀.LG.isLB
    have hPl := P.isLB
    have hU := F.univ.isLB
    let ρ : Fin 8 → ((Over.pullback (jK V₁)).obj (powObj G₀ 8) ⟶ (Over.pullback (jK V₁)).obj G₀) :=
      fun a => (Over.pullback (jK V₁)).map (powPr G₀ a)
    let e₂ : (G2 A₀.A).left ⟶ (G2 c.A).left := (lift (fst _ _ ≫ e.hom) (snd _ _ ≫ e.hom)).left
    let mAB : Fin 8 × Fin 8 → (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ (G2 A₀.A).left) :=
      fun ab => (lift (ρ ab.1 ≫ U₀.gen.hom) (ρ ab.2 ≫ U₀.gen.hom)).left
    have hm : ∀ ab : Fin 8 × Fin 8, mAB ab ≫ e₂ = gen.hom.left ≫ (lift (pr ab.1) (pr ab.2)).left := fun ab => by
      simp only [mAB, e₂, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hcoord, Iso.trans_hom,
        Category.assoc]
      rfl
    have he₂ : e₂ ≫ φ₂ = α₂ := by
      apply pullback.hom_ext
      · have h1 : (fst F.univ.A F.univ.A).left = pullback.fst _ _ := rfl
        rw [← h1, Category.assoc, hφsq.1, hsq.1, ← heα]
        simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_fst]
      · have h1 : (snd F.univ.A F.univ.A).left = pullback.snd _ _ := rfl
        rw [← h1, Category.assoc, hφsq.2, hsq.2, ← heα]
        simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_snd]
    have Q1 : LBIso (c.P.pull e₂) (abelian₂ A₀.A A₀.L) := by
      refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
        (GlobalTheory.PowPrimitive.lbIso_linComb hφlb (fun _ : PUnit => e₂) (fun _ => 1)) ?_
      refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
        (lbIso_nested hU (fun _ : PUnit => φ₂) (fun _ => 1) (fun _ : PUnit => e₂) (fun _ => 1)
          (fun _ : PUnit => α₂) (fun _ => 1) (by simp [he₂])) ?_
      exact hlb.symm
    let q := pullback.fst (powObj G₀ 8).hom (jK V₁)
    let q0 := pullback.fst G₀.hom (jK V₁)
    let n : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) →
        (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ ((Over.pullback (jK V₁)).obj G₀).left) :=
      fun p => (psum _ ![ρ p.1.1, ρ p.1.2] p.2.down).left
    let κ : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => GlobalTheory.PrimCocycle.lamε p.2 * W p.1.1 p.1.2
    have hn : ∀ ab I, mAB ab ≫ GlobalTheory.PrimCocycle.lamφ A₀.A I = n (ab, I) ≫ U₀.gen.hom.left := fun ab I => by
      rw [lift_lamφ, psum_comp_hom]; rfl
    let Uq : Over.mk (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).hom ≫ jK V₁) ⟶ powObj G₀ 8 :=
      Over.homMk q pullback.condition
    have hq : ∀ ab I, n (ab, I) ≫ q0 = q ≫ (lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I :=
      fun ab I => by
        rw [lift_lamφ]
        refine psum_push (isGrpPullback_pullback G₀ (jK V₁)) _ _ Uq (fun i => ?_) I.down
        apply Over.OverMorphism.ext
        fin_cases i
        · exact pullback.lift_fst _ _ _
        · exact pullback.lift_fst _ _ _
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hPL (fun _ : PUnit => gen.hom.left) (fun _ => 1)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hc _ _ (fun _ : PUnit => gen.hom.left) (fun _ => 1) (fun ab => mAB ab ≫ e₂)
        (fun ab => W ab.1 ab.2) (by simp [hm])) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hc (fun _ : PUnit => e₂) (fun _ => 1) mAB (fun ab => W ab.1 ab.2)
        (fun ab => mAB ab ≫ e₂) (fun ab => W ab.1 ab.2) (by simp)).symm ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb Q1 mAB (fun ab => W ab.1 ab.2)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hA0 (GlobalTheory.PrimCocycle.lamφ A₀.A) GlobalTheory.PrimCocycle.lamε mAB (fun ab => W ab.1 ab.2)
        (fun p => n p ≫ U₀.gen.hom.left) κ ?_) ?_
    · refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
      refine Fintype.prod_congr _ _ fun ab => ?_
      rw [← Finset.prod_zpow]
      refine Fintype.prod_congr _ _ fun I => ?_
      rw [← zpow_mul, hn]
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hA0 (fun _ : PUnit => U₀.gen.hom.left) (fun _ => 1) n κ
        (fun p => n p ≫ U₀.gen.hom.left) κ (by simp)).symm ?_
    obtain ⟨w, hw⟩ := U₀.ext
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (GlobalTheory.PowPrimitive.lbIso_linComb ⟨w, hw⟩ n κ) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (lbIso_nested hLG (fun _ : PUnit => q0) (fun _ => 1) n κ (fun p => n p ≫ q0) κ (by simp)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      ((lbIso_iff hLG (fun p => n p ≫ q0) κ
        (fun k : (Fin 8 × Fin 8) × Fin 4 => q ≫ lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
        (fun k => -(W k.1.1 k.1.2 * negε k.2))).2 ?_) ?_
    · refine ((Fintype.prod_prod_type _).trans ?_).trans (Fintype.prod_prod_type _).symm
      refine Fintype.prod_congr _ _ fun ab => ?_
      have e1 : ∏ I, cls U₀.LG.L (n (ab, I) ≫ q0) ^ κ (ab, I) =
          (∏ I, (fun m => cls U₀.LG.L (q ≫ m))
            ((lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I) ^ GlobalTheory.PrimCocycle.lamε I) ^
            W ab.1 ab.2 := by
        rw [← Finset.prod_zpow]
        refine Fintype.prod_congr _ _ fun I => ?_
        rw [← zpow_mul, hq]
        simp only [κ, Category.assoc]
      rw [e1]
      refine (congrArg (· ^ W ab.1 ab.2) (GlobalTheory.PrimCocycle.prod_lam (powPr G₀ ab.1) (powPr G₀ ab.2)
        (fun m => cls U₀.LG.L (q ≫ m)))).trans ?_
      rw [Fin.prod_univ_four]
      exact zpow_lam _ _ _ _ _
    exact (lbIso_nested hLG
      (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
      (fun k => -(W k.1.1 k.1.2 * negε k.2)) (fun _ : PUnit => q) (fun _ => 1) _ _ (by simp)).symm

end GlobalTheory.SharpGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_eighth_power_uniformised_is_polarised : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  first | exact @GlobalTheory.SharpGen.gen_eighthPower | exact GlobalTheory.SharpGen.gen_eighthPower | (intros; apply GlobalTheory.SharpGen.gen_eighthPower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem isAdmissibleBase_of_completeNormalLocalCharZero (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (h : IsCN V₁) :
    GlobalTheory.LN.admitted V₁ (maximalIdeal V₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  exact ⟨⟨h1, inferInstance, h2, h3⟩, h3, h4, inferInstance, inferInstance⟩

theorem exists_unif_pow8 : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  intro g n o _ ζ F W hW V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb P hP
  have hL := GlobalTheory.abelianSchemeLaws_all
  let P₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.1.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₀ W
  obtain ⟨gen, hgen, hA⟩ := GlobalTheory.T.generic_eighth_power_uniformised_is_polarised g n o ζ F W V₁ D₀ G₀ A₀ U₀ y α α₂ hpb hsq hlb P hP
  have hW8 : GlobalTheory.LN.HypW (powObj G₀ 8) Pc.L.L := hPc ▸ GlobalTheory.T.hypW_e8LB_powObj _ G₀ P₀ W hW
  have hT : GlobalTheory.LN.ThetaNZ (powObj G₀ 8) Pc.L.L :=
    hPc ▸ GlobalTheory.T.thetaNZ_e8LB_powObj hL.1 hL.2 GlobalTheory.LN.ega_holds V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hA' : LBIso (P.L.pull gen.hom.left) (Pc.L.L.pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := hPc ▸ hA
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  obtain ⟨D, U, -, -⟩ := GlobalTheory.PrimeUnif.exists_unif hL.1 hL.2 GlobalTheory.laws3 GlobalTheory.LN.ega_holds GlobalTheory.uniformisation_total_closed V₁
    (maximalIdeal V₁) (isAdmissibleBase_of_completeNormalLocalCharZero V₁ hCN) inferInstance (powObj G₀ 8) Pc
    (GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS) hW8
    (GlobalTheory.T.splitOver_powObj_eight V₁ G₀ _ (GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal V₁ hCN D₀ G₀ A₀ U₀ hS)) hT P gen hgen hA'
  exact ⟨D, ⟨U⟩⟩

end GlobalTheory.PowE8
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationEighthPowerExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformization_eighth_power_exists : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  first | exact @GlobalTheory.PowE8.exists_unif_pow8 | exact GlobalTheory.PowE8.exists_unif_pow8 | (intros; apply GlobalTheory.PowE8.exists_unif_pow8 <;> assumption)
end
