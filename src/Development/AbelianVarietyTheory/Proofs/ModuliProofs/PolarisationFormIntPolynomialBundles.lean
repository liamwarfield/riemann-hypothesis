module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LiftConnectedOfTrivialUnique
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GoodPtOfIrredOfMulPull

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.FormPoly

open GlobalTheory.CechPic Polynomial

theorem poly_induction {p : ℤ[X] → Prop} (h1 : p 1) (hadd : ∀ F G, p F → p G → p (F + G))
    (hneg : ∀ F, p F → p (-F)) (hX : ∀ F, p F → p (X * F)) (F : ℤ[X]) : p F := by
  have h0 : p 0 := by simpa using hadd 1 (-1) h1 (hneg 1 h1)
  have hC : ∀ a : ℤ, p (Polynomial.C a) := by
    intro a
    induction a using Int.induction_on with
    | zero => simpa using h0
    | succ i ih => simpa using hadd _ _ ih h1
    | pred i ih => simpa [sub_eq_add_neg] using hadd _ _ ih (hneg 1 h1)
  have hmono : ∀ (n : ℕ) (a : ℤ), p (Polynomial.monomial n a) := by
    intro n a
    induction n with
    | zero => simpa using hC a
    | succ n ih => rw [← Polynomial.X_mul_monomial]; exact hX _ ih
  induction F using Polynomial.induction_on' with
  | add F G hF hG => exact hadd _ _ hF hG
  | monomial n a => exact hmono n a

theorem exists_apply {V : Type} [CommGroup V] (c : V → V) (hc : ∀ a b, c (a * b) = c a * c b) (v : V) :
    ∃ ev : ℤ[X] → V, ev 1 = v ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = c (ev F) := by
  let φ : Module.End ℤ (Additive V) :=
    (AddMonoidHom.mk' (fun a => Additive.ofMul (c a.toMul)) (fun a b => by simp [hc])).toIntLinearMap
  refine ⟨fun F => (Polynomial.aeval φ F (Additive.ofMul v)).toMul, by simp, fun F G => by simp, fun F => by simp [φ]⟩

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem exists_ev (s : A ⟶ A) [IsMonHom s] : ∃ ev : ℤ[X] → (A ⟶ A), ev 1 = 𝟙 A ∧
    (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (X * F) = ev F ≫ s := by
  exact exists_apply (fun f => f ≫ s) (fun a b => MonObj.mul_comp a b s) (𝟙 A)

section Ev

variable {s : A ⟶ A} [IsMonHom s] {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
  (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s)

include hadd in
theorem ev_neg (F : ℤ[X]) : ev (-F) = (ev F)⁻¹ := by
  have h0 : ev 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (_root_.mul_one _).symm)
  have e := hadd F (-F)
  rw [add_neg_cancel, h0] at e
  exact eq_inv_of_mul_eq_one_right e.symm

include h1 hadd hX

theorem ev_isMonHom (F : ℤ[X]) : IsMonHom (ev F) := by
  refine poly_induction (p := fun F => IsMonHom (ev F)) ?_ ?_ ?_ ?_ F
  · rw [h1]; infer_instance
  · intro F G hF hG; rw [hadd, Hom.mul_def]; infer_instance
  · intro F hF; rw [ev_neg hadd]; infer_instance
  · intro F hF; rw [hX]; infer_instance

omit [IsMonHom s] in
theorem ev_mul (F G : ℤ[X]) : ev (F * G) = ev F ≫ ev G := by
  refine poly_induction (p := fun G => ev (F * G) = ev F ≫ ev G) ?_ ?_ ?_ ?_ G
  · rw [_root_.mul_one, h1, Category.comp_id]
  · intro G H hG hH; rw [mul_add, hadd, hadd, hG, hH, MonObj.comp_mul]
  · intro G hG; rw [mul_neg, ev_neg hadd, ev_neg hadd, hG, GrpObj.comp_inv]
  · intro G hG; rw [mul_left_comm F X G, hX, hX, hG, Category.assoc]

omit [IsMonHom s] hadd in
theorem ev_X : ev X = s := by
  have e := hX 1
  rwa [_root_.mul_one, h1, Category.id_comp] at e

end Ev

variable {L : LB A.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen)

include hΘ in
theorem lam_inv_left {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x⁻¹ y = -lam (cls L hL) x y := by
  have e := lam_mul_left hL hΘ x x⁻¹ y
  rw [mul_inv_cancel, lam_one_left] at e
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact e.symm

include hΘ in
theorem lam_inv_right {T : Over S} (x y : T ⟶ A) : lam (cls L hL) x y⁻¹ = -lam (cls L hL) x y := by
  rw [lam_comm, lam_inv_left hL hΘ, lam_comm]


include hΘ in
theorem lam_ev_adj {s : A ⟶ A} {ev : ℤ[X] → (A ⟶ A)} (h1 : ev 1 = 𝟙 A)
    (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (X * F) = ev F ≫ s) {T : Over S}
    (hs : ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ s) y = lam (cls L hL) x (y ≫ s)) (F : ℤ[X]) :
    ∀ x y : T ⟶ A, lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F) := by
  have hcomm : ∀ G : ℤ[X], s ≫ ev G = ev G ≫ s := by
    intro G
    have e := ev_mul h1 hadd hX X G
    rw [ev_X h1 hX, hX] at e
    exact e.symm
  refine poly_induction (p := fun F => ∀ x y : T ⟶ A,
    lam (cls L hL) (x ≫ ev F) y = lam (cls L hL) x (y ≫ ev F)) ?_ ?_ ?_ ?_ F
  · intro x y; simp only [h1, Category.comp_id]
  · intro F G hF hG x y
    rw [hadd, MonObj.comp_mul, MonObj.comp_mul, lam_mul_left hL hΘ,
      GlobalTheory.HermTensorLB.lam_mul_right hL hΘ, hF, hG]
  · intro F hF x y
    rw [ev_neg hadd, GrpObj.comp_inv, GrpObj.comp_inv, lam_inv_left hL hΘ, lam_inv_right hL hΘ, hF]
  · intro F hF x y
    rw [hX, ← Category.assoc, hs, hF, Category.assoc, ← hcomm F]

theorem pull_one {K : Type} [Field K] {B T : Over (Sp K)} [GrpObj B] (c : Pic B.left) :
    pull (1 : T ⟶ B).left c = 0 := by
  rw [Hom.one_def, Over.comp_left, pull_comp]
  obtain ⟨N, hN, hc⟩ := cls_surj (pull η[B].left c)
  rw [← hc, (cls_eq_zero_iff hN).2 (ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local N hN), map_zero]

private theorem isLB_cube_lemma {S : Scheme.{0}} {A T : Over S} [GrpObj A] {n : ℕ} (x : Fin n → (T ⟶ A))
    {N : LB A.left} (hN : N.IsLB) : (cubeLB A x N).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hN _ _

private theorem lam_id_lemma_2 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (c : Pic A.left)
    (hadd : ∀ x y z : A ⟶ A, lam c x (y * z) = lam c x y + lam c x z) :
    lam c (𝟙 A) (𝟙 A) = c + pull (GrpObj.inv : A ⟶ A).left c := by
  have e := hadd (𝟙 A) (𝟙 A) (𝟙 A)⁻¹
  rw [_root_.mul_inv_cancel, lam_one_right] at e
  have e2 : lam c (𝟙 A) (𝟙 A)⁻¹ = -c - pull (GrpObj.inv : A ⟶ A).left c := by
    unfold lam
    rw [_root_.mul_inv_cancel, pull_one, ← GrpObj.inv_eq_inv, Over.id_left, pull_id]
    abel
  rw [e2, eq_comm, add_eq_zero_iff_eq_neg] at e
  rw [e]
  abel

private theorem pull_inv_lemma_3 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    (h : Out.Sym A L) : pull (GrpObj.inv : A ⟶ A).left (cls L hL) = cls L hL := by
  obtain ⟨U, hU, t, ht⟩ := h (IsLocalRing.closedPoint K)
  have hV : A.hom ⁻¹ᵁ U = ⊤ := by
    rw [ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem U hU]
    simp
  have h0 := (cls_eq_zero_iff (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_two] at h0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul,
    ← sub_eq_add_neg, sub_eq_zero, pull_comp] at h0
  have hf : (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom) ≫ (A.hom ⁻¹ᵁ U).ι = 𝟙 A.left := by
    rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
  have e := congrArg (pull (A.left.topIso.inv ≫ (A.left.isoOfEq hV.symm).hom)) h0
  rw [← pull_comp _ (A.hom ⁻¹ᵁ U).ι, ← pull_comp _ (A.hom ⁻¹ᵁ U).ι, hf, pull_id, pull_id] at e
  exact e

end GlobalTheory.FormPoly

namespace GlobalTheory

open GlobalTheory.CechPic GlobalTheory.FormPoly

theorem formPoly_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  intro laws _ K _ _ P M s hM hF
  obtain ⟨hsM, hFi⟩ := hF
  have hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := by
    obtain ⟨r, hr⟩ := P.rigid
    obtain ⟨cs⟩ := (laws.cube (Sp K) P { L := P.L, rig := r, isLB := P.isLB, rigGen := hr } rfl).1
    exact ⟨cs.t, cs.isGen⟩
  have hc : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A) (N : LB P.A.left) (hN : N.IsLB),
      cls (cubeLB P.A ![x, y] N) (isLB_cube_lemma _ hN) = lam (cls N hN) x y :=
    fun x y N hN => cls_cube_two hN x y _
  have eF : lam (cls M hM) (fst P.A P.A) (snd P.A P.A) =
      lam (cls P.L P.isLB) (fst P.A P.A) (snd P.A P.A ≫ s) := by
    rw [← hc _ _ M hM, ← hc _ _ P.L P.isLB]
    exact (cls_eq_iff (isLB_cube_lemma _ hM) (isLB_cube_lemma _ P.isLB)).2 hFi
  have eF' : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls M hM) x y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    have e := congrArg (pull (lift x y).left) eF
    rwa [pull_lam, pull_lam, lift_fst, lift_snd, lift_snd_assoc] at e
  have hsa : ∀ (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ s) y = lam (cls P.L P.isLB) x (y ≫ s) := by
    intro T x y
    rw [lam_comm (cls P.L P.isLB) (x ≫ s) y, ← eF' y x, lam_comm (cls M hM) y x, eF' x y]
  have hMadd : ∀ x y z : P.A ⟶ P.A,
      lam (cls M hM) x (y * z) = lam (cls M hM) x y + lam (cls M hM) x z := by
    intro x y z
    rw [eF', eF', eF', MonObj.mul_comp, GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ]
  have hι := pull_inv_lemma_3 P.isLB P.sym
  refine ⟨exists_ev s, fun ev h1 hadd hX => ?_⟩
  have adj : ∀ (F : Polynomial ℤ) (T : Over (Sp K)) (x y : T ⟶ P.A),
      lam (cls P.L P.isLB) (x ≫ ev F) y = lam (cls P.L P.isLB) x (y ≫ ev F) :=
    fun F T => lam_ev_adj P.isLB hΘ h1 hadd hX (hsa T) F
  refine ⟨ev_isMonHom h1 hadd hX, ev_mul h1 hadd hX, ?_, ?_, ?_, ?_, ?_⟩
  · intro F
    have := ev_isMonHom h1 hadd hX F
    unfold FormIs
    refine ⟨ev_isMonHom h1 hadd hX (2 * F), ?_⟩
    show LBIso (cubeLB P.A ![fst P.A P.A, snd P.A P.A] (cubeLB P.A ![𝟙 P.A, ev F] P.L)) _
    rw [← cls_eq_iff (isLB_cube_lemma _ (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB), hc, hc, hc,
      GlobalTheory.HermTensorLB.lam_lam P.isLB hΘ, two_mul, hadd, MonObj.comp_mul,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, Category.comp_id, Category.comp_id,
      lam_comm (cls P.L P.isLB) (snd P.A P.A), adj]
    all_goals first | exact P.isLB | exact isLB_cube_lemma _ P.isLB
  · intro F G
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (pull_isLB (isLB_cube_lemma _ P.isLB) _),
      cls_pull (isLB_cube_lemma _ P.isLB), hc, hc, pull_lam, Category.comp_id]
    have e := adj G P.A (𝟙 P.A) (ev G ≫ ev F)
    rw [Category.id_comp] at e
    rw [e, show G ^ 2 * F = G * F * G by ring, ev_mul h1 hadd hX, ev_mul h1 hadd hX, Category.assoc]
    all_goals exact P.isLB
  · intro F G
    rw [← cls_eq_iff (LB.isLB_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB)) (isLB_cube_lemma _ P.isLB),
      cls_div (isLB_cube_lemma _ P.isLB) (isLB_cube_lemma _ P.isLB), hc, hc, hc, hadd,
      GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ, add_sub_cancel_left]
    all_goals exact P.isLB
  · rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ P.isLB _ _), hc,
      cls_lbPow P.isLB, h1, lam_id_lemma_2 _ (fun x y z => GlobalTheory.HermTensorLB.lam_mul_right P.isLB hΘ x y z), hι,
      two_nsmul]
    all_goals exact P.isLB
  · intro hsym
    have hιM : pull (GrpObj.inv : P.A ⟶ P.A).left (cls M hM) = cls M hM := by
      rw [← cls_pull hM _ (pull_isLB hM _)]
      exact ((cls_eq_iff hM (pull_isLB hM _)).2 hsym).symm
    have e := eF' (𝟙 P.A) (𝟙 P.A)
    rw [Category.id_comp] at e
    rw [← cls_eq_iff (isLB_cube_lemma _ P.isLB) (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ hM _ _), hc, cls_lbPow hM,
      ev_X h1 hX, ← e, lam_id_lemma_2 _ hMadd, hιM, two_nsmul]
    all_goals exact P.isLB

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundlesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationForm_intPolynomial_bundles : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → (∃ ev : Polynomial ℤ → (P.A ⟶ P.A), ev 1 = 𝟙 P.A ∧ (∀ F G, ev (F + G) = ev F * ev G) ∧ ∀ F, ev (Polynomial.X * F) = ev F ≫ s) ∧ ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → (∀ F, IsMonHom (ev F)) ∧ (∀ F G, ev (F * G) = ev F ≫ ev G) ∧ (∀ F, FormIs P (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) (ev (2 * F))) ∧ (∀ F G, LBIso (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ((cubeLB P.A ![𝟙 P.A, ev (F)] P.L).pull (ev G).left)) ∧ (∀ F G, LBIso (LB.div (cubeLB P.A ![𝟙 P.A, ev (F + G)] P.L) (cubeLB P.A ![𝟙 P.A, ev (F)] P.L)) (cubeLB P.A ![𝟙 P.A, ev (G)] P.L)) ∧ LBIso (cubeLB P.A ![𝟙 P.A, ev (1)] P.L) (lbPow P.L 2) ∧ (SymB M → LBIso (cubeLB P.A ![𝟙 P.A, ev (Polynomial.X)] P.L) (lbPow M 2)) := by
  first | exact @GlobalTheory.formPoly_bundles | exact GlobalTheory.formPoly_bundles | (intros; apply GlobalTheory.formPoly_bundles <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfPeriod
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open PeriodPoint

theorem exists_point_of_period : ThetaUnifAV → Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M
    : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin
    g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef
    : LinearMap.BilinForm ℤ Λ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
    ℂ)) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ a b : Λ, (Ef
    a b : ℝ) = (hermForm Hm a b).im) → Function.Bijective Ef → ∃ (P : Out.PolAV (Sp ℂ)) (u
    : HolUnif P.A P.L g) (χ
    : u.Λ → ℂ), P.g = g ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (P
    P' : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif P.A P.L g) (u' : HolUnif P'.A P'.L g) (F : (Fin g →
    ℂ) →ₗ[ℂ] (Fin g →
    ℂ)), P.g = g → P'.g = g → (∀ z ∈ u.Λ, F z ∈ u'.Λ) → ∃ f : P.A ⟶ P'.A, IsMonHom f ∧ ∀ z, u'.ex (F
    z) = u.ex z ≫ f) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P : Out.PolAV (Sp
    k)) (a a' : P.A ⟶ P.A), IsMonHom a → IsMonHom a' → (∀ (n : ℕ) (x y : 𝟙_ (Over (Sp k)) ⟶ P.A) (c
    : Γ((𝟙_ (Over (Sp k))).left, ⊤)ˣ), 0 < n → x ^ n = 1 → y ^ n = 1 → Out.WeilIs P.A P.L n (x ≫
    a) y c → Out.WeilIs P.A P.L n x (y ≫ a') c) → LBIso (cubeLB P.A ![fst P.A P.A ≫ a, snd P.A P.A]
    P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ a'] P.L)) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (act
    : OAct (𝓞 E) B) (M : LB B.left), IsAbelianScheme B → M.IsLB → (∃ t : LB.Gen (Theta B
    M), t.IsGen) → (∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M) (cubeLB B ![fst B B, snd
    B B ≫ act.act (H.bar a)] M)) → ∃ (PP : RigLB B) (_
    : CubicalStr B PP), PP.IsSymmetric ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    M) ∧ LBIso (abelian₂ B PP.L) (abelian₂ B M) ∧ LBIso PP.L (cubeLB B ![𝟙 B, act.act H.w0]
    PP.L) ∧ ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] PP.L) (cubeLB B ![fst B B, snd B B
    ≫ act.act (H.bar a)] PP.L)) → (∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (P
    : Out.PolAV (Sp k)) (n : ℕ) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B) (M
    : LB B.left), 0 < n → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → Nat.card {x
    : 𝟙_ (Over (Sp k)) ⟶ P.A // x ≫ ψ = 1} = n ^ P.g → LBIso (abelian₂ P.A (lbPow P.L n)) (abelian₂
    P.A (M.pull ψ.left)) → Out.KTriv B M) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B
    : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (M : LB B.left) (n
    : ℕ), 0 < n → IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsFinite ψ.left → (Out.RelAmple B
    M → Out.RelAmple A (M.pull ψ.left)) ∧ (Out.RelAmple B (lbPow M n) ↔ Out.RelAmple B M) ∧ (Flat
    ψ.left → Surjective ψ.left → Out.RelAmple A (M.pull ψ.left) → Out.RelAmple B
    M) ∧ ∀ M' : LB B.left, M'.IsLB → LBIso M M' → Out.RelAmple B M → Out.RelAmple B M') → (∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (B : Type) [CommRing B] (b : Base l B) (j : KA l →+* B) (S : Scheme.{0}) (s
    : S ⟶ Sp B) (o : Obj D l b s), IsReduced S → j (baseKA l).ρ = b.ρ → j (baseKA
    l).ζ = b.ζ → ∃! f : S ⟶ Xo.X, f ≫ Xo.s = s ≫ spMap j ∧ Nonempty (ObjMap o Xo.univ f)) → ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo
    : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin
    g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z +
    w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro _ laws cube tor hom adjW prim princ amp rep E _ _ _ H D l Xo σ g ty hpq hσ hty D' t P
    ⟨hp, hq, f, ν, htow, hiso, hsim, hζ, ht⟩ hP
  obtain ⟨T, L, u, hA, hdim, hamp, hK, ht₁, ht₂, hker, hact, hW⟩ :=
    exists_triple laws cube tor hom adjW prim princ amp D' ty P hP
  let Q : Out.PolAV (Sp ℂ) :=
    { A := T.G, isAb := hA, g := g, smoothDim := hdim, L := T.PP.L, isLB := T.PP.isLB,
      rigid := ⟨T.PP.rig, T.PP.rigGen⟩, sym := CechPic.sym_of_isSymmetric T.PP T.sym, ample := hamp, ktriv := hK }
  obtain ⟨v, hv, heig⟩ := exists_lieBasis_of_holUnif T.G L g u hA.smooth ht₁ ht₂
  have hmul : ∀ (n : ℕ) a, 0 < n → u.ex ((n : ℂ)⁻¹ • P (n • a)) = 1 := fun n a hn => by
    rw [hker, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    exact ⟨a, rfl⟩
  have hadd : ∀ (n : ℕ) a b, u.ex ((n : ℂ)⁻¹ • P (f n (a + b))) =
      u.ex ((n : ℂ)⁻¹ • P (f n a)) * u.ex ((n : ℂ)⁻¹ • P (f n b)) := fun n a b => by
    rw [map_add (f := _), map_add (f := _), smul_add, u.ex_add]
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨κ, hκ₁, hκ₂, hκ₃⟩ := exists_halfLevel (D := D) l (fun a => u.ex ((l.M : ℂ)⁻¹ • P (f l.M a))) (hadd l.M)
    fun b => by rw [map_nsmul, hmul _ _ hM]
  let b : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  let o : Obj D l b (𝟙 (Sp ℂ)) :=
    { t := T, proper := hA.proper, ample := hamp, ktriv := hK
      eta := κ, eta_add := hκ₁, eta_ker := hκ₂
      etaA := fun a => u.ex ((l.A : ℂ)⁻¹ • P (f l.A a))
      etaA_add := hadd l.A
      etaA_ker := fun a => by rw [map_nsmul, hmul _ _ l.A_pos]
      geom := fun k _ _ x β hx => by
        obtain rfl : x = spMap β := (Category.comp_id x).symm.trans hx
        refine ⟨?_, ?_⟩
        · rw [show b.ρ = H.rt0 from hσ]
          exact detCond_of_eigenbasis lieMult_of_eigenbasis D T ty hty v hv
            (fun i a => heig _ _ (T.act.hom a) (hact a) i) β
        · obtain ⟨I, hI₁, hI₂⟩ := exists_tateIso_of_periods laws E H D D' g ty P Q T.act u.ex f ν hpq hP u.ex_add
            u.ex_onto hker hact hW htow hiso hsim k β
          exact ⟨I, (hI₁ _).trans (congrArg β hζ.symm), fun a => (hI₂ _ a).symm,
            fun a ha => by rw [hκ₃ a ha]; exact (hI₂ _ a).symm⟩ }
  obtain ⟨y, ⟨hy, ⟨m⟩⟩, -⟩ := rep E H D l Xo ℂ b σ (Sp ℂ) (𝟙 _) o inferInstance rfl rfl
  obtain ⟨e, he, hhol, he₁, he₂, he₃⟩ := exists_fibre_unif T Xo.univ.t y m.toSABMap u ht₁ ht₂
  have hlev : ∀ n : ℕ, 0 < n → n ∣ l.M' → ∀ a, u.ex ((n : ℂ)⁻¹ • P (t a)) = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
    rintro n hn ⟨r, hr⟩ a
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left ((Nat.lcm_pos hM l.A_pos).trans_eq hr)
    obtain ⟨c, hc⟩ := htow n r hn hr0 a
    rw [ht, hr, hc, map_add (f := _), smul_add, u.ex_add, hmul _ _ hn, _root_.mul_one]
  refine ⟨y, e, hy.trans (Category.id_comp _), hP, hhol, fun z => (he₁ z).trans (hker z),
    fun a z => he₂ a z _ (hact a z), fun k a a₂ c hk hc => he₃ k _ _ _ (hW k a a₂ c hk hc),
    fun a ha => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · rw [he, hlev _ hM (Nat.dvd_lcm_left _ _), ← hκ₃ a ha]
    exact (m.eta a).symm
  · rw [he, hlev _ l.A_pos (Nat.dvd_lcm_right _ _)]
    exact (m.etaA a).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AmpleDivSec

open LBGerm GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

variable {X : Scheme.{0}}

def invLB (L : LB X) : LB X := ⟨L.1, L.U, fun i j => (L.g i j)⁻¹⟩

theorem isLB_invLB {L : LB X} (hL : L.IsLB) : (invLB L).IsLB := {
  cover := hL.cover
  g_self i := by
    have h := congrArg (·⁻¹) (hL.g_self i)
    simp only [inv_one, ← map_inv] at h
    exact h
  cocycle i j k := by
    have h := congrArg (·⁻¹) (hL.cocycle i j k)
    simp only [mul_inv, ← map_inv] at h
    exact h }

theorem exists_sec_div (L M : LB X) (n t : ℕ) (u : LB.Sec (tw (invLB L) (lbPow M n) (t : ℤ))) :
    ∃ s : (LB.div (lbPow M (n * t)) L).Sec, nonzeroLocus u ≤ nonzeroLocus s := by
  have le : ∀ p : (PUnit → M.ι) × L.ι, powChart M p.1 ⊓ L.U p.2 ≤ L.U p.2 ⊓ powChart M p.1 :=
    fun p y hy => ⟨hy.2, hy.1⟩
  let F : ∀ p : (PUnit → M.ι) × L.ι, Γ(X, powChart M p.1 ⊓ L.U p.2) := fun p =>
    resG X (le p) (show Γ(X, L.U p.2 ⊓ powChart M p.1) from u.f (p.2, p.1))
  have hF : ∀ (y : X) (p : (PUnit → M.ι) × L.ι), y ∈ powChart M p.1 ⊓ L.U p.2 → gs (𝟙 X) y _ (F p) =
      gs (𝟙 X) y _ (u.f (p.2, p.1)) := fun y p hy => gs_res (𝟙 X) y (le p) hy _
  refine ⟨secOfGerm (M := LB.div (lbPow M (n * t)) L) F fun y p q hp hq => ?_, fun y hy => ?_⟩
  · have e₁ := gs_compat u (𝟙 X) y (j := (p.2, p.1)) (j' := (q.2, q.1)) (le p hp) (le q hq)
    have e₂ := TwistGen.gm_tw_g (invLB L) (lbPow M n) t y (p.2, p.1) (q.2, q.1) (le p hp) (le q hq)
    have e₃ := gm_lbPow_g (L := M) n (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₄ := gm_lbPow_g (L := M) (n * t) (𝟙 X) y p.1 q.1 hp.1 hq.1
    have e₅ := gm_div L (lbPow M (n * t)) (𝟙 X) y p q ⟨hp, hq⟩
    have e₆ : gm (𝟙 X) y ((invLB L).U p.2 ⊓ (invLB L).U q.2) ((invLB L).g p.2 q.2) =
        (gm (𝟙 X) y (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2))⁻¹ := map_inv _ _
    rw [e₄] at e₅
    dsimp only at e₂
    rw [e₃, e₆] at e₂
    refine (hF y p hp).trans (e₁.trans (congrArg₂ (· * ·) (e₂.trans ?_) (hF y q hq).symm))
    refine Eq.trans ?_ (congrArg Units.val e₅).symm
    rw [Units.val_mul, pow_mul, _root_.mul_comm]
    simp only [Units.val_pow_eq_pow_val]
  · obtain ⟨p, hp⟩ := exists_chart_of_mem_nonzeroLocus hy
    have hp' : y ∈ powChart M p.2 ⊓ L.U p.1 := ⟨hp.2, hp.1⟩
    refine (mem_nonzeroLocus_iff_isUnit (M := LB.div (lbPow M (n * t)) L) _ (k := (p.2, p.1)) hp').2 ?_
    exact (congrArg IsUnit (hF y (p.2, p.1) hp')).mpr ((mem_nonzeroLocus_iff_isUnit u hp).1 hy)

theorem exists_sec_div_mem {L M : LB X} (hL : L.IsLB) (hM : IsAmpleLB M) (x : X) :
    ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ x ∈ nonzeroLocus s := by
  have := hM.compactSpace
  have := hM.quasiSeparatedSpace
  obtain ⟨n, hn, σ, hx, ha⟩ := hM.exists_affine x
  obtain ⟨V, N, hV, h⟩ := TwistGen.exists_nhds (isLB_invLB hL) (isLB_lbPow hM.isLB n) σ ha x hx
  obtain ⟨u, hu⟩ := h 1
  obtain ⟨s, hs⟩ := exists_sec_div L M n (N + 1) u
  exact ⟨_, s, Nat.mul_pos hn (Nat.succ_pos N), hs (hu hV)⟩

theorem exists_sec_pow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  intro K _ A L M _ ⟨x⟩ hL hM hA
  obtain ⟨a, s, ha, hx⟩ := exists_sec_div_mem hL (isAmpleLB_of_relAmple_of_isAffine A hM hA) x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨a, s, ha, j, fun h => ?_⟩
  rw [h, Scheme.basicOpen_zero] at hj
  exact hj

end GlobalTheory.AmpleDivSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecRelAmplePowDivNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_sec_relAmplePow_div_ne_zero : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left), IsProper A.hom → Nonempty A.left → L.IsLB → M.IsLB → Out.RelAmple A M → ∃ (a : ℕ) (s : (LB.div (lbPow M a) L).Sec), 1 ≤ a ∧ ∃ j, s.f j ≠ 0 := by
  first | exact @GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero | exact GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero | (intros; apply GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExists
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsClopenEqualizer
open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.ClopenEqualizer

theorem exists_isClopen_equalizer {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C)
    (h : a ≫ c = b ≫ c) :
    ∃ (U : Set P), IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  let d := pullback.diagonal c
  let l : P ⟶ pullback c c := pullback.lift a b h
  haveI : IsOpenImmersion d := inferInstance
  haveI : IsClosedImmersion d := inferInstance
  let j : pullback l d ⟶ P := pullback.fst l d
  have hj : j ≫ a = j ≫ b := by
    have h0 : j ≫ l = pullback.snd l d ≫ d := pullback.condition
    have h1 := congrArg (· ≫ pullback.fst c c) h0
    have h2 := congrArg (· ≫ pullback.snd c c) h0
    simp [l, d, pullback.lift_fst, pullback.lift_snd] at h1 h2
    rw [h1, h2]
  refine ⟨Set.range j, ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩, ?_⟩
  intro T y
  constructor
  · intro hy
    have e : y ≫ l = (y ≫ a) ≫ d := by
      apply pullback.hom_ext
      · simp [l, d, pullback.lift_fst]
      · simp [l, d, hy, pullback.lift_snd]
    have e2 : pullback.lift y (y ≫ a) e ≫ j = y := pullback.lift_fst _ _ _
    rintro _ ⟨t, rfl⟩
    refine ⟨pullback.lift y (y ≫ a) e t, ?_⟩
    rw [← Scheme.Hom.comp_apply, e2]
  · intro hy
    rw [← IsOpenImmersion.lift_fac j y hy, Category.assoc, Category.assoc, hj]

end GlobalTheory.ClopenEqualizer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkCover

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem exists_geomPt (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ X), ∀ q, x q = g :=
  ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g,
    fun _ => Scheme.fromSpecResidueField_apply g _⟩

theorem exists_power {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      ∀ (T : Scheme.{0}) (x : T ⟶ S) (u : Fin n → (T ⟶ C)), (∀ j, u j ≫ c = x) →
        ∃ y : T ⟶ P, y ≫ π = x ∧ ∀ j, y ≫ σ j = u j := by
  induction n with
  | zero => exact ⟨S, 𝟙 S, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0,
      fun T x u _ => ⟨x, by simp, fun j => j.elim0⟩⟩
  | succ n ih =>
    obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := ih
    refine ⟨pullback π c, pullback.fst π c ≫ π,
      Fin.cons (pullback.snd π c) (fun j => pullback.fst π c ≫ σ j), inferInstance, inferInstance, fun j => ?_,
      fun T x u hu => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [pullback.condition]
      · simp [h₃]
    · obtain ⟨y, hy, hy'⟩ := h₄ T x (fun j => u j.succ) (fun j => hu _)
      refine ⟨pullback.lift y (u 0) (hy.trans (hu 0).symm), by simp [hy], fun j => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [hy']

theorem exists_eqLocus {P C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (a b : P ⟶ C) (h : a ≫ c = b ≫ c) :
    ∃ U : Set P, IsClopen U ∧ ∀ (T : Scheme.{0}) (y : T ⟶ P), y ≫ a = y ≫ b ↔ Set.range y ⊆ U := by
  first
  | (rename_i h_4 h_5; revert P C S c h_4 h_5 a b h; exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer)
  | exact @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer
  | (apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClopenEqualizer.exists_isClopen_equalizer ..)

theorem exists_distinct {C S : Scheme.{0}} (c : C ⟶ S) [IsFinite c] [Etale c] (n : ℕ) :
    ∃ (P : Scheme.{0}) (π : P ⟶ S) (σ : Fin n → (P ⟶ C)), IsFinite π ∧ Etale π ∧ (∀ j, σ j ≫ c = π) ∧
      (∀ (k : Type) [Field k] (y : Sp k ⟶ P), Function.Injective fun j => y ≫ σ j) ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (u : Fin n → (Sp k ⟶ C)), (∀ j, u j ≫ c = x) → Function.Injective u →
        ∃ y : Sp k ⟶ P, y ≫ π = x := by
  obtain ⟨P, π, σ, h₁, h₂, h₃, h₄⟩ := exists_power c n
  choose U hU hU' using fun a b : Fin n => exists_eqLocus c (σ a) (σ b) ((h₃ a).trans (h₃ b).symm)
  have hV : IsClopen (⋂ a, ⋂ b, ⋂ _ : a ≠ b, (U a b)ᶜ) :=
    isClopen_iInter_of_finite fun a => isClopen_iInter_of_finite fun b =>
      isClopen_iInter_of_finite fun _ => (hU a b).compl
  let V : P.Opens := ⟨_, hV.isOpen⟩
  have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV.isClosed)
  refine ⟨V, V.ι ≫ π, fun j => V.ι ≫ σ j, inferInstance, inferInstance, fun j => by simp [h₃],
    fun k _ y a b e => ?_, fun k _ x u hu hi => ?_⟩
  · by_contra ne
    have q : Sp k := IsLocalRing.closedPoint k
    have m₁ : (y ≫ V.ι) q ∈ U a b := (hU' a b _ (y ≫ V.ι)).1 (by simpa using e) ⟨q, rfl⟩
    have m₂ : (y ≫ V.ι) q ∈ (V : Set P) := by
      rw [← Scheme.Opens.range_ι, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    exact (Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 m₂ a) b) ne) m₁
  · obtain ⟨y, hy, hy'⟩ := h₄ _ x u hu
    have hr : Set.range y ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      refine Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun b => Set.mem_iInter.2 fun ne m => ne (hi ?_)
      rw [← hy', ← hy', hU']
      rintro _ ⟨q', rfl⟩
      rwa [Subsingleton.elim q' q]
    exact ⟨IsOpenImmersion.lift V.ι y hr, by rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem comp_act_natCast (t : SAB H S) {T : Over S} (z : T ⟶ t.G) (n : ℕ) : z ≫ t.act.act (n : 𝓞 E) = z ^ n := by
  induction n with
  | zero =>
    have := t.act.add 0 0
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero, show t.act.act 0 = 1 from left_eq_mul.1 this, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem pow_sq_eq_one (t : SAB H S) {T : Over S} {D : Datum H} {P : Ideal (𝓞 E)} {p i : ℕ} (hp : (p : 𝓞 E) ∈ P)
    {C : Subgroup (T ⟶ t.G)} (h : t.HeckeKer T D P p i C) {z : T ⟶ t.G} (hz : z ∈ C) : z ^ (p ^ 2) = 1 := by
  rw [← comp_act_natCast]
  refine h.2.2.1 hz _ ?_
  rw [Nat.cast_pow, sq]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hp

end GlobalTheory.HkCover


open GlobalTheory.HkCover in
theorem GlobalTheory.exists_cover_lists_heckeSet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → EtSet o.t.G K → HeckeSet D o.t 𝔓 p i K → ∃ (S' : Scheme.{0}) (π : S' ⟶ S) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over S') ⟶ o'.t.G)), IsFinite π ∧ Etale π ∧ Surjective π ∧ Lists (p ^ 2) τ (m.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l P p i S _ s o K hA hE hK
  obtain ⟨C, j, h₁, h₂, h₃, rfl⟩ := hE
  have hn : p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) ≠ 0 := pow_ne_zero _ hA.2.2.1.ne_zero
  have hcard : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ Q : Subgroup (Over.mk x ⟶ o.t.G),
      (∀ z, z ∈ Q ↔ Set.range z.left ⊆ Set.range j.left) ∧ (∀ z ∈ Q, z ^ (p ^ 2) = 1) ∧
      Nat.card Q = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := fun k _ _ x => by
    obtain ⟨Q, hQ, hq⟩ := hK k x
    exact ⟨Q, hQ, fun z hz => pow_sq_eq_one o.t hA.2.2.2.1 hq hz, hq.2.2.2.2.1⟩
  generalize p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) = n at hn hcard ⊢
  have wj : j.left ≫ o.t.G.hom = C.hom := Over.w j
  have rg : ∀ {T : Scheme.{0}} (u : T ⟶ C.left), Set.range (u ≫ j.left) ⊆ Set.range j.left := by
    rintro T u _ ⟨q, rfl⟩
    exact ⟨u q, (Scheme.Hom.comp_apply _ _ _).symm⟩

  have hj : j ^ (p ^ 2) = 1 := by
    have : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
    have := o.proper
    refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_geometricPoints_dense o.t.G.hom _ _
      ((Over.w _).trans (Over.w _).symm) Set.univ dense_univ fun k _ _ x _ => ?_)
    obtain ⟨Q, hQ, hq, -⟩ := hcard k (x ≫ C.hom)
    let x' : Over.mk (x ≫ C.hom) ⟶ C := Over.homMk x rfl
    have e := hq (x' ≫ j) ((hQ _).2 (rg x))
    rw [← MonObj.comp_pow, ← MonObj.comp_one x'] at e
    exact congrArg (fun z => z.left) e
  obtain ⟨S', π, σ, f₁, f₂, f₃, f₄, f₅⟩ := exists_distinct C.hom n
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (π ≫ s) π rfl rfl
    (by simp [spMap]) o
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv m.cart (𝟙_ (Over S'))
  let σ' : Fin n → (Over.mk ((𝟙_ (Over S')).hom ≫ π) ⟶ C) := fun a => Over.homMk (σ a) (by simpa using f₃ a)
  have e : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ m.toSABMap.φ = σ a ≫ j.left := fun a => by
    rw [← e₀, ρ.apply_symm_apply]; rfl
  have wτ : ∀ a, (ρ.symm (σ' a ≫ j)).left ≫ o'.t.G.hom = 𝟙 S' := fun a => Over.w _
  refine ⟨S', π, o', m, fun a => ρ.symm (σ' a ≫ j), f₁, f₂, ⟨fun g => ?_⟩, fun a => ?_, ?_, fun k _ _ y a b hab => ?_⟩
  · obtain ⟨k, _, _, x, hx⟩ := exists_geomPt S g
    obtain ⟨Q, hQ, -, hc⟩ := hcard k x
    have en : Q ≃ Fin n := Nat.equivFinOfCardPos (hc ▸ hn) |>.trans (finCongr hc)
    have : ∀ a : Fin n, ∃ u : Sp k ⟶ C.left, u ≫ j.left = (en.symm a).1.left := fun a =>
      GlobalTheory.exists_lift_closedImmersion_of_dense j.left _ Set.univ dense_univ
        fun q _ => (hQ _).1 (en.symm a).2 ⟨q, rfl⟩
    choose u hu using this
    obtain ⟨y, hy⟩ := f₅ k x u (fun a => by rw [← wj, ← Category.assoc, hu]; exact Over.w (en.symm a).1)
      fun a b hab => en.symm.injective (Subtype.ext (Over.OverMorphism.ext (by rw [← hu, ← hu, hab])))
    have q : Sp k := IsLocalRing.closedPoint k
    exact ⟨y q, by rw [← Scheme.Hom.comp_apply, hy, hx]⟩
  · rw [← map_pow, ← MonObj.comp_pow, hj, MonObj.comp_one, map_one]
  · refine Set.Subset.antisymm (fun g hg => ?_) (Set.iUnion_subset fun a => ?_)
    · obtain ⟨k, _, _, w, hw⟩ := exists_geomPt _ g
      obtain ⟨Q, hQ, -, hc⟩ := hcard k ((w ≫ o'.t.G.hom) ≫ π)
      let z : Fin n → Q := fun a => ⟨Over.homMk (((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left)
        (by simp [wj, f₃]), (hQ _).2 (rg _)⟩
      have zi : Function.Injective z := fun a b hab => f₄ k (w ≫ o'.t.G.hom)
        ((cancel_mono j.left).1 (congrArg (fun z : Q => z.1.left) hab))
      have : Finite Q := Nat.finite_of_card_ne_zero (hc ▸ hn)
      have zb := (Nat.bijective_iff_injective_and_card z).2 ⟨zi, by simp [hc]⟩
      obtain ⟨a, ha⟩ := zb.2 ⟨Over.homMk (w ≫ m.toSABMap.φ) (by simpa using congrArg (w ≫ ·) m.cart.1.w), (hQ _).2 (by
        rintro _ ⟨q, rfl⟩
        have : (w ≫ m.toSABMap.φ) q ∈ Set.range j.left := by rw [Scheme.Hom.comp_apply, hw]; exact hg
        exact this)⟩
      have ha' : ((w ≫ o'.t.G.hom) ≫ σ a) ≫ j.left = w ≫ m.toSABMap.φ := congrArg (fun z : Q => z.1.left) ha
      have hw' : (w ≫ o'.t.G.hom) ≫ (ρ.symm (σ' a ≫ j)).left = w := m.cart.1.hom_ext
        (by rw [Category.assoc, ← ha', Category.assoc _ (σ a)]; exact congrArg (_ ≫ ·) (e a))
        (by rw [Category.assoc, wτ]; exact Category.comp_id _)
      have q : Sp k := IsLocalRing.closedPoint k
      refine Set.mem_iUnion.2 ⟨a, (w ≫ o'.t.G.hom) q, ?_⟩
      rw [← hw q]
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun v : Sp k ⟶ _ => v q) hw')
    · rintro _ ⟨q, rfl⟩
      have := rg (σ a) ⟨q, rfl⟩
      rw [← e, Scheme.Hom.comp_apply] at this
      exact this
  · refine f₄ k y ((cancel_mono j.left).1 ?_)
    have := congrArg (· ≫ m.toSABMap.φ) hab
    simpa only [Category.assoc, e] using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetEtaleLevelStructureExistsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_set_etale_level_structure_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → EtSet o.t.G K → HeckeSet D o.t 𝔓 p i K → ∃ (S' : Scheme.{0}) (π : S' ⟶ S) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (τ : Fin (p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))) → (𝟙_ (Over S') ⟶ o'.t.G)), IsFinite π ∧ Etale π ∧ Surjective π ∧ Lists (p ^ 2) τ (m.toSABMap.φ ⁻¹' K) := by
  first | exact @GlobalTheory.exists_cover_lists_heckeSet | exact GlobalTheory.exists_cover_lists_heckeSet | (intros; apply GlobalTheory.exists_cover_lists_heckeSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndSurjectiveOfFormIs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.FormFinite

open GlobalTheory.CechPic GlobalTheory.AmpleStabFinite

theorem lam_inv_eq {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (m l : CechPic.Pic A.left) (s : A ⟶ A)
    [IsMonHom s] (h : ∀ u v : T ⟶ A, lam m u v = lam l u (v ≫ s)) {x y : T ⟶ A} (e : x ≫ s = y ≫ s) :
    lam m x⁻¹ x = lam m y y⁻¹ := by
  rw [h, e, ← h, lam_comm, h, GrpObj.inv_comp, e, ← GrpObj.inv_comp, ← h]

theorem isFinite_of_lam_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    {M : LB A.left} (hM : IsAmpleLB M) (l : CechPic.Pic A.left) (s : A ⟶ A) [IsMonHom s]
    (h : ∀ (T : Over (Sp K)) (u v : T ⟶ A), lam (cls M hM.isLB) u v = lam l u (v ≫ s)) : IsFinite s.left := by
  obtain ⟨n, -, N, t, hc, ha⟩ := hM.exists_cover
  have : IsProper (s.left ≫ A.hom) := by rw [Over.w s]; infer_instance
  have : IsProper s.left := .of_comp _ A.hom
  suffices LocallyQuasiFinite s.left from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun z => ?_
  rcases Set.eq_empty_or_nonempty (s.left ⁻¹' {z}) with h0 | ⟨a, hz⟩
  · rw [h0]; exact Set.finite_empty
  let k : Type := A.left.residueField a
  let y₀ : Spec (CommRingCat.of k) ⟶ A.left := A.left.fromSpecResidueField a
  let P : Over (Sp K) := Over.mk (y₀ ≫ A.hom)
  let y : P ⟶ A := Over.homMk y₀ rfl
  let π : pullback s.left (y₀ ≫ s.left) ⟶ A.left := pullback.fst _ _
  let q : pullback s.left (y₀ ≫ s.left) ⟶ Spec (CommRingCat.of k) := pullback.snd _ _
  have w : π ≫ s.left = q ≫ y₀ ≫ s.left := pullback.condition
  let F : Over (Sp K) := Over.mk (π ≫ A.hom)
  let x : F ⟶ A := Over.homMk π rfl
  let r : F ⟶ P := Over.homMk q (by
    change q ≫ y₀ ≫ A.hom = π ≫ A.hom
    rw [← Over.w s, reassoc_of% w])
  have : IsAffineHom (y₀ ≫ s.left) := .of_comp _ A.hom
  have : IsAffineHom π := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
    (IsPullback.of_hasPullback s.left (y₀ ≫ s.left)).flip this
  have key := lam_inv_eq _ l s (h F) (x := x) (y := r ≫ y) (Over.OverMorphism.ext w)
  have triv : ∀ (b : P ⟶ A) (c : CechPic.Pic A.left), CechPic.pull (r ≫ b).left c = 0 := fun b c => by
    rw [Over.comp_left, pull_comp, pull_spec_local (K := k) b.left, map_zero]
  have one : ∀ c : CechPic.Pic A.left, CechPic.pull (1 : F ⟶ A).left c = 0 := fun c => by
    rw [← MonObj.comp_one r, triv]
  simp only [lam, inv_mul_cancel, ← GrpObj.comp_inv, ← MonObj.comp_mul, one, triv] at key
  have : CompactSpace ↥(pullback s.left (y₀ ≫ s.left)) := QuasiCompact.compactSpace_of_compactSpace q
  have : (pullback s.left (y₀ ≫ s.left)).IsQuasiAffine := quasiAffine_of_pull_add π (x⁻¹).left
    (isLB_lbPow hM.isLB n) t hc ha (by
      have e : CechPic.pull x.left (cls M hM.isLB) + CechPic.pull (x⁻¹).left (cls M hM.isLB) = 0 := by
        linear_combination (norm := abel) - key
      change CechPic.pull x.left _ + CechPic.pull (x⁻¹).left _ = 0
      rw [cls_lbPow hM.isLB, map_nsmul, map_nsmul, ← nsmul_add, e, nsmul_zero])
  have : IsAffine (pullback s.left (y₀ ≫ s.left)) := isAffine_of_quasiAffine q
  have : IsFinite q := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : (Set.univ : Set ↥(pullback s.left (y₀ ≫ s.left))).Finite :=
    (q.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  refine (hfin.image π).subset fun b hb => ?_
  have e : s.left b = (y₀ ≫ s.left) (IsLocalRing.closedPoint k) := by
    have e₀ : y₀ (IsLocalRing.closedPoint k) = a := Scheme.fromSpecResidueField_apply a _
    exact (show s.left b = z from hb).trans ((show s.left a = z from hz).symm.trans (congrArg s.left e₀).symm)
  obtain ⟨c, hc, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := s.left) (g := y₀ ≫ s.left) b _ e
  exact ⟨c, trivial, hc⟩

theorem isFinite_and_surjective_of_formIs : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → Out.RelAmple P.A M → FormIs P M s → IsFinite s.left ∧ Surjective s.left := by
  intro _ _ K _ _ P M s hM hA ⟨hs, H⟩
  have := P.isAb.proper
  have := P.isAb.comm
  have e := (cls_eq_iff (LB.isLB_linComb hM _ _) (LB.isLB_linComb P.isLB _ _)).2 H
  have e' := (cls_cube_two hM _ _ _).symm.trans (e.trans (cls_cube_two P.isLB _ _ _))
  have hf : IsFinite s.left :=
    isFinite_of_lam_eq (isAmpleLB_of_relAmple_of_isAffine P.A hM hA) (cls P.L P.isLB) s fun T u v => by
      simpa only [pull_lam, lift_fst, lift_snd, lift_snd_assoc] using congrArg (CechPic.pull (lift u v).left) e'
  exact ⟨hf, (flat_and_surjective_of_isFinite_abelianEnd
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K P.A P.isAb s hs hf).2⟩

end GlobalTheory.FormFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsMemNonzeroLocus
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionDense

open GoodPoint

theorem exists_sec_lPow {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (T : Over S) (k : ℕ)
    (s : (lbPow L k).Sec) : ∃ s' : LB.Sec (LPow A L k T), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → (IsUnit (powVal s' r z J) ↔ (r ≫ (snd T A).left) z ∈ nonzeroLocus s) := by
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => (k : ℤ))
    (fun U _ h => by simp [Fintype.prod_sum_type, -Over.snd_left])
    (pullMulSec (L := L) (φ := fun _ : PUnit => 𝟙 A.left) (ε := fun _ => (k : ℤ)) s (snd T A).left
      (LB.oneGen L (Y := (T ⊗ A).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)).symm))
  refine ⟨s', fun Z r z J hJ => ?_⟩
  have e := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ _ r z hJ)
  refine (iff_of_eq (congrArg IsUnit e)).trans ?_
  rw [Units.isUnit_mul_units]
  exact (mem_nonzeroLocus_iff_pull s _ z (hJ.mem (fun _ : PUnit => 𝟙 A.left) _)).symm

variable {K : Type} [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K)))

theorem exists_mem_nonzeroLocus (hI : IrredSt) (hK : KerPowSt) (k : ℕ) (hk : 4 ≤ k) (hkK : (k : K) ≠ 0)
    (B : Set (baseOver (Spec (CommRingCat.of K)) ⟶ P.A)) (hB : ∀ w, w ^ k = 1 → ∀ b ∈ B, w * b ∈ B)
    (s t : (lbPow P.L k).Sec) (x : P.A.left) (hx : x ∈ nonzeroLocus s)
    (b : baseOver (Spec (CommRingCat.of K)) ⟶ P.A) (hb : b ∈ B)
    (p : (baseOver (Spec (CommRingCat.of K))).left) (ht : b.left p ∈ nonzeroLocus t) :
    ∃ b' ∈ B, ∃ p', b'.left p' ∈ nonzeroLocus s := by
  by_contra hcon
  obtain ⟨s', hs'⟩ := exists_sec_lPow P.isLB (baseOver _) k s
  obtain ⟨t', ht'⟩ := exists_sec_lPow P.isLB (baseOver _) k t
  rcases hI K P k (Or.inr hk) hkK (vanishing P.L _ B)
    (fun θ s s' h hsB q hq y J hJ => by
      obtain ⟨c, hc⟩ := powVal_act h (ptSecT P.A q).left hJ
      rw [← Over.comp_left, ptSecT_translT] at hc
      refine (congrArg (· ∈ IsLocalRing.maximalIdeal _) hc).mpr
        (Ideal.mul_mem_left _ _ (hsB _ (hB _ ?_ q hq) y J hJ))
      exact (hK _ P k (by omega) _ θ.pt).1 fun p => ⟨⊤, trivial, exists_isGen_pull _ θ.φ θ.isGen _⟩) with h | h
  · have hm : SecM.ofSec P.A s' ∈ vanishing P.L _ B := fun q hq y J hJ hu => by
      have := (hs' _ _ y J hJ).1 hu
      rw [← Over.comp_left, ptSecT_snd] at this
      exact hcon ⟨q, hq, y, this⟩
    rw [h, Submodule.mem_bot] at hm
    choose J hJ using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ x)
    have hu := (hs' _ (unitInv P.A).left x J hJ).2 (by rw [← Over.comp_left, unitInv_snd]; exact hx)
    have e : powVal s' (unitInv P.A).left x J = 0 :=
      (congrArg (gs _ x _) (congrFun (congrArg Subtype.val hm) _)).trans (gs_zero _ x _)
    rw [e] at hu
    exact not_isUnit_zero hu
  · choose J hJ using fun χ : (baseOver (Spec (CommRingCat.of K))).left ⟶ P.A.left => exists_chart P.isLB (χ p)
    have hm : SecM.ofSec P.A t' ∈ vanishing P.L _ B := by rw [h]; trivial
    exact hm b hb p J hJ ((ht' _ _ p J hJ).2 (by rw [← Over.comp_left, ptSecT_snd]; exact ht))

theorem dense_torsion [CharZero K] (hI : IrredSt) (hK : KerPowSt) :
    Dense (⋃ x ∈ {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P.A | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}, Set.range x.left) := by
  have := P.isAb.comm
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ => ?_
  obtain ⟨n, hn, s, hs, hle, -⟩ := hA.exists_affine_le (x := x) (U := ⟨U, hU⟩) hx
  let p : (baseOver (Spec (CommRingCat.of K))).left := IsLocalRing.closedPoint K
  obtain ⟨m, hm, t, ht, -⟩ := hA.exists_affine ((1 : baseOver (Spec (CommRingCat.of K)) ⟶ P.A).left p)
  have e₁ := nonzeroLocus_secPow s (k := m * 4) (by omega)
  have e₂ := nonzeroLocus_secPow t (k := n * 4) (by omega)
  have hk : 4 ≤ n * (m * 4) := by nlinarith [Nat.mul_pos hn hm]
  obtain ⟨b, hb, q, hq⟩ := exists_mem_nonzeroLocus P hI hK (n * (m * 4)) hk (Nat.cast_ne_zero.2 (by omega))
    {x | ∃ n : ℕ, 0 < n ∧ x ^ n = 1} (fun w hw b ⟨l, hl, hb⟩ => ⟨n * (m * 4) * l, Nat.mul_pos (by omega) hl, by
      rw [mul_pow, pow_mul w, hw, one_pow, mul_comm _ l, pow_mul, hb, one_pow, _root_.one_mul]⟩)
    (secPow s (m * 4)) (secCast (by ring) (secPow t (n * 4))) x (e₁.ge hs) 1 ⟨1, one_pos, one_pow _⟩ p (e₂.ge ht)
  exact ⟨b.left q, hle (e₁.le hq), Set.mem_iUnion₂.2 ⟨b, hb, q, rfl⟩⟩

end GlobalTheory.TorsionDense
end
end
