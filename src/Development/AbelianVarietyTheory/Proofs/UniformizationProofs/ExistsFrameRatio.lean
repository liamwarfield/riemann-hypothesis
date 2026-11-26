module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

omit [IsDomain R] in
theorem pt_eq (z z' : (TF (R := R) F).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum F) z z'

def cstH (z : (TF (R := R) F).left) : F →+* (TF (R := R) F).left.presheaf.stalk z :=
  ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

omit [IsDomain R] in
theorem cst_eq (z : (TF (R := R) F).left) (x : F) : cst F z x = cstH z x :=
  gs_eq (𝟙 _) z ⊤ trivial _

omit [IsDomain R] in
theorem cstH_surj (z : (TF (R := R) F).left) : Function.Surjective (cstH (R := R) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TF (R := R) F).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom hx⟩

omit [IsDomain R] in
theorem cstH_inj (z : (TF (R := R) F).left) : Function.Injective (cstH (R := R) z) :=
  (cstH (R := R) z).injective

omit [IsDomain R] in
theorem exists_pt : Nonempty (TF (R := R) F).left := ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)⟩

theorem exists_good' {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) : ∃ J, Good L z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨I, hI⟩

def trU {X Z : Scheme.{0}} (L : LB X) (z : Z) (J J' : (Z ⟶ X) → L.ι) (ψ : Z ⟶ X) : (Z.presheaf.stalk z)ˣ :=
  gm ψ z (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))

theorem val_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    val t r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k) * val t r z J' :=
  gen_trans ht r z (hJ.mem φ r) (hJ'.mem φ r)

theorem sval_tr {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L z J') :
    sval s r z J = (∏ k, trU L z J J' (r ≫ φ k) ^ ε k).val * sval s r z J' :=
  sec_trans s r z (hJ.mem φ r) (hJ'.mem φ r)

theorem exists_gen_pt {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (y₀ : Y) (hY : ∀ y : Y, y = y₀) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨J, hJ⟩ := exists_good' hL y₀
  let j₀ : K → L.ι := fun k => J (𝟙 Y ≫ φ k)
  have h₀ : ∀ y : Y, (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L φ j₀ := fun y => by
    rw [hY y]; exact hJ.mem φ (𝟙 Y)
  have le : ∀ j, LB.wchart L φ j ≤ LB.wchart L φ j ⊓ LB.wchart L φ j₀ := fun j y hy => ⟨hy, h₀ y⟩
  refine ⟨⟨fun j => res (le j) ((LB.LinComb L φ ε).g j j₀)⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have v : ∀ j, y ∈ LB.wchart L φ j → gm (𝟙 Y) y (LB.wchart L φ j) (res (le j) ((LB.LinComb L φ ε).g j j₀)) =
      trF φ ε (𝟙 Y) y j j₀ := fun j hj =>
    (gm_res (𝟙 Y) y (le j) hj _).trans (gm_linComb L φ ε (𝟙 Y) y j j₀ hj (h₀ y))
  refine ((gm_res (𝟙 Y) y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (v j' hy.2)))).symm)
  exact (trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (h₀ y)).symm

theorem prod_line (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) {U : Type} [CommGroup U]
    (h : ((TF (R := R) F).left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.lineφ D F b i) ^ DegPre.lineε k i = h (1 : TF (R := R) F ⟶ D.P.A).left ^ k * (h b.left ^ k)⁻¹ := by
  rw [Fin.prod_univ_two]
  show h (1 : TF (R := R) F ⟶ D.P.A).left ^ (k : ℤ) * h b.left ^ (-(k : ℤ)) = _
  rw [zpow_neg, zpow_natCast, zpow_natCast]

theorem isCoef_unique {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s} {x y : F}
    (hx : IsCoef k g w χ s x) (hy : IsCoef k g w χ s y) : x = y := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB z
  have e := (hx z J hJ).trans (hy z J hJ).symm
  rw [← Units.val_pow_eq_pow_val, Units.mul_left_inj, cst_eq, cst_eq] at e
  exact cstH_inj z e

theorem coef_eq {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s : Fam D F k} {x : F}
    (hx : IsCoef k g w χ (s.s χ) x) : coef s g w χ = x :=
  isCoef_unique (Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) ⟨x, hx⟩) hx

theorem exists_isCoef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s) :
    ∃ x, IsCoef k g w χ s x := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨x, hx⟩ := cstH_surj z (sval s (lift (𝟙 (TF (R := R) F)) g.b).left z J' * (val (g.s χ) (𝟙 _) z J').val *
    (val w (𝟙 _) z J').val * ((rigV D (TF (R := R) F).hom z J' ^ k)⁻¹).val)
  refine ⟨x, fun z' J hJ => ?_⟩
  obtain rfl := pt_eq z z'
  have a₁ := sval_tr s (lift (𝟙 (TF (R := R) F)) g.b).left hJ hJ'
  have a₂ := val_tr (g.isGen χ) (𝟙 _) hJ hJ'
  have a₃ := val_tr hw (𝟙 _) hJ hJ'
  have a₄ : rigV D (TF (R := R) F).hom z J = trU D.P.L z J J' (1 : TF (R := R) F ⟶ D.P.A).left *
      rigV D (TF (R := R) F).hom z J' := by
    refine (val_tr (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig_gen
      (TF (R := R) F).hom hJ hJ').trans ?_
    rw [Fintype.prod_unique, zpow_one]; rfl
  rw [prod_fam D F (lift (𝟙 (TF (R := R) F)) g.b) χ k (trU D.P.L z J J'), lift_snd] at a₁
  simp only [Category.id_comp] at a₂ a₃
  rw [prod_gt g.b χ (trU D.P.L z J J')] at a₂
  rw [prod_line k g.b (trU D.P.L z J J')] at a₃
  rw [cst_eq, hx, a₁, a₂, a₃, a₄, ← Units.val_pow_eq_pow_val, mul_comm (Units.val _) (sval _ _ _ _)]
  simp only [_root_.mul_assoc, ← Units.val_mul]
  congr 2
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  module

theorem isCoef_coef {k : ℕ} (g : GtPtF D F) {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) (s : Fam D F k) :
    IsCoef k g w χ (s.s χ) (coef s g w χ) :=
  Classical.epsilon_spec (p := IsCoef k g w χ (s.s χ)) (exists_isCoef g hw χ _)

theorem sval_lin {k : ℕ} (b : TF (R := R) F ⟶ D.P.A) (s s' : Fam D F k) (c : F) (χ : D.X) {z : (TF (R := R) F).left} {J}
    (hJ : Good D.P.L z J) : sval ((c • s + s').s χ) (lift (𝟙 (TF (R := R) F)) b).left z J =
      cst F z c * sval (s.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J +
        sval (s'.s χ) (lift (𝟙 (TF (R := R) F)) b).left z J := by
  have hm := hJ.mem (DegPre.famφ D F χ) (lift (𝟙 (TF (R := R) F)) b).left
  refine (gs_add _ z _ hm _ _).trans (congrArg₂ (· + ·) ((gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·) ?_ rfl)) rfl)
  refine (gs_res _ z le_top hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, lift_fst]; rfl

theorem exists_frame_ratio {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} {w w' : Frm D F k b} (hw : w.IsGen) (hw' : w'.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J', hJ'⟩ := exists_good' D.P.isLB z
  obtain ⟨c, hc⟩ := cstH_surj z (val w' (𝟙 _) z J' * (val w (𝟙 _) z J')⁻¹).val
  refine ⟨c, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hc
    exact Units.ne_zero _ hc.symm
  · obtain rfl := pt_eq z z'
    rw [cst_eq, hc, val_tr hw (𝟙 _) hJ hJ', val_tr hw' (𝟙 _) hJ hJ', ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem coef_basic : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F), (∃ w : Frm D F k g.b, w.IsGen) ∧ (g.b = 1 → ∃ w : Frm D F k g.b, FrmOne w) ∧ ∀ w : Frm D F k g.b, w.IsGen → (∀ χ s, ∃! x, IsCoef k g w χ s x) ∧ (∀ (s s' : Fam D F k) (c : F) χ, coef (c • s + s') g w χ = c * coef s g w χ + coef s' g w χ) ∧ (∀ w' : Frm D F k g.b, w'.IsGen → ∃ c : F, c ≠ 0 ∧ (∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) ∧ ∀ (s : Fam D F k) χ, coef s g w' χ = c * coef s g w χ) ∧ ∀ (t : Multiplicative D.X →* Fˣ) (g₀ g' : GtPtF D F) (w' : Frm D F k g'.b), IsTor t g₀ → g.IsAdd g₀ g' → (∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J) → ∀ (s : Fam D F k) χ, coef s g' w' χ = (t (Multiplicative.ofAdd χ)).val * coef s g w χ := by
  intro R _ _ D F _ _ k g
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  refine ⟨exists_gen_pt D.P.isLB z₀ (fun y => pt_eq y z₀) _ _, fun hb => ?_, fun w hw => ⟨fun χ s => ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F g.b) (ε' := DegPre.lineε k)
      (fun U _ h => by rw [prod_line, hb, mul_inv_cancel]; exact Fintype.prod_empty _)
      (LB.oneGen D.P.L (Y := (TF (R := R) F).left))
      (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
    exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (val_one _)⟩
  · obtain ⟨x, hx⟩ := exists_isCoef g hw χ s
    exact ⟨x, hx, fun y hy => isCoef_unique hy hx⟩
  · intro s s' c χ
    refine coef_eq fun z J hJ => ?_
    have a := isCoef_coef g hw χ s z J hJ
    have a' := isCoef_coef g hw χ s' z J hJ
    rw [sval_lin g.b s s' c χ hJ]
    simp only [cst_eq, map_add (f := _), map_mul] at a a' ⊢
    linear_combination cstH z c * a + a'
  · intro w' hw'
    obtain ⟨c, hc, hv⟩ := exists_frame_ratio hw hw'
    refine ⟨c, hc, hv, fun s χ => coef_eq fun z J hJ => ?_⟩
    have a := isCoef_coef g hw χ s z J hJ
    rw [hv z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z c * a
  · intro t g₀ g' w' ht hadd hv s χ
    obtain ⟨hb, hs⟩ := (isAdd_iff _ _ _).1 hadd
    refine coef_eq fun z J hJ => ?_
    have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
    have a := isCoef_coef g hw χ s z J hJ
    have e := hs χ z J hJ
    rw [ht.1, _root_.mul_one] at hb
    have e₀ : th D z J (cP D _ χ) g.b g₀.b = 1 := by rw [ht.1, C.face₃]
    rw [e₀, _root_.mul_one] at e
    have e₁ : lift (𝟙 (TF (R := R) F)) g'.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
    rw [hv z J hJ, e, e₁, Units.val_mul, ht.2 χ z J hJ]
    simp only [cst_eq, map_mul] at a ⊢
    linear_combination cstH z (t (Multiplicative.ofAdd χ)).val * a

end GlobalTheory.UT.CoefBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TauPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem gm_injective_of_dense {Y Z : Scheme.{0}} [IsReduced Y] (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V) (V : Y.Opens) (hV : h z ∈ V) :
    Function.Injective (gm h z V) := by
  intro a b hab
  apply Units.ext
  have e := congrArg Units.val hab
  rw [gm_val h z V hV, gm_val h z V hV, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hm : z ∈ h ⁻¹ᵁ Y.basicOpen (a.val - b.val) :=
    hd _ (by
      by_contra hn
      exact hne (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _ |>.1 hn))
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ z hV, e] at hm
  exact not_isUnit_zero hm

theorem corr_of_dense {X Y Z : Scheme.{0}} [IsReduced Y] [X.IsSeparated] {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V)
    (H : ∀ J, Good L z J → val t h z J = val t' h z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have dom : IsDominant h := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨h z, hd ⟨U, hU⟩ hne, z, rfl⟩⟩
  refine unit_ext fun y hy => congrArg (gm (𝟙 Y) y _) ?_
  have hz : h z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hd _ ⟨y, hy⟩
  apply gm_injective_of_dense h z hd _ hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (Sum.elim (fun k => h ≫ φ k) (fun k => h ≫ φ' k)) (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b (ext_of_isDominant h e), c₃ a b (ext_of_isDominant h e),
      (c₃ b a (ext_of_isDominant h e.symm)).symm, c₂ a b (ext_of_isDominant h e)]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])
  have := H J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  exact (gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm)

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (V : (Spec (CommRingCat.of R)).Opens)
    (hV : (V : Set (Spec (CommRingCat.of R))).Nonempty) : jK R z ∈ V := by
  obtain ⟨x, hx⟩ := hV
  have hz : (jK R z).asIdeal ≤ x.asIdeal := by
    have h0 : PrimeSpectrum.asIdeal (R := FractionRing R) z = ⊥ := @Ideal.eq_bot_of_prime _ _ _ (PrimeSpectrum.isPrime _)
    intro r hr
    have h1 : algebraMap R (FractionRing R) r ∈ PrimeSpectrum.asIdeal (R := FractionRing R) z := hr
    rw [h0, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
    rw [h1]; exact zero_mem _
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 hz).mem_open V.isOpen hx

section OnW

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens}

theorem val_tau {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) (a b : D.X) :
    val (D.tau a b) r z J =
      val (D.psi (a + b)) r z J * (val (D.psi a) r z J)⁻¹ * (val (D.psi b) r z J)⁻¹ * (val D.rigK r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem val_tauW (ψW : PsiOn D W) {Z : Scheme.{0}} (r : Z ⟶ (TW W).left) {z : Z} {J} (hJ : Good D.P.L z J)
    (a b : D.X) : val (ψW.tau a b) r z J =
      val (ψW.psi (a + b)) r z J * (val (ψW.psi a) r z J)⁻¹ * (val (ψW.psi b) r z J)⁻¹ * (val (D.rigW W) r z J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem tauW_corr (hB : D.TauBimult) (ψW : PsiOn D W) (hW : (W : Set (Spec (CommRingCat.of R))).Nonempty)
    (a a' b : D.X) : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau (a + a') b)
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (cP D (TW W) a) (lift (cP D (TW W) a') (cP D (TW W) b))).left))
      (LB.mulGen D.P.L _ _ _ _ (ψW.tau a b) (ψW.tau a' b)) := by
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨lam, hl⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift _ (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact jK_mem y W hW), IsOpenImmersion.lift_fac _ _ _⟩
  have hκ : (lam ≫ jK R ∣_ W) ≫ W.ι = jK R := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hl, Category.id_comp]
  let κ : TK R ⟶ TW W := Over.homMk (lam ≫ jK R ∣_ W) hκ
  obtain ⟨z⟩ : Nonempty (TK R).left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R)))
  have red : IsReduced (TW W).left := inferInstanceAs (IsReduced W.toScheme)
  refine corr_of_dense D.P.isLB κ.left z (fun V hV => ?_) fun J hJ => ?_
  · have h₁ : jK R z ∈ W.ι ''ᵁ V := jK_mem z _ (hV.image _)
    obtain ⟨y, hy, e⟩ := h₁
    have e' : W.ι y = W.ι (κ.left z) := e.trans (congrArg (fun q => q z) hκ).symm
    rw [← W.ι.isOpenEmbedding.injective e']
    exact hy
  · have vψ : ∀ χ, val (ψW.psi χ) κ.left z J = val (D.psi χ) (𝟙 _) z J := fun χ => by
      have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq χ) lam).trans (val_pull hJ _ _ _))
      rw [hl] at this
      exact this
    have vρ : val (D.rigW W) κ.left z J = val D.rigK (𝟙 _) z J := by
      refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [Category.id_comp]
      exact congrArg (fun q => val D.rig q z J) hκ
    have vτ : ∀ a b, val (ψW.tau a b) κ.left z J = val (D.tau a b) (𝟙 _) z J := fun a b => by
      rw [val_tauW ψW _ hJ, val_tau _ hJ, vψ, vψ, vψ, vρ]
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (hB a a' b) (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
    rw [vτ, vτ, vτ, ← e]
    refine congrArg₂ (· * ·) rfl ((val_cub D.cub κ hJ _ _ _).trans (Eq.trans ?_
      (val_cub D.cub (𝟙 (TK R)) hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm))
    simp only [comp_cP]

theorem tauW_mul (hB : D.TauBimult) (ψW : PsiOn D W) {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TW W)
    {z : T.left} {J} (hJ : Good D.P.L z J) (a a' b : D.X) :
    val (ψW.tau (a + a') b) κ.left z J * th D z J (cP D T a) (cP D T a') (cP D T b) =
      val (ψW.tau a b) κ.left z J * val (ψW.tau a' b) κ.left z J := by
  have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (tauW_corr hB ψW ⟨_, (κ.left z).2⟩ a a' b) κ.left).trans
    (val_mul hJ _ _ _))
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) this
  refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ a) (cP D _ a') (cP D _ b)).symm
  rw [comp_cP, comp_cP, comp_cP]

end OnW

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem val_psiW (hD : IsPullDeg φ D D') {y : (TK R').left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J')
    (χ : D'.X) : val (hD.psiW.psi (hD.xe χ)) hD.g y J =
      (gw hD.w (D'.xK χ) y (J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))) (J' (D'.xK χ)))⁻¹ *
        val (D'.psi χ) (𝟙 _) y J' := by
  obtain ⟨b, hb, hc⟩ := hD.psi_pr χ
  have e₂ := (val_corr hJ hc (𝟙 _)).trans (val_pull hJ _ _ _)
  rw [Category.id_comp] at e₂
  rw [← e₂]
  obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK χ ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = J' (D'.xK χ) := ⟨_, rfl⟩
  rw [← hp, ← hq, val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp]),
    val_of (D'.psi χ) _ y J' (fun _ => q) (fun _ => by rw [Category.id_comp, hq])]
  have m₁ : (𝟙 (TK R').left : _ ⟶ _) y ∈ D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U
      (fun _ => p) ⊓ D'.P.L.U q) := ⟨mem_pull.2 (hp ▸ hJ _), hq ▸ hJ' _⟩
  have e₁ := congrArg (gm (𝟙 (TK R').left) y
    (D'.xK χ ⁻¹ᵁ ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q)))
    (hb (fun _ => p) q)
  refine (gm_res _ y _ m₁ _).symm.trans (e₁.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans ((congrArg (· ^ (-1 : ℤ)) (gm_pull _ (D'.xK χ) y
      ((D.P.L.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))).U (fun _ => p) ⊓ D'.P.L.U q) m₁ _)).trans ?_))
      (gm_res _ y _ m₁ _))))
  rw [Category.id_comp]
  exact zpow_neg_one _

set_option maxHeartbeats 1000000 in
theorem tauBimult_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') (hB : D.TauBimult) : D'.TauBimult := by
  intro a a' b
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ₀ using fun χ : (TK R').left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ : Good D.P.L y J := hJ₀
  have gp := pull_grp hD
  let Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TW hD.W := Over.homMk hD.g hD.g_comm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ Φ = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw hD.w x.left y (J (x.left ≫ Φ)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw hD.w q y (J (q ≫ Φ)) (J' q))) rfl)
  have vψ : ∀ χ, val (hD.psiW.psi (hD.xe χ)) hD.g y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' :=
    fun χ => val_psiW hD hJ hJ' χ
  have vρ : val (D.rigW hD.W) hD.g y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le Φ (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
    have a₂ : ((TK R').hom ≫ specOf φ) ≫ eSec D.P.A = (1 : TK R' ⟶ D'.P.A).left ≫ Φ :=
      congrArg (fun q => q.left) (map_one (pushHom gp (TK R'))).symm
    have e := pm _ (TK R').hom y (fun _ => J ((1 : TK R' ⟶ D'.P.A).left ≫ Φ))
      (fun _ => J' (1 : TK R' ⟶ D'.P.A).left) (fun _ => hJ _) (fun _ => hJ' _)
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : hD.g ≫ (toUnit (TW hD.W)).left = (TK R').hom ≫ specOf φ := hD.g_comm
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans e
  have key : val (hD.psiW.tau (hD.xe a + hD.xe a') (hD.xe b)) hD.g y J *
      θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      val (hD.psiW.tau (hD.xe a) (hD.xe b)) hD.g y J * val (hD.psiW.tau (hD.xe a') (hD.xe b)) hD.g y J :=
    tauW_mul hB hD.psiW κ hJ _ _ _
  rw [← βc, ← βc, ← βc, cub, val_tauW _ _ hJ, val_tauW _ _ hJ, val_tauW _ _ hJ, ← map_add (f := _), ← map_add (f := _), ← map_add (f := _),
    ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add] at key
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).trans ?_
  rw [Category.id_comp, Category.id_comp, Category.id_comp, val_tau _ hJ', val_tau _ hJ', val_tau _ hJ']
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end Pull

end TauPull

theorem tauBimult_of_isPullDeg : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (_hD : IsPullDeg φ D D'), D.TauBimult → D'.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ hD hB => TauPull.tauBimult_pull hG hD hB

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem expBijF_and_expandsF_lin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ExpBijF U.toUnifPre ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (w₀ : W0 U.toUnifPre) (t t' t'' : SecA A F k) (s s' : Fam D.toPre F k) (c : F), U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀ t' s' → (∀ j, t''.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t.f j + t'.f j) → U.ExpandsF F k w₀ t'' (c • s + s') := by
  intro hL R _ _ _ I _ D A G _ _ _ U
  refine ⟨GlobalTheory.expansion_bijective_over_fields hL.1.globalFns R I D A G U, ?_⟩
  intro F _ _ k w₀ t t' t'' s s' c h h' e
  have key := GlobalTheory.FieldBaseChange.expandsF_lin U.toUnifPre F c h h'
  have ext : ∀ a b : SecA A F k, (∀ j, a.f j = b.f j) → a = b := by
    rintro ⟨a, _⟩ ⟨b, _⟩ hab
    obtain rfl : a = b := funext hab
    rfl
  exact (congrArg (fun x : SecA A F k => U.ExpandsF F k w₀ x (c • s + s')) (ext t'' _ fun j => (e j).trans rfl)).mpr key

end GlobalTheory.UT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecPull

variable {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem mem_wchart_comp {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) {p : K → L.ι} {y : Y'}
    (hy : y ∈ LB.wchart L (fun k => φ' k ≫ F) p) : h y ∈ LB.wchart L φ p :=
  Set.mem_iInter.2 fun k => by
    have := Set.mem_iInter.1 hy k
    show (h ≫ φ k) y ∈ L.U (p k)
    rw [← hc]; exact this

theorem trF_comp {Z : Scheme.{0}} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {h : Y' ⟶ Y}
    (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (p p' : K → L.ι) :
    trF φ ε (r ≫ h) z p p' = trF (fun k => φ' k ≫ F) ε r z p p' := by
  simp only [trF, hc, Category.assoc]

theorem exists_down_sec {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    (φ' : K → (Y' ⟶ X')) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ)
    (s : LB.Sec (LB.LinComb L φ ε)) : ∃ a : LB.Sec (LB.LinComb L' φ' ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gs r z (LB.wchart L' φ' q) (a.f q) =
          (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ a : Γ(Y', LB.wchart L' φ' q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ a = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) := by
    intro q
    let W : (K → L.ι) → Y'.Opens := fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    have le : ∀ p, W p ≤ h ⁻¹ᵁ LB.wchart L φ p := fun p y hy => mem_wchart_comp hc hy.1
    obtain ⟨v, hv⟩ : ∃ v : ∀ p, Γ(Y', W p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p, r z ∈ W p →
        gs r z (W p) (v p) = (pw w φ' ε r z p q)⁻¹.val * gs (r ≫ h) z (LB.wchart L φ p) (s.f p) :=
      ⟨fun p => (u p q)⁻¹.val * (Y'.presheaf.map (homOfLE (le p)).op).hom ((h.app _).hom (s.f p)),
        fun Z r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q Z r z hz)))))
          ((gs_res r z (le p) hz _).trans (gs_pull r h z _ (le p hz) _)))⟩
    obtain ⟨a, ha, -⟩ := Y'.sheaf.existsUnique_gluing' W (LB.wchart L' φ' q)
      (fun p => homOfLE inf_le_right) (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) v
      (fun p p' => fn_ext (V := W p ⊓ W p') fun y hy => by
        refine (gs_res (𝟙 Y') y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y') y inf_le_right hy _).symm)
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, sec_trans s (𝟙 Y' ≫ h) y (le p hy.1) (le p' hy.2), trF_comp hc,
          pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.1.2, trF_self hL' _ ε (𝟙 Y') y hy.1.2, inv_one, mul_one,
          ← mul_assoc, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right])
    refine ⟨a, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ W p := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_right hz a).symm.trans ((congrArg (gs r z (W p)) (ha p)).trans (hv Z r z p hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => ha q Z r z p⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : (𝟙 Y' : Y' ⟶ Y') y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (gs_res (𝟙 Y') y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y') y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y') y _ hy _).trans (congrArg Units.val (gm_linComb L' φ' ε (𝟙 Y') y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y') y _ hy _))).symm)
  refine (ha j _ (𝟙 Y') y p m hy.1).trans (Eq.trans ?_ (congrArg _ (ha j' _ (𝟙 Y') y p m hy.2)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y') y m m hy.1 hy.2, trF_self hL _ ε (𝟙 Y') y m, one_mul, mul_inv, inv_inv, Units.val_mul,
    mul_assoc]
  rfl

theorem existsUnique_secPull (X X' Y Y' : Scheme.{0}) (L : LB X) (L' : LB X') (F : X' ⟶ X) (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) (K : Type) [Fintype K] (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃! a : LB.Sec (LB.LinComb L' φ' ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain ⟨a, ha⟩ := exists_down_sec ((isGen_iff w).1 hw) hL hL' φ' φ ε h hc s
  refine ⟨a, fun Z r z p q hp hq => ?_, fun b hb => ?_⟩
  · rw [ha Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)]
    exact (Units.mul_inv_cancel_left (pw w φ' ε r z p q) _).symm
  · have e : b.f = a.f := funext fun q => fn_ext fun y hy => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      refine Eq.trans ?_ (ha _ (𝟙 Y') y p q (Set.mem_iInter.2 hp) hy).symm
      rw [hb _ (𝟙 Y') y p q hp (Set.mem_iInter.1 hy)]
      exact (Units.inv_mul_cancel_left (pw w φ' ε (𝟙 Y') y p q) _).symm
    cases a; cases b; cases e; rfl

end GlobalTheory.SecPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.AdicSum
section
variable {R : Type} [CommRing R] {I : Ideal R} {E E' Ix : Type} [AddCommGroup E] [Module R E]
  [AddCommGroup E'] [Module R E']

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumI_unique [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥)
    {x : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x s') : s = s' := by
  classical
  obtain ⟨N, hN, hs, -, hconv⟩ := h
  obtain ⟨N', hN', hs', -, hconv'⟩ := h'
  set M := N ⊔ N' with hM
  have hMfg : M.FG := hN.sup hN'
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
  have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
  have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
    intro n
    obtain ⟨S, hS⟩ := hconv n
    obtain ⟨S', hS'⟩ := hconv' n
    have h1 := hS (S ∪ S') Finset.subset_union_left
    have h2 := hS' (S ∪ S') Finset.subset_union_right
    have h3 : s - s' ∈ I ^ n • M := by
      have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
      rw [e]
      exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
        (Submodule.smul_mono le_rfl le_sup_right h2)
    rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
    obtain ⟨y, hy, hyeq⟩ := h3
    have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
    rwa [← hy']
  have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
    rw [Ideal.jacobson_bot] at hI
    have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
    rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
    exact hpow
  exact sub_eq_zero.mp (congrArg Subtype.val h0)

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumI_map (f : E →ₗ[R] E') {x : Ix → E} {s : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) :
    _root_.GlobalTheory.UT.SumI I (fun i => f (x i)) (f s) := by
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  refine ⟨N.map f, hN.map f, Submodule.mem_map_of_mem hs,
    fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  refine ⟨S, fun T hT => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Submodule.map_smul'', ← map_sum, ← map_sub]
  exact Submodule.mem_map_of_mem (hS T hT)

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumI_add {x x' : Ix → E} {s s' : E}
    (h : _root_.GlobalTheory.UT.SumI I x s) (h' : _root_.GlobalTheory.UT.SumI I x' s') :
    _root_.GlobalTheory.UT.SumI I (fun i => x i + x' i) (s + s') := by
  classical
  obtain ⟨N, hN, hs, hx, hconv⟩ := h
  obtain ⟨N', hN', hs', hx', hconv'⟩ := h'
  refine ⟨N ⊔ N', hN.sup hN', Submodule.add_mem_sup hs hs',
    fun i => Submodule.add_mem_sup (hx i) (hx' i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hconv n
  obtain ⟨S', hS'⟩ := hconv' n
  refine ⟨S ∪ S', fun T hT => ?_⟩
  have e : s + s' - ∑ i ∈ T, (x i + x' i) = (s - ∑ i ∈ T, x i) + (s' - ∑ i ∈ T, x' i) := by
    rw [Finset.sum_add_distrib]; abel
  rw [e]
  exact Submodule.add_mem _
    (Submodule.smul_mono le_rfl le_sup_left (hS T (Finset.union_subset_left hT)))
    (Submodule.smul_mono le_rfl le_sup_right (hS' T (Finset.union_subset_right hT)))

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumI_comp_iff {Jx : Type} {e : Jx → Ix}
    (he : Function.Injective e) {x : Ix → E}
    (h0 : ∀ i, i ∉ Set.range e → x i = 0) {s : E} :
    _root_.GlobalTheory.UT.SumI I (x ∘ e) s ↔ _root_.GlobalTheory.UT.SumI I x s := by
  classical
  constructor
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun i => ?_, fun n => ?_⟩
    · by_cases hi : i ∈ Set.range e
      · obtain ⟨j, rfl⟩ := hi
        exact hx j
      · rw [h0 i hi]
        exact N.zero_mem
    · obtain ⟨S, hS⟩ := hconv n
      refine ⟨S.map ⟨e, he⟩, fun T hT => ?_⟩
      rw [← Finset.sum_preimage e T he.injOn x (fun i _ hi => h0 i hi)]
      refine hS _ fun j hj => ?_
      rw [Finset.mem_preimage]
      exact hT (Finset.mem_map_of_mem _ hj)
  · rintro ⟨N, hN, hs, hx, hconv⟩
    refine ⟨N, hN, hs, fun j => hx (e j), fun n => ?_⟩
    obtain ⟨S, hS⟩ := hconv n
    refine ⟨S.preimage e he.injOn, fun T hT => ?_⟩
    have hpre : (T.map ⟨e, he⟩ ∪ S).preimage e he.injOn = T := by
      ext j
      simp only [Finset.mem_preimage, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk, he.eq_iff, exists_eq_right]
      exact ⟨fun hj => hj.elim id fun hj => hT (Finset.mem_preimage.mpr hj), Or.inl⟩
    have hsum := hS (T.map ⟨e, he⟩ ∪ S) Finset.subset_union_right
    rw [← Finset.sum_preimage e _ he.injOn x (fun i _ hi => h0 i hi), hpre] at hsum
    exact hsum

end

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AdicSum.sumF_calculus : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R),
    _root_.ReciprocityTheory.ChartRestriction.G.Out.AdmBase R I → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (Ix : Type)
    (x x' : Ix → F) (s s' : F),
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x s' →
      s = s') ∧
    (_root_.GlobalTheory.UT.SumF I F x s → _root_.GlobalTheory.UT.SumF I F x' s' →
      ∀ c : F, _root_.GlobalTheory.UT.SumF I F (fun i => c * x i + x' i) (c * s + s')) ∧
    ∀ (Jx : Type) (e : Jx → Ix), Function.Injective e → (∀ i, i ∉ Set.range e → x i = 0) →
      (_root_.GlobalTheory.UT.SumF I F (x ∘ e) s ↔
        _root_.GlobalTheory.UT.SumF I F x s) := by
  intro R _ _ I hadm F _ _ Ix x x' s s'
  obtain ⟨hnoeth, -, -, hcomplete⟩ := hadm
  haveI := hnoeth
  haveI := hcomplete
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  refine ⟨fun h h' => _root_.GlobalTheory.AdicSum.sumI_unique (IsAdicComplete.le_jacobson_bot I) h h',
    fun h h' c => ?_, fun Jx e he h0 => _root_.GlobalTheory.AdicSum.sumI_comp_iff he h0⟩
  let f : F →ₗ[R] F :=
    { toFun := fun y => c * y
      map_add' := mul_add c
      map_smul' := fun r y => by
        show c * (algebraMap R (FractionRing R) r • y) = algebraMap R (FractionRing R) r • (c * y)
        exact Algebra.mul_smul_comm _ _ _ }
  exact _root_.GlobalTheory.AdicSum.sumI_add (_root_.GlobalTheory.AdicSum.sumI_map f h) h'

end GlobalTheory.AdicSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif.RigidifyIso

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_ratio {X X' Y Y' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (f : Y' ⟶ Y) (hφ : ∀ k, φ' k ≫ F = f ≫ φ k) (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ c : Γ(Y', ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm (r ≫ f) z (LB.wchart L φ p) (t.s p) =
        gm r z ⊤ c * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q)) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have le : ∀ p, LB.wchart L (fun k => φ' k ≫ F) p ≤ f ⁻¹ᵁ LB.wchart L φ p := fun p y hy =>
    Set.mem_iInter.2 fun k => (congrArg (fun g : Y' ⟶ X => g y ∈ L.U (p k)) (hφ k)).mp (Set.mem_iInter.1 hy k)
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) p q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
      gm r z _ (res (inf_le_left.trans (le p)) (pullU f _ (t.s p)) * (u p q * res inf_le_right (a.s q))⁻¹) =
        gm (r ≫ f) z (LB.wchart L φ p) (t.s p) * (pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q))⁻¹ :=
    fun Z r z p q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z _ hz _).trans (gm_pull r f z _ (le p hz.1) _))
      ((map_inv _ _).trans (congrArg (·⁻¹) ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (hu p q Z r z hz) (gm_res r z _ hz _))))))
  obtain ⟨c, hc⟩ := glue_unit (⊤ : Y'.Opens)
    (fun i : (K → L.ι) × (K → L'.ι) => LB.wchart L (fun k => φ' k ≫ F) i.1 ⊓ LB.wchart L' φ' i.2) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (F (φ' k y))
      choose q hq using fun k => exists_chart hL' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(p, q), Set.mem_iInter.2 hp, Set.mem_iInter.2 hq⟩)
    (fun i => res (inf_le_left.trans (le i.1)) (pullU f _ (t.s i.1)) * (u i.1 i.2 * res inf_le_right (a.s i.2))⁻¹)
    (fun i i' y hy => by
      have e : trF φ ε (𝟙 Y' ≫ f) y i.1 i'.1 = trF (fun k => φ' k ≫ F) ε (𝟙 Y') y i.1 i'.1 := by
        simp only [trF, hφ, Category.assoc]
      rw [hv _ _ y _ _ hy.1, hv _ _ y _ _ hy.2, pw_trans hw φ' ε (𝟙 Y') y hy.1.1 hy.2.1 hy.1.2 hy.2.2,
        gen_trans ha (𝟙 Y') y hy.1.2 hy.2.2, gen_trans ht (𝟙 Y' ≫ f) y (le _ hy.1.1) (le _ hy.2.1), e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨c, fun Z r z p q h₁ h₂ => ?_⟩
  have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
  have e := (gm_res r z le_top hz c).symm.trans ((congrArg (gm r z _) (hc (p, q))).trans (hv Z r z p q hz))
  rw [e, inv_mul_cancel_right]

theorem exists_scaled {X X' B : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    (π : X' ⟶ B) (c : Γ(B, ⊤)ˣ) : ∃ w' : LB.Iso L' (L.pull F), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι)
      (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k → gw w' r z j k = gm (r ≫ π) z ⊤ c * gw w r z j k := by
  refine ⟨⟨fun i => res (le_top : _ ≤ π ⁻¹ᵁ ⊤) (pullU π ⊤ c) * w.s i⟩, fun Z r z j k hj hk => ?_⟩
  have hz : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z _ hz _).trans (gm_pull r π z ⊤ trivial c)) rfl)

theorem exists_rigidified_iso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (he : eSec G' ≫ Ψ = f ≫ eSec G) (L : RigLB G) (L' : RigLB G'), (∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen) → ∃ w : LB.Iso L'.L (L.L.pull Ψ), w.IsGen ∧ LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) := by
  rintro S S' f G _ _ G' _ _ Ψ he L L' ⟨w, hw⟩
  have hw := (isGen_iff w).1 hw
  obtain ⟨c, hc⟩ := exists_ratio (K := PUnit) (φ' := fun _ => eSec G') (φ := fun _ => eSec G) (ε := fun _ => 1)
    hw L.isLB L'.isLB f (fun _ => he) L'.rig L'.rigGen L.rig L.rigGen
  obtain ⟨w', hw'⟩ := exists_scaled (B := (𝟙_ (Over S')).left) w G'.hom c
  have hs : eSec G' ≫ (show G'.left ⟶ (𝟙_ (Over S')).left from G'.hom) = 𝟙 _ := Over.w η[G']
  refine ⟨w', (isGen_iff w').2 fun Y r y j j' k k' hj hj' hk hk' => ?_,
    (maps_iff w' _ (fun _ => eSec G) _ L'.rig L.rig f _ (rigPull_le Ψ f he L.L) (fun _ => rfl)).2
      fun Z r z p q hp hq => ?_⟩
  · rw [hw' Y r y j k hj hk, hw' Y r y j' k' hj' hk', hw Y r y j j' k k' hj hj' hk hk', mul_left_comm]
  · refine (hc Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)).trans ?_
    rw [← _root_.mul_assoc]
    refine congrArg₂ (· * ·) ?_ rfl
    rw [pw, Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one,
      hw' Z (r ≫ eSec G') z _ _ (hp _) (hq _), Category.assoc]
    exact congrArg (fun g => gm g z ⊤ c * _) ((congrArg (r ≫ ·) hs).trans (Category.comp_id r)).symm

end GlobalTheory.Unif.RigidifyIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaActs
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionTheta

theorem exists_theta_acts : KerPowSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] (t : Spec (CommRingCat.of F) ⟶ S) (n : ℕ), 1 ≤ n → ∀ x : Over.mk t ⟶ P.A, x ^ n = 1 → ∃ θ : ThetaGrp P.A P.L (n : ℤ) (Over.mk t), θ.pt = x ∧ ∀ s : LB.Sec (LPow P.A P.L (n : ℤ) (Over.mk t)), ∃ s', IsActOf P.A P.L (n : ℤ) θ s s' := by
  intro hK S _ P F _ t n hn x hx

  have : Unique (Over.mk t).left := inferInstanceAs (Unique (PrimeSpectrum F))
  obtain ⟨θ, hθ⟩ := GlobalTheory.BoxTheta.exists_theta hK P hn x hx

  exact ⟨θ, hθ, fun s => GlobalTheory.VVRank.exists_isTwistPull P.A P.isLB θ.isGen s⟩

end GlobalTheory.TorsionTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixRingAct
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MatrixAction

variable {S : Scheme.{0}}

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.MatrixAction.comp_finsetProd {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S}
    (a : T' ⟶ T) {κ : Type} (s : Finset κ) (x : κ → (T ⟶ G)) :
    a ≫ (∏ l ∈ s, x l) = ∏ l ∈ s, a ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, comp_mul, ih]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.MatrixAction.isMonHom_of_points {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h1 : ∀ T : Over S, (1 : T ⟶ G) ≫ f = 1)
    (hm : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  constructor
  · have := h1 (𝟙_ (Over S))
    simpa [Hom.one_def] using this
  · have := hm (G ⊗ G) (fst G G) (snd G G)
    simpa [Hom.mul_def] using this

section
variable {G : Over S} [GrpObj G] {O : Type} [Ring O] (ρ : RingAct G O)

end

end GlobalTheory.MatrixAction
end
