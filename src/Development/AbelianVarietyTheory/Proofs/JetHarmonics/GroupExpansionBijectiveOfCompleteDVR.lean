module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroOfSectionValue
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem expandsG_bijective_of_dvr : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ σ' : U.SecGF F k, ∃! s : Fam D.toPre F k, U.ExpandsG F k σ' s) ∧ ∀ s : Fam D.toPre F k, ∃! σ' : U.SecGF F k, U.ExpandsG F k σ' s :=
  fun hL _ _ _ _ _ _ _ _ _ _ _ _ _ U F _ _ k hk =>
    FieldBaseChange.expandsG_bijective U.toUnifPre F hL.globalFns hk (U.expand k hk)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVRStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupExpansion_bijective_of_completeDVR : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → (∀ σ' : U.SecGF F k, ∃! s : Fam D.toPre F k, U.ExpandsG F k σ' s) ∧ ∀ s : Fam D.toPre F k, ∃! σ' : U.SecGF F k, U.ExpandsG F k σ' s := by
  first | exact @GlobalTheory.expandsG_bijective_of_dvr | exact GlobalTheory.expandsG_bijective_of_dvr | (intros; apply GlobalTheory.expandsG_bijective_of_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpandsGSum
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GroupExpansionLinear

open GlobalTheory.ExpansionLinear

theorem expandsG_sum : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (F : Type) [Field F] [Algebra (FractionRing V) F] (k l : ℕ) (c : Fin l → F) (σ : Fin l → U.SecGF F k) (s : Fin l → Fam D.toPre F k) (σ' : U.SecGF F k), (∀ i, U.ExpandsG F k (σ i) (s i)) → (∀ jj, σ'.f jj = ∑ i, resTop _ (scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) * (σ i).f jj) → U.ExpandsG F k σ' (∑ i, c i • s i) := by
  intro R _ _ _ _ D A G _ _ U F _ _ k n c σ' s σ₀ ht h₀
  choose m d σ f hexp hG hB using ht
  let e : Fin (Fintype.card (Σ l, Fin (m l))) ≃ Σ l, Fin (m l) := (Fintype.equivFin _).symm
  refine ⟨_, fun i => c (e i).1 * d (e i).1 (e i).2, fun i => σ (e i).1 (e i).2, fun i => f (e i).1 (e i).2,
    fun i => hexp _ _, ?_, fun α => ?_⟩
  · exact secLin_comb _ _ _ _ _ _ _ σ' _ h₀ σ _ hG e _ (fun i => GlobalTheory.ExpansionLinear.scal_mul _ _ _)
  · exact secLin_comb _ _ _ _ _ _ (fun l => scal (fst (TF (R := R) F) D.toPre.P.A).left (c l))
      (fun l => (s l).s α) _ (fun j => fam_sum_f _ _ α j) (fun l i => f l i α) _ (fun l => hB l α) e _
      (fun i => GlobalTheory.ExpansionLinear.scal_mul _ _ _)

end GlobalTheory.GroupExpansionLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxLinear

open GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}
  {Z : Scheme.{0}}

theorem ext_val {D : DegPre R} {S T : Fam D F k}
    (h : ∀ (α : D.X) (y : (DegPre.BF D F).left) (J), Good D.P.L y J →
      sval (S.s α) (𝟙 _) y J = sval (T.s α) (𝟙 _) y J) : S = T := by
  refine fam_ext fun α jj => fn_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  refine (sec_trans (S.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).trans
    (Eq.trans (congrArg _ (h α y J hJ)) (sec_trans (T.s α) (𝟙 _) y hy (hJ.mem _ (𝟙 _))).symm)

theorem sval_add {D : DegPre R} (S T : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((S + T).s α) q y J = sval (S.s α) q y J + sval (T.s α) q y J :=
  gs_add q y _ (hJ.mem _ q) _ _

theorem sval_smul {D : DegPre R} (c : F) (S : Fam D F k) (α : D.X) (q : Z ⟶ (DegPre.BF D F).left) (y : Z) {J}
    (hJ : Good D.P.L y J) :
    sval ((c • S).s α) q y J = gs (X := Spec (CommRingCat.of F)) (q ≫ (fst (TF (R := R) F) D.P.A).left) y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * sval (S.s α) q y J := by
  refine (gs_mul q y _ (hJ.mem _ q) _ _).trans (congrArg (· * _) ?_)
  exact (gs_res q y le_top (hJ.mem _ q) _).trans (gs_pull q (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _)

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem prB_fst (i : Fin j) : prB pD F i ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R) F) D'.P.A).left :=
  congrArg (fun g => g.left) (whiskerLeft_fst (TF (R := R) F) (pD.pw.pr i))

theorem box_val {S : Fam D' F k} {s : Fin j → Fam D F k} (h : IsBoxFam pD F k S s) (α' : D'.X)
    (y : (DegPre.BF D' F).left) {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    (∏ a, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D' F α' a) ^ DegPre.famε k a).val * sval (S.s α') (𝟙 _) y J' =
      ∏ i, sval ((s i).s (pD.xe α' i)) (𝟙 _ ≫ prB pD F i) y J := by
  obtain ⟨hφ, H⟩ := h α'
  exact boxPull_val (w := pD.w) (hφ := hφ) (s := fun i => (s i).s (pD.xe α' i)) H (𝟙 _) y hJ hJ'

theorem prod_update {A S : Type*} [CommMonoid S] {j : ℕ} [DecidableEq (Fin j)] (g : Fin j → A → S) (s : Fin j → A)
    (i : Fin j) (x : A) :
    ∏ l, g l (Function.update s i x l) = g i x * ∏ l ∈ Finset.univ.erase i, g l (s l) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun l hl => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

theorem box_unique {S T : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    (hT : IsBoxFam pD F k T s) : S = T :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    exact (Units.mul_right_inj _).1 ((box_val pD hS α y hJ hJ').trans (box_val pD hT α y hJ hJ').symm)

theorem box_add [DecidableEq (Fin j)] {S S₁ S₂ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {a b : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (a + b))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a))
    (h₂ : IsBoxFam pD F k S₂ (Function.update s i b)) : S = S₁ + S₂ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    have e₂ := (box_val pD h₂ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_add _ _ _ _ _ hJ, sval_add _ _ _ _ _ hJ', mul_add, add_mul, e₁, e₂]

theorem box_smul [DecidableEq (Fin j)] {S S₁ : Fam D' F k} {s : Fin j → Fam D F k} {i : Fin j} {c : F} {a : Fam D F k}
    (h : IsBoxFam pD F k S (Function.update s i (c • a))) (h₁ : IsBoxFam pD F k S₁ (Function.update s i a)) :
    S = c • S₁ :=
  ext_val fun α y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
    have p := prod_update (fun l (t : Fam D F k) => sval (t.s (pD.xe α l)) (𝟙 _ ≫ prB pD F l) y J) s i
    have e := (box_val pD h α y hJ hJ').trans (p _)
    have e₁ := (box_val pD h₁ α y hJ hJ').trans (p _)
    refine (Units.mul_right_inj _).1 (e.trans ?_)
    rw [sval_smul _ _ _ _ _ hJ, sval_smul _ _ _ _ _ hJ', Category.assoc, prB_fst, mul_left_comm, e₁,
      _root_.mul_assoc]

end GlobalTheory.BoxLinear

namespace GlobalTheory

theorem exists_boxFam_multilinear : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  intro hG R _ _ j D D' pD F _ _ k
  choose bx hbx using BoxFamily.exists_isBoxFam hG R j D D' pD F k
  refine ⟨⟨bx, fun s i a b => BoxLinear.box_add pD (hbx _) (hbx _) (hbx _),
    fun s i c a => BoxLinear.box_smul pD (hbx _) (hbx _)⟩, fun s S => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact BoxLinear.box_unique pD h (hbx s)
  · rw [h]; exact hbx s

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMapStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boxFamily_multilinear_map : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), ∃ bx : MultilinearMap (RingHom.id F) (fun _ : Fin j => Fam D F k) (Fam D' F k), ∀ (s : Fin j → Fam D F k) (S : Fam D' F k), IsBoxFam pD F k S s ↔ S = bx s := by
  exact @_root_.GlobalTheory.exists_boxFam_multilinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqZeroOfSval
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullComp

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

theorem sval_of_heq {m n : ℕ} (h : m = n) (s : Fam D.toPre F m) (t : Fam D.toPre F n) (e : HEq s t)
    {α β : D.toPre.X} (hα : α = β) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) :
    sval (t.s α) r z J = sval (s.s β) r z J := by
  subst h hα
  cases e
  rfl

theorem sval_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J) : sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h (fun k => J (r ≫ φ k)))).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem eq_zero_of_sval {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ y J, Good L y J → sval s (𝟙 Y) y J = 0) (j) : s.f j = 0 :=
  sec_ext_val hL (s' := SectionArithmetic.secZero _) (fun y J hJ => (h y J hJ).trans
    (sval_eq_zero _ (fun _ => rfl) _ _ _).symm) j

theorem aF_comp (oa : D.toPre.OAct O) (a a' : O) : aF D F oa a ≫ aF D F oa a' = aF D F oa (a' * a) := by
  have : oa.onB.act (a' * a) = oa.onB.act a ≫ oa.onB.act a' := by
    first
      | exact oa.onB.map_mul _ _
      | (rw [mul_comm]; exact oa.onB.map_mul _ _)
  simp [aF, DegPre.prB, this]

theorem zF_aF (oa : D.toPre.OAct O) (a : O) : DegPre.zF D.toPre F ≫ aF D F oa a = DegPre.zF D.toPre F := by
  have := oa.onB.hom a
  have z₁ : DegPre.zF D.toPre F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  apply CartesianMonoidalCategory.hom_ext
  · rw [aF, Category.assoc, lift_fst]
  · rw [aF, Category.assoc, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
    first | done | exact z₂.symm

end GlobalTheory.PullComp

namespace GlobalTheory


open PullComp in
theorem pullAl_comp : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a a' : O) (N N' k : ℕ), 1 ≤ N → 1 ≤ N' → 1 ≤ k → a * star a = (N : O) → a' * star a' = (N' : O) → ∀ (s : Fam D.toPre F k) (s₁ : Fam D.toPre F (k * N')) (s₂ : Fam D.toPre F (k * N' * N)) (s₃ : Fam D.toPre F (k * (N' * N))), PullAl D F oa a' k N' s s₁ → PullAl D F oa a (k * N') N s₁ s₂ → HEq s₂ s₃ → PullAl D F oa (a' * a) k (N' * N) s s₃ := by
  intro _ V _ _ _ D F _ _ O _ _ _ oa w0 _ a a' N N' k hN hN' _ _ _ s s₁ s₂ s₃ h₁ h₂ he
  have hL : D.toPre.P.L.IsLB := D.toPre.P.isLB
  have hst : ∀ χ : D.toPre.X, star (a' * a) • χ = star a • star a' • χ := fun χ => by
    rw [star_mul, mul_smul]
  have hcl : (aF D F oa a).left ≫ (aF D F oa a').left = (aF D F oa (a' * a)).left :=
    congrArg (fun q => q.left) (aF_comp D F oa a a')
  have hzl : (DegPre.zF D.toPre F).left ≫ (aF D F oa a).left = (DegPre.zF D.toPre F).left :=
    congrArg (fun q => q.left) (zF_aF D F oa a)
  refine ⟨fun χ => ?_, fun β hβ => ?_⟩
  · obtain ⟨u₁, hu₁, c₁, r₁⟩ := h₁.1 χ
    obtain ⟨u₂, hu₂, c₂, r₂⟩ := h₂.1 (star a' • χ)
    obtain ⟨u, hu, vu⟩ := exists_gen hL (φ' := pullφ D F oa (a' * a) χ) (ε' := pullε k (N' * N)) (fun U _ h => by
        simp only [pullφ, pullε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hst, ← hcl, Category.assoc,
          zpow_neg, Finset.prod_inv_distrib, Nat.mul_assoc]
        group)
      (LB.mulGen D.toPre.P.L _ _ _ _ u₂ (LB.pullGen D.toPre.P.L _ _ u₁ (aF D F oa a).left))
      (mulGen_isGen _ _ _ _ _ _ _ hu₂ (pullGen_isGen _ _ _ _ hu₁ _))
    refine ⟨u, hu, corr_of_val hL fun y J hJ => ?_, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).2 fun y J hJ => ?_⟩
    · have e₁ := val_corr hJ c₁ (𝟙 _)
      have e₂ := val_corr hJ c₂ (𝟙 _)
      rw [val_pull hJ, val_pull hJ, val_pow] at e₁ e₂
      rw [val_pull hJ, val_pull hJ, val_pow, vu _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, hzl, e₁, e₂,
        ← pow_add]
      congr 1
      obtain ⟨N, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
      obtain ⟨N', rfl⟩ : ∃ n, N' = n + 1 := ⟨N' - 1, by omega⟩
      have : (N' + 1) * (N + 1) - 1 = (N' + 1) * N + N' := by
        rw [Nat.sub_eq_iff_eq_add (Nat.succ_le_of_lt (by positivity))]; ring
      rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
      ring
    · rw [sval_of_heq D F (Nat.mul_assoc k N' N) s₂ s₃ he (hst χ),
        (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₂ _ _ y J hJ, (secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₁ _ _ y J hJ,
        vu _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, hcl, Units.val_mul]
      ring
  · refine eq_zero_of_sval hL _ fun y J hJ => ?_
    rw [sval_of_heq D F (Nat.mul_assoc k N' N) s₂ s₃ he rfl]
    by_cases hb : ∃ χ', β = star a • χ'
    · obtain ⟨χ', rfl⟩ := hb
      obtain ⟨u₂, -, -, r₂⟩ := h₂.1 χ'
      rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ _).1 r₂ _ _ y J hJ,
        sval_eq_zero _ (h₁.2 χ' fun χ e => hβ χ (by rw [hst, e])), zero_mul]
    · exact sval_eq_zero _ (h₂.2 β fun χ e => hb ⟨χ, e⟩) _ _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdPullZero
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxPull

open GlobalTheory.BoxPhi

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

theorem prod_pull_zero (D : DegData V (maximalIdeal V)) [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ)
    (hN : 1 ≤ N) (χ : D.toPre.X) {U : Type} [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h ((DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) ^ pullε k N i =
      h (1 : TF (R := V) F ⟶ D.toPre.P.A).left ^ (k * (N - 1)) := by
  have := oa.onB.hom a
  have p₃ := prod_fam D.toPre F (DegPre.zF D.toPre F) (star a • χ) (k * N) h
  have p₄ := prod_fam D.toPre F (DegPre.zF D.toPre F ≫ aF D F oa a) χ k h
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D.toPre F ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = 1 := by
    rw [Category.assoc, aF, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
  rw [z₂, _root_.mul_one] at p₃
  rw [z₃, _root_.mul_one] at p₄
  simp only [Over.comp_left, Category.assoc] at p₄
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).trans ?_
  rw [← zpow_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem aF_pr {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X] (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O) (a : O) (i : Fin j)
    (hact : oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) :
    (aF D' F oa' a).left ≫ prB pD F i = prB pD F i ≫ (aF D F oa a).left := by
  refine congrArg (fun q => q.left) (?_ : aF D' F oa' a ≫ (TF (R := V) F ◁ pD.pw.pr i) =
    (TF (R := V) F ◁ pD.pw.pr i) ≫ aF D F oa a)
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, hact]

theorem pullAl_box {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X]
    (hx : ∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i)
    (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (a : O) (N k : ℕ) (hN : 1 ≤ N)
    (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k)
    (S' : Fam D'.toPre F (k * N)) (hs : ∀ i, PullAl D F oa a k N (s i) (s' i)) (hS : IsBoxFam pD F k S s)
    (hS' : IsBoxFam pD F (k * N) S' s') : PullAl D' F oa' a k N S S' := by
  have ht := fun i => aF_pr (F := F) pD oa oa' a i (hact a i)
  refine ⟨fun χ' => ?_, fun β' hβ' => ?_⟩
  · choose u hu hc hr using fun i => (hs i).1 (pD.xe χ' i)
    have hφ : ∀ i b, pullφ D' F oa' a χ' b ≫ (pD.pw.pr i).left =
        prB pD F i ≫ pullφ D F oa a (pD.xe χ' i) b := by
      rintro i (b | b)
      · exact ((hS' (star a • χ')).choose i b).trans (by rw [hx]; rfl)
      · show ((aF D' F oa' a).left ≫ DegPre.famφ D'.toPre F χ' b) ≫ _ =
          _ ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F (pD.xe χ' i) b
        rw [Category.assoc, (hS χ').choose i b, ← Category.assoc, ht, Category.assoc]
    obtain ⟨v, hv, vv⟩ := exists_box_gen D.toPre.P.isLB D'.toPre.P.isLB pD.w pD.w_gen hφ u hu
    refine ⟨v, hv, corr_of_val D'.toPre.P.isLB fun y J' hJ' => ?_,
      (secRel_iff D'.toPre.P.isLB _ _ _ _ _ _ _ _ _ v).2 fun y J' hJ' => ?_⟩
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₂ := vv _ (DegPre.zF D'.toPre F).left y J J' hJ hJ'
      let r : (TF (R := V) F).left ⟶ (TK V).left := 𝟙 (TF (R := V) F).left ≫ jFK (R := V) F
      have e₃ : om pD.w y J J' (1 : TF (R := V) F ⟶ D'.toPre.P.A).left * val D'.toPre.rigK r y J' =
          ∏ _i : Fin j, val D.toPre.rigK r y J := by
        have z : (1 : TF (R := V) F ⟶ D'.toPre.P.A).left = r ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A :=
          (show (1 : TF (R := V) F ⟶ D'.toPre.P.A).left =
              jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A by
            show (toUnit _ ≫ η[D'.toPre.P.A]).left = _
            rw [Over.comp_left]
            rfl).trans (congrArg (· ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A)
            (Category.id_comp (jFK (R := V) F)).symm)
        rw [z]
        exact BoxFamily.rig_val pD hJ hJ' r
      have e₅ : ∀ i, val (u i) ((DegPre.zF D'.toPre F).left ≫ prB pD F i) y J =
          val D.toPre.rigK r y J ^ (k * (N - 1)) := fun i => by
        have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hc i) (𝟙 _)).trans
          ((val_pull hJ _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)))
        rw [Category.id_comp] at this
        rw [BoxFamily.zF_pr]
        exact this
      rw [prod_pull_zero D' oa' a k N hN χ', Finset.prod_congr rfl (fun i _ => e₅ i), Finset.prod_pow, ← e₃,
        mul_pow] at e₂
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_
        ((val_pull hJ' _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)).symm)
      rw [Category.id_comp]
      exact mul_left_cancel e₂
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₁ := fam_val pD hS' (star a • χ') (𝟙 _) y hJ hJ'
      have e₂ := fam_val pD hS χ' (𝟙 _ ≫ (aF D' F oa' a).left) y hJ hJ'
      have e₃ := vv _ (𝟙 _) y J J' hJ hJ'
      have e₄ : ∀ i, sval ((s' i).s (pD.xe (star a • χ') i)) (𝟙 _ ≫ prB pD F i) y J =
          sval ((s i).s (pD.xe χ' i)) ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ prB pD F i) y J *
            (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
        rw [hx, Category.assoc, ht, ← Category.assoc]
        exact (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 (hr i) _ _ y J hJ
      have e₅ : ∏ b, om pD.w y J J' (𝟙 _ ≫ pullφ D' F oa' a χ' b) ^ pullε k N b =
          (∏ b, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D'.toPre F (star a • χ') b) ^ DegPre.famε (k * N) b) *
          (∏ b, om pD.w y J J' ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ DegPre.famφ D'.toPre F χ' b) ^
            DegPre.famε k b)⁻¹ := by
        simp only [Category.assoc]
        exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
      rw [Finset.prod_congr rfl (fun i _ => e₄ i), Finset.prod_mul_distrib, ← e₂, ← Units.coe_prod, ← e₃, e₅] at e₁
      exact alg_fin e₁
  · obtain ⟨i, hi⟩ : ∃ i, ∀ χ, pD.xe β' i ≠ star a • χ := by
      by_contra hne
      push Not at hne
      choose χ hχ using hne
      refine hβ' (pD.xe.symm χ) (pD.xe.injective (funext fun i => ?_))
      rw [hx, AddEquiv.apply_symm_apply, hχ]
    have hz := (hs i).2 _ hi
    intro jj
    refine fn_ext fun y hy => ?_
    obtain ⟨J', hJ', e⟩ := sval_trans D'.toPre.P.isLB (S'.s β') y jj hy
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
    have e₁ := fam_val pD hS' β' (𝟙 _) y hJ hJ'
    have z₀ : sval ((s' i).s (pD.xe β' i)) (𝟙 _ ≫ prB pD F i) y J = 0 := by
      exact (congrArg (gs _ y _) (hz _)).trans (gs_zero' _ y _)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z₀, Units.mul_right_eq_zero] at e₁
    rw [e₁, mul_zero] at e
    refine e.trans ?_
    exact (gs_zero' _ y _).symm

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i) → ∀ (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k) (S' : Fam D'.toPre F (k * N)), (∀ i, PullAl D F oa a k N (s i) (s' i)) → IsBoxFam pD F k S s → IsBoxFam pD F (k * N) S' s' → PullAl D' F oa' a k N S S' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ pD _ _ _ _ _ _ _ _ hx oa oa' hact a N k hN _ _ s s' S S' hs hS hS' =>
    pullAl_box pD hx oa oa' hact a N k hN s s' S S' hs hS hS'

end GlobalTheory.BoxPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsValEqOfNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PullAlValueIntegralPoint
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pullAl_value_integral_point :
    Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fam D.toPre F k) (s' : Fam D.toPre F (k * N)), PullAl D F oa a k N s s' → ∀ (χ : D.toPre.X) (m : TWM.TO hϖ hv ⟶ D.toPre.P.A) (r : ℚ), (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre (χ) i) (DegPre.famε (k))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s.s χ) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) → (∃ G₀ : LB.Gen (LB.LinComb D.toPre.P.L (fun i => (m).left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N))), G₀.IsGen ∧ ∃ x : F, v x = ((r : ℚ) : WithTop ℚ) ∧ ∀ (z : (TF (R := V) F).left) (J), Good D.toPre.P.L z J → sval (s'.s (star a • χ)) (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom x) * (val G₀ (TWM.ιS hϖ hv).left z J).val) := by
  intro hLaws V _ _ _ ϖ hϖ D Q _ F _ _ _ v hv O _ _ _ oa w0 hw a N k hN _ haa s s' hpull χ m r ⟨G₀, hG₀, x, hx, hval⟩
  have hL := D.toPre.P.isLB
  obtain ⟨u, hu, hcorr, hrel⟩ := hpull.1 χ
  obtain ⟨n, ψ, δ, eB, heB, hform, ve⟩ :=
    pullGen_one hLaws.globalFns D F oa w0 hw a N hN (by rw [mul_comm]; exact haa) k χ u hu hcorr
  have hform' : FormEq (Sum.elim (fun i => (m ≫ oa.onB.act a).left ≫ DegPre.famφB D.toPre χ i)
      (fun i => m.left ≫ ψ i)) (Sum.elim (DegPre.famε k) δ)
      (fun i => m.left ≫ DegPre.famφB D.toPre (star a • χ) i) (DegPre.famε (k * N)) := fun U _ h => by
    refine Eq.trans ?_ (hform U (fun q => h (m.left ≫ q)))
    refine Finset.prod_congr rfl ?_
    rintro (i | i) -
    · simp only [Sum.elim_inl, Over.comp_left, Category.assoc]
    · rfl
  obtain ⟨G₁, hG₁, vG⟩ := exists_gen hL hform'
    (LB.mulGen D.toPre.P.L _ _ _ _ G₀ (LB.pullGen D.toPre.P.L _ _ eB m.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hG₀ (DVR.pullGen_isGen _ _ _ _ heB _))
  refine ⟨G₁, hG₁, x, hx, fun z J hJ => ?_⟩
  have H := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _
    (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left z J hJ
  have e₁ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (aF D F oa a).left =
      (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m ≫ oa.onB.act a)).left := by
    rw [← Over.comp_left, aF, comp_lift, lift_fst, ← Category.assoc, lift_snd, Category.assoc]
  have e₂ : (lift (𝟙 (TF (R := V) F)) (TWM.ιS hϖ hv ≫ m)).left ≫ (DegPre.prB D.toPre F).left =
      (TWM.ιS hϖ hv).left ≫ m.left := by
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  rw [H, e₁, hval z J hJ, ve _ _ z J hJ, e₂, vG _ _ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul, _root_.mul_assoc]

end GlobalTheory
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExactTerm

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem exists_val_eq_of_nonneg [IsAlgClosed F] (hv : ValOver ϖ F v) {r : ℚ} (hr : 0 ≤ r) :
    ∃ c : F, v c = ((r : ℚ) : WithTop ℚ) := by
  rcases hr.eq_or_lt with rfl | hr
  · exact ⟨1, by rw [AddValuation.map_one]; rfl⟩
  · obtain ⟨c, -, hc⟩ := exists_val_eq hv hr
    exact ⟨c, hc⟩

theorem nuGe_of_single (hϖ : Irreducible ϖ) (hQ : QForm.IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) (α : D.toPre.X) (r : ℚ)
    (hs : ∀ β : D.toPre.X, (∀ mu, α + k • mu ≠ β) → ∀ j, (s.s β).f j = 0)
    (h : VGe D F v k α (s.s α) (r + (Q α : ℚ) / k)) : NuGe D Q F v k s r := by
  intro β
  by_cases hβ : ∃ mu, α + k • mu = β
  · obtain ⟨m0, rfl⟩ := hβ
    have H := SectionScalarValuation.fe_move hϖ hQ hv k m0 α s h
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e : r + (Q α : ℚ) / k + ((k * Q m0 + QForm.bOf D.toPre Q m0 α : ℤ) : ℚ) = r + (Q (α + k • m0) : ℚ) / k := by
      rw [q_shift hϖ hQ α m0 k]; push_cast; field_simp; ring
    rwa [e] at H
  · exact vge_of_zero (hs β fun mu e => hβ ⟨mu, e⟩) _

theorem pullAl_zero {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} {a : O} {k N : ℕ}
    {s : Fam D.toPre F k} {s' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s s') (χ : D.toPre.X)
    (h0 : ∀ j, (s.s χ).f j = 0) : ∀ j, (s'.s (star a • χ)).f j = 0 := by
  intro j
  obtain ⟨u, -, -, hrel⟩ := h.1 χ
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

theorem phiRel_zero (hG : GlobalFnsSt) {k : ℕ} {p : QkPt D.toPre F k}
    {w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))} (hw : w.IsGen)
    {s t : Fam D.toPre F k} (h : PhiRel D.toPre F k p w s t) (α : D.toPre.X)
    (h0 : ∀ j, (s.s α).f j = 0) : ∀ j, (t.s (α + p.y)).f j = 0 := by
  intro j
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_phi hG p w hw α
  refine sec_ext_val (s' := SecOps.secZero) D.toPre.P.isLB (fun y J hJ => ?_) j
  rw [(secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h α u hu hc) _ (𝟙 _) y J hJ,
    UUA.sval_zero_of h0 _ y J (hJ.mem _ _), UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul]

end

theorem main : Laws → TwistBCSpanStatement → TWM.VRatioGtStatement → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (w0 : O), TraceFormTwistIso D.toPre oa w0 → ∀ (a : O) (N k : ℕ), 1 ≤ N → 4 ≤ k → a * star a = (N : O) → ∀ (p : QkPt D.toPre F (k * N)) (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε (k * N)))), w.IsGen → ∀ ζ : F, ζ ≠ 0 → FinOrd D F (k * N) p w ζ → ∀ χ₀ : D.toPre.X, ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ ∀ s' t h : Fam D.toPre F (k * N), PullAl D F oa a k N s s' → PhiRel D.toPre F (k * N) p w s' t → Fam.IsSmul D.toPre F ζ t h → NuGe D Q F v (k * N) h 0 ∧ (∀ β : D.toPre.X, (∀ z, β ≠ p.y + star a • χ₀ + k • star a • z) → ∀ j, (h.s β).f j = 0) ∧ ∃ x : F, Val0 D F (k * N) (star a • χ₀ + p.y) (h.s (star a • χ₀ + p.y)) x ∧ v x = (((Q (star a • χ₀ + p.y) : ℚ) / (k * N) : ℚ) : WithTop ℚ) := by
  intro hL hTW hVR hUU V _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv O _ _ _ oa w0 hw0 a N k hN hk haa p w hw ζ hζ hfin χ₀
  have hG := hL.globalFns
  have hk1 : 1 ≤ k := by omega
  have hkN : 1 ≤ k * N := Nat.mul_pos hk1 hN
  have haa' : star a * a = (N : O) := by rw [mul_comm, haa]
  obtain ⟨m, hm⟩ := TWM.exists_liftO hϖ hv (D := D) p.g.b
  obtain ⟨σ, hσ, G₀, hG₀, x, hx, hval⟩ :=
    GlobalTheory.exists_integral_section_unit_at hL hTW V ϖ hϖ D Q hQ F v hv k hk χ₀ (m ≫ oa.onB.act a)
  have hQ0 : (0 : ℚ) ≤ Q χ₀ := by
    by_cases hχ : χ₀ = 0
    · subst hχ; rw [QForm.Q_zero hϖ D hQ]; simp
    · have := QForm.Q_pos hϖ D hQ hχ; exact_mod_cast (by omega : (0 : ℤ) ≤ Q χ₀)
  obtain ⟨c, hc⟩ := exists_val_eq_of_nonneg hv (div_nonneg hQ0 (Nat.cast_nonneg k))
  obtain ⟨s₀, rfl, hs₀⟩ := GlobalTheory.FamFree.exists_fam_single hG D.tau_bimult hk1 χ₀ σ
  have hsupp : ∀ β : D.toPre.X, (∀ mu, χ₀ + k • mu ≠ β) → ∀ j, ((c • s₀).s β).f j = 0 := fun β hβ j => by
    rw [smul_f, hs₀ β hβ j, mul_zero]
  have hnu : NuGe D Q F v k (c • s₀) 0 :=
    nuGe_of_single hϖ hQ hv hk1 _ χ₀ 0 hsupp (hσ.smul hc.ge fun j => rfl)
  refine ⟨c • s₀, hnu, fun s' t h hP hΦ hsm => ⟨?_, fun β hβ j => ?_, ?_⟩⟩
  · exact (galois_fixed_adelic_matrices_descend hL (TWM.tw_of hG hTW hVR) V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin s' t h hΦ hsm 0).1
      (pullback_valuation_forward_of (pullGen_of hG) (QuadraticAlgebraValuation.qAl_of hL) V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N hN haa haa' k hk1
        _ s' hP 0 hnu)
  · obtain ⟨α, rfl⟩ : ∃ α, α + p.y = β := ⟨β - p.y, sub_add_cancel _ _⟩
    have h1 : ∀ j, (s'.s α).f j = 0 := by
      by_cases hα : ∃ χ, α = star a • χ
      · obtain ⟨χ, rfl⟩ := hα
        refine pullAl_zero hP χ (hsupp χ ?_)
        rintro mu rfl
        refine hβ mu ?_
        rw [smul_add, smul_comm (star a) k mu]
        abel
      · exact hP.2 α fun χ e => hα ⟨χ, e⟩
    refine (hsm _ j).trans ?_
    rw [phiRel_zero hG hw hΦ α h1 j]
    exact mul_zero _
  · have hpull := GlobalTheory.pullAl_value_integral_point hL V ϖ hϖ D Q hQ F v hv O oa w0 hw0 a N k hN hk1 haa _ s' hP χ₀ m
      ((Q χ₀ : ℚ) / k) ⟨G₀, hG₀, c * x, by rw [AddValuation.map_mul, hc, hx, ← WithTop.coe_add, add_zero],
        fun z J hJ => by
          rw [sval_smul c s₀ χ₀ _ z hJ, hval z J hJ, ← Over.comp_left, lift_fst, Over.id_left, map_mul,
            gs_mul _ z ⊤ trivial, _root_.mul_assoc]⟩
    obtain ⟨y, hy, hvy⟩ := GlobalTheory.PhiValue.main hL hTW hVR hUU V ϖ hϖ D Q hQ F v hv (k * N) hkN p w hw ζ hζ hfin
      s' t h hΦ hsm (star a • χ₀) m hm _ hpull
    refine ⟨y, hy, hvy.trans (congrArg _ ?_)⟩
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [QuadraticAlgebraValuation.qAl_of hL V ϖ hϖ D Q hQ O oa a N haa haa' χ₀]
    push_cast
    field_simp
    ring

end GlobalTheory.ExactTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsAlgClosedAddValuationIsAdicComplete
namespace GlobalTheory

open scoped NNReal

theorem expNegTop_inj_of_eq {a b : WithTop ℚ} (h : expNegTop a = expNegTop b) : a = b :=
  le_antisymm ((expNegTop_le_iff _ _).1 h.ge) ((expNegTop_le_iff _ _).1 h.le)

noncomputable def expNegAbsoluteValue {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    AbsoluteValue F ℝ where
  toFun x := (expNegValuation v x : ℝ)
  map_mul' x y := by rw [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by rw [NNReal.coe_eq_zero, Valuation.zero_iff]
  add_le' x y := by
    have h := (expNegValuation v).map_add x y
    have h' : expNegValuation v (x + y) ≤ expNegValuation v x + expNegValuation v y :=
      h.trans (max_le le_self_add le_add_self)
    exact_mod_cast h'

theorem isNonarchimedean_expNegAbsoluteValue {F : Type} [Field F]
    (v : AddValuation F (WithTop ℚ)) : IsNonarchimedean (expNegAbsoluteValue v) := by
  intro x y
  have h := (expNegValuation v).map_add x y
  change ((expNegValuation v (x + y) : ℝ≥0) : ℝ) ≤
    max ((expNegValuation v x : ℝ≥0) : ℝ) ((expNegValuation v y : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem exists_norm_eq_of_completion {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : UniformSpace.Completion K) : ∃ y : K, ‖x‖ = ‖y‖ := by
  haveI : IsUltrametricDist (UniformSpace.Completion K) := IsUltrametricDist.of_normedAlgebra K
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (UniformSpace.Completion.denseRange_coe (α := K)) x
    ‖x‖ (norm_pos_iff.2 hx)
  refine ⟨y, ?_⟩
  rw [← UniformSpace.Completion.norm_coe y]
  rw [dist_comm, dist_eq_norm] at hy
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := y - x) hy.ne'
  rw [add_sub_cancel, max_eq_left hy.le] at h
  exact h.symm

theorem exists_addValuation_expNegTop_eq_nnnorm {C : Type} [NormedField C] [IsUltrametricDist C]
    (h : ∀ x : C, ∃ t : WithTop ℚ, expNegTop t = ‖x‖₊) :
    ∃ v : AddValuation C (WithTop ℚ), ∀ x, expNegTop (v x) = ‖x‖₊ := by
  choose f hf using h
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hf⟩
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_zero, expNegTop_top]
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_one, expNegTop_zero]
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.nnnorm_add_le_max x y) with h | h
    · exact min_le_of_left_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
    · exact min_le_of_right_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
  · intro x y
    apply expNegTop_inj_of_eq
    rw [expNegTop_add, hf, hf, hf, nnnorm_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVR
namespace GlobalTheory.ClosedValuedField

open scoped NNReal

theorem exists_isAlgClosed_forall_isAdicComplete (F₀ : Type) [Field F₀] [IsAlgClosed F₀]
    (v₀ : AddValuation F₀ (WithTop ℚ)) {a : F₀} (ha : a ≠ 0) (hv : 0 < v₀ a) :
    ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (e : F₀ →+* F)
      (v : AddValuation F (WithTop ℚ)), (∀ x, v (e x) = v₀ x) ∧
      ∀ b : ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v, 0 < v (b : F) →
        IsAdicComplete (Ideal.span {b}) (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  let w := expNegAbsoluteValue v₀
  have hw : ∀ x, w x = (expNegTop (v₀ x) : ℝ) := fun _ => rfl
  have hp1 : w a < 1 := by
    rw [hw, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le, expNegTop_le_iff]
    exact not_le.2 hv
  have hp0 : 0 < w a := w.pos ha
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w a)⁻¹, by
        rw [norm_inv]
        change 1 < (w a)⁻¹
        exact (one_lt_inv₀ hp0).2 hp1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_expNegAbsoluteValue v₀ x.ofAbs y.ofAbs
  haveI : IsAlgClosed (WithAbs w) := IsAlgClosed.of_ringEquiv F₀ _ (WithAbs.equiv w).symm
  let C := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField C := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := WithAbs w) UniformSpace.Completion.denseRange_coe
  let e : F₀ →+* C := (algebraMap (WithAbs w) C).comp (WithAbs.equiv w).symm.toRingHom
  have he : ∀ x, ‖e x‖₊ = expNegTop (v₀ x) := fun x =>
    NNReal.coe_injective (UniformSpace.Completion.norm_coe (WithAbs.toAbs w x))
  obtain ⟨v, hvC⟩ := exists_addValuation_expNegTop_eq_nnnorm (C := C) fun x => by
    obtain ⟨y, hy⟩ := exists_norm_eq_of_completion x
    exact ⟨v₀ y.ofAbs, NNReal.coe_injective hy.symm⟩
  have hmem : ∀ x : C, NormedField.valuation x ≤ 1 ↔ 0 ≤ v x := fun x => by
    rw [NormedField.valuation_apply, ← hvC, ← expNegTop_zero, expNegTop_le_iff]
  have hO : (NormedField.valuation (K := C)).Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) :=
    ⟨Subtype.val_injective, fun x => (hmem _).2 x.2, fun r hr => ⟨⟨r, (hmem r).1 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, e, v,
    fun x => expNegTop_inj_of_eq (by rw [hvC, he]), fun b hb =>
    NormIntegers.isAdicComplete_span_singleton hO (by
      change ‖(b : C)‖ < 1
      rw [← coe_nnnorm, ← hvC, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le,
        expNegTop_le_iff]
      exact not_le.2 hb)⟩

end GlobalTheory.ClosedValuedField

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.ClosedValuedField

theorem exists_field_over_cdvr : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → CharZero T.Fr → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v ∧ ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : Algebra T.V O) (_ : IsScalarTower T.V O F), Function.Injective (algebraMap O F) ∧ (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) ∧ ∀ g : ℕ, g ≠ 0 → ¬ IsUnit ((g : ℕ) : T.V) → IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O := by
  intro T ϖ hϖ _
  obtain ⟨v₀, hv₀⟩ := exists_valOver_of_isAlgebraic hϖ (AlgebraicClosure T.Fr)
  have hinj : Function.Injective (TWO.algVF (V := T.V) (F := AlgebraicClosure T.Fr)) :=
    (algebraMap T.Fr (AlgebraicClosure T.Fr)).injective.comp (IsFractionRing.injective T.V T.Fr)
  obtain ⟨F, _, _, e, v, he, hc⟩ := exists_isAlgClosed_forall_isAdicComplete
    (AlgebraicClosure T.Fr) v₀ ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero)
    (lt_of_lt_of_le zero_lt_one ((TWO.v_of_V v₀ hϖ hv₀ ϖ).2 hϖ.not_isUnit hϖ.ne_zero))
  letI : Algebra T.Fr F := (e.comp (algebraMap T.Fr (AlgebraicClosure T.Fr))).toAlgebra
  haveI : CharZero F := charZero_of_injective_ringHom (algebraMap T.Fr F).injective
  letI : Algebra T.V F := (TWO.algVF (V := T.V) (F := F)).toAlgebra
  haveI : IsScalarTower T.V T.Fr F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hv : ValOver ϖ F v := fun c n h => (he _).trans (hv₀ c n h)
  letI : Algebra T.V (TWO.Ov v) := (TWO.fO v hϖ hv).toAlgebra
  haveI : IsScalarTower T.V (TWO.Ov v) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, v, hv, TWO.Ov v, inferInstance, inferInstance, inferInstance, inferInstance,
    Subtype.val_injective, fun z => ⟨fun h => ⟨⟨z, h⟩, rfl⟩, ?_⟩, fun g hg hu => hc _ ?_⟩
  · rintro ⟨y, rfl⟩
    exact y.2
  · have h := (TWO.v_of_V v hϖ hv (g : T.V)).2 hu (Nat.cast_ne_zero.2 hg)
    rw [map_natCast] at h
    have e' : (((g : ℕ) : TWO.Ov v) : F) = (g : F) := map_natCast (algebraMap (TWO.Ov v) F) g
    rw [e']
    exact lt_of_lt_of_le zero_lt_one h

end GlobalTheory.ClosedValuedField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAlgClosedValuedFieldOverCompleteDVRStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosed_valuedField_over_completeDVR : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → CharZero T.Fr → ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (_ : Algebra T.Fr F) (_ : Algebra T.V F) (_ : IsScalarTower T.V T.Fr F) (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v ∧ ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : Algebra T.V O) (_ : IsScalarTower T.V O F), Function.Injective (algebraMap O F) ∧ (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) ∧ ∀ g : ℕ, g ≠ 0 → ¬ IsUnit ((g : ℕ) : T.V) → IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O := by
  first | exact @GlobalTheory.ClosedValuedField.exists_field_over_cdvr | exact GlobalTheory.ClosedValuedField.exists_field_over_cdvr | (intros; apply GlobalTheory.ClosedValuedField.exists_field_over_cdvr <;> assumption)
end
end
