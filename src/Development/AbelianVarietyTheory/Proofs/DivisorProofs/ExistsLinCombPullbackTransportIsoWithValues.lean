module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

section TransportLinComb

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]

theorem transChart_le (ψ : K → (X' ⟶ X)) (σ : I → (Y ⟶ X')) (jN : I × K → L.ι) (jM : I → L'.ι) (i : I) :
    LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) jN ⊓ LB.wchart L' σ jM ≤
      σ i ⁻¹ᵁ (LB.wchart L ψ (fun k => jN (i, k)) ⊓ L'.U (jM i)) :=
  fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (i, k), Set.mem_iInter.1 hy.2 i⟩

def transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X')) (e : I → ℤ) :
    LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) where
  s P := ∏ i, res (transChart_le ψ σ P.1 P.2 i) (pullU (σ i) _ (w.s (fun k => P.1 (i, k), P.2 i))) ^ e i

theorem gm_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) (r : Z ⟶ Y) (z : Z) (P : (I × K → L.ι) × (I → L'.ι))
    (hP : r z ∈ LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) P.1 ⊓ LB.wchart L' σ P.2) :
    gm r z _ ((transIso ψ δ w σ e).s P) = ∏ i, gm (r ≫ σ i) z _ (w.s (fun k => P.1 (i, k), P.2 i)) ^ e i := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => (map_zpow _ _ _).trans (congrArg (· ^ e i) ?_))
  exact (gm_res r z _ hP _).trans (gm_pull r (σ i) z _ (transChart_le ψ σ P.1 P.2 i hP) _)

theorem isGen_iff_gm' {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

theorem gm_of_isGen (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (r : Z ⟶ X') (z : Z) (P Q : (K → L.ι) × L'.ι)
    (hm : r z ∈ LB.wchart L ψ P.1 ⊓ L'.U P.2 ⊓ (LB.wchart L ψ Q.1 ⊓ L'.U Q.2)) :
    gm r z _ (w.s P) = ((∏ k, gm (r ≫ ψ k) z (L.U (P.1 k) ⊓ L.U (Q.1 k)) (L.g (P.1 k) (Q.1 k)) ^ δ k) *
      (gm r z _ (L'.g P.2 Q.2))⁻¹) * gm r z _ (w.s Q) := by
  have h := congrArg (gm r z _) (hw P Q)
  exact (gm_res r z _ hm _).symm.trans (h.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div L' (LB.LinComb L ψ δ) r z P Q hm).trans (congrArg (· * _) (gm_linComb L ψ δ r z _ _ hm.1.1 hm.2.1)))
    (gm_res r z _ hm _))))

theorem isGen_transIso (ψ : K → (X' ⟶ X)) (δ : K → ℤ) {w : LB.Iso L' (LB.LinComb L ψ δ)} (hw : w.IsGen)
    (σ : I → (Y ⟶ X')) (e : I → ℤ) : (transIso ψ δ w σ e).IsGen := by
  refine (isGen_iff_gm' _).2 fun P Q y hy => ?_
  have hd : gm (𝟙 Y) y ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U P ⊓ (LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).U Q) ((LB.div (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb L' σ e)).g P Q) = _ :=
    gm_div (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)) (𝟙 Y) y P Q hy
  rw [gm_transIso ψ δ w σ e (𝟙 Y) y P hy.1, gm_transIso ψ δ w σ e (𝟙 Y) y Q hy.2,
    hd]
  erw [gm_linComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2) (𝟙 Y) y P.1 Q.1 hy.1.1 hy.2.1,
    gm_linComb L' σ e (𝟙 Y) y P.2 Q.2 hy.1.2 hy.2.2,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ e i) (gm_of_isGen ψ δ hw (𝟙 Y ≫ σ i) y
      (fun k => P.1 (i, k), P.2 i) (fun k => Q.1 (i, k), Q.2 i)
      ⟨transChart_le ψ σ P.1 P.2 i hy.1, transChart_le ψ σ Q.1 Q.2 i hy.2⟩)]
  rw [Fintype.prod_prod_type]
  simp only [Category.assoc, mul_zpow, Finset.prod_mul_distrib, ← Finset.prod_zpow, ← zpow_mul, inv_zpow',
    Finset.prod_inv_distrib]
  simp only [mul_comm (δ _) (e _)]
  simp only [zpow_neg, Finset.prod_inv_distrib]
  rfl

end TransportLinComb

theorem exists_transIso_linComb : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I]
    (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB →
    ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e)
      (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) =
          ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  intro X X' Y L L' K I _ _ ψ δ w hw _ _ σ e
  refine ⟨transIso ψ δ w σ e, isGen_transIso ψ δ hw σ e, fun Z q z J J' hJ hJ' => ?_⟩
  exact gm_transIso ψ δ w σ e q z _ ⟨hJ.mem (fun p : I × K => σ p.1 ≫ ψ p.2) q, hJ'.mem σ q⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linCombPullbackTransportIso_with_values : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {K I : Type} [Fintype K] [Fintype I] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (w : LB.Iso L' (LB.LinComb L ψ δ)), w.IsGen → L.IsLB → L'.IsLB → ∀ (σ : I → (Y ⟶ X')) (e : I → ℤ), ∃ v : LB.Iso (LB.LinComb L' σ e) (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' → gm q z _ (v.s (fun p => J (q ≫ σ p.1 ≫ ψ p.2), fun i => J' (q ≫ σ i))) = ∏ i, gm (q ≫ σ i) z _ (w.s (fun k => J (q ≫ σ i ≫ ψ k), J' (q ≫ σ i))) ^ e i := by
  first | exact @GlobalTheory.Mum.exists_transIso_linComb | exact GlobalTheory.Mum.exists_transIso_linComb | (intros; apply GlobalTheory.Mum.exists_transIso_linComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomProperties
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TensAct

section General

variable {S : Scheme.{0}} {X Y Z G : Over S}

def preHom [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) : (Y ⟶ G) →* (X ⟶ G) where
  toFun g := f ≫ g
  map_one' := MonObj.comp_one f
  map_mul' := fun g h => MonObj.comp_mul f g h

theorem comp_prod_zpow [GrpObj G] [IsCommMonObj G] (f : X ⟶ Y) {K : Type} [Fintype K] (g : K → (Y ⟶ G)) (n : K → ℤ) :
    f ≫ (∏ j, g j ^ n j) = ∏ j, (f ≫ g j) ^ n j := by
  show preHom f (∏ j, g j ^ n j) = ∏ j, (preHom f (g j)) ^ n j
  rw [map_prod]
  simp only [map_zpow]

end General

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem hom_ext (T : Tens D D' W) {X} {f g : X ⟶ D'.P.A} (h : ∀ i, f ≫ T.pr i = g ≫ T.pr i) : f = g :=
  T.lim.hom_ext fun ⟨i⟩ => h i

theorem comp_act_pr (T : Tens D D' W) {X} (f : X ⟶ D'.P.A) (a : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) :
    f ≫ T.act a ≫ T.pr i = ∏ j, (f ≫ T.pr j) ^ a i j := by
  rw [Tens.act_pr, comp_prod_zpow]

theorem act_isMonHom (T : Tens D D' W) (a : Matrix (Fin r) (Fin r) ℤ) : IsMonHom (T.act a) := by
  haveI := T.pr_hom
  have h1 : ∀ {X} , (1 : X ⟶ D'.P.A) ≫ T.act a = 1 := by
    intro X
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr]
    simp [MonObj.one_comp]
  have h2 : ∀ {X} (f g : X ⟶ D'.P.A), (f * g) ≫ T.act a = (f ≫ T.act a) * (g ≫ T.act a) := by
    intro X f g
    refine hom_ext T fun i => ?_
    rw [Category.assoc, comp_act_pr, MonObj.mul_comp, Category.assoc, Category.assoc, comp_act_pr, comp_act_pr,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [MonObj.mul_comp, mul_zpow]
  constructor
  · have := h1 (X := 𝟙_ _)
    simpa [Hom.one_def] using this
  · have := h2 (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

theorem act_one (T : Tens D D' W) : T.act 1 = 𝟙 _ := by
  refine hom_ext T fun i => ?_
  rw [Tens.act_pr, Category.id_comp, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, zpow_zero]
  · simp

theorem act_mul (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) : T.act (a * b) = T.act b ≫ T.act a := by
  refine hom_ext T fun i => ?_
  rw [Category.assoc, comp_act_pr, Tens.act_pr]
  simp only [Tens.act_pr, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  have : ∀ (s : Finset (Fin r)) (n : Fin r → ℤ), T.pr k ^ (∑ j ∈ s, n j) = ∏ j ∈ s, T.pr k ^ n j := by
    intro s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]
  rw [this]
  simp only [mul_comm]

theorem act_add (T : Tens D D' W) (a b : Matrix (Fin r) (Fin r) ℤ) :
    T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  haveI := T.pr_hom
  show _ = T.act a * T.act b
  refine hom_ext T fun i => ?_
  rw [MonObj.mul_comp]
  simp only [Tens.act_pr, Matrix.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem act_ring : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧
      ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) :=
  fun _ _ _ _ _ _ _ T => ⟨act_isMonHom T, act_one T, act_mul T, act_add T⟩

end GlobalTheory.Mum.TensAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataMatrixActionRingHomPropertiesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordTensorData_matrixAction_ringHom_properties : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D D' W), (∀ a, IsMonHom (T.act a)) ∧ T.act 1 = 𝟙 _ ∧ (∀ a b, T.act (a * b) = T.act b ≫ T.act a) ∧ ∀ a b, T.act (a + b) = padd D'.P.A (T.act a) (T.act b) := by
  first | exact @GlobalTheory.Mum.TensAct.act_ring | exact GlobalTheory.Mum.TensAct.act_ring | (intros; apply GlobalTheory.Mum.TensAct.act_ring <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeIntStalkOfArithBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.ZH.RatModel

theorem essFiniteType_int_stalk_of_arithBase {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω]
    [hA : ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z) :
    Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o' := M.s x
  letI A : Algebra o' ((Sp o').presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o' _ ((Sp o').presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o' ((Sp o').presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h := ((h₀.comp h₂).comp h₁)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h
  exact RingHom.ext_int _ _

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueChar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem exists_prime_eq_zero_of_finiteType (κ : Type) [Field κ] [Algebra.FiniteType ℤ κ] :
    ∃ p : ℕ, p.Prime ∧ (p : κ) = 0 := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : Module.Finite ℤ κ := finite_of_finite_type_of_isJacobsonRing ℤ κ
  obtain ⟨q, hq⟩ := CharP.exists κ
  rcases CharP.char_is_prime_or_zero κ q with hqp | hq0
  · exact ⟨q, hqp, CharP.cast_eq_zero κ q⟩
  · subst hq0
    haveI : CharZero κ := CharP.charP_to_charZero κ
    exact absurd (isField_of_isIntegral_of_isField (R := ℤ) (S := κ) (algebraMap ℤ κ).injective_int (Field.toIsField κ))
      Int.not_isField

theorem isLocalHom_of_isCpl {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] {j : O →+* R} (h : IsCpl j) :
    IsLocalHom j := by
  obtain ⟨e, he⟩ := h
  refine ⟨fun a ha => ?_⟩
  rw [← he] at ha
  have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
    simpa using ha.map e.symm
  have h2 := h1.map (AdicCompletion.evalₐ (maximalIdeal O) 1)
  rw [AlgHom.commutes] at h2
  by_contra hn
  have hm : a ∈ maximalIdeal O ^ 1 := by rw [pow_one]; exact hn
  have h0 : algebraMap O (O ⧸ maximalIdeal O ^ 1) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ 1) :=
    Ideal.Quotient.nontrivial_iff.2 (by rw [pow_one]; exact (maximalIdeal.isMaximal O).ne_top)
  rw [h0] at h2
  exact not_isUnit_zero h2

theorem finiteType_residueField {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    (M : RatModel o' Ω) (x : M.Z) (hx : IsClosed ({x} : Set M.Z)) :
    Algebra.FiniteType ℤ (M.Z.residueField x) := by
  haveI : LocallyOfFiniteType M.s := M.lft
  haveI : IsClosedImmersion (M.Z.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.1 hx
  have h : LocallyOfFiniteType (M.Z.fromSpecResidueField x ≫ M.s) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of o') (M.Z.fromSpecResidueField x ≫ M.s)
  rw [← hφ] at h
  have h₁ : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ o' := hA.ft
  have h₀ : (algebraMap ℤ o').FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  rw [← RingHom.finiteType_algebraMap]
  convert h₁.comp h₀
  exact RingHom.ext_int _ _

theorem closedPoint_cpl_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  intro o' Ω _ _ _ _ M x hx
  refine ⟨RatModel.essFiniteType_int_stalk_of_arithBase M x, fun R _ _ j hj => ?_⟩
  haveI hl := isLocalHom_of_isCpl hj
  refine ⟨hl, ?_⟩
  haveI := finiteType_residueField M x hx
  obtain ⟨p, hp, h0⟩ := exists_prime_eq_zero_of_finiteType (M.Z.residueField x)
  refine ⟨p, hp, ?_⟩
  have hm : (p : M.Z.presheaf.stalk x) ∈ maximalIdeal (M.Z.presheaf.stalk x) := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact h0
  rw [← map_natCast j p]
  exact map_nonunit j _ hm

end GlobalTheory.UPoinc.ClosedPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueCharStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_completion_positive_residueChar : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsLocalHom j ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ maximalIdeal R := by
  first | exact @GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar | exact GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar | (intros; apply GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechKS

theorem Pt.nonempty_affHom_of_in {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s) (h : P.In U.1) :
    Nonempty ((Pt.aff s U).Hom P) := by
  let φ := GlobalTheory.Points.valMap P.x U.1 h
  have hc : ∀ r : R, φ.hom (algebraMap R (CechDR.Sec s U.1) r) = algebraMap R P.B r := by
    intro r
    change φ.hom ((s.appLE ⊤ U.1 le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    rw [← GlobalTheory.Points.valR_eq P.x U.1 h, GlobalTheory.Points.valR_appLE P.x s le_top h, P.w,
      GlobalTheory.Points.valR_specMap]
    rfl
  refine ⟨⟨{ φ.hom with commutes' := hc }, ?_⟩⟩
  exact GlobalTheory.Points.specMap_valMap_fromSpec U.2 P.x h

theorem Pt.affHom_ρ_eq_valR {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a : (Pt.aff s U).Hom P) (b : Γ(X, U.1)) : a.ρ b = valR P.x U.1 b := by
  have hpre : ⊤ ≤ (CechDR.affPt s U) ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  have hid : valR (CechDR.affPt s U) U.1 b = b := by
    rw [GlobalTheory.Points.valR_eq _ _ hpre]
    have h1 : Spec.map (𝟙 Γ(X, U.1)) ≫ U.2.fromSpec = CechDR.affPt s U := by
      rw [Spec.map_id, Category.id_comp]; rfl
    have h2 := GlobalTheory.Points.valMap_specMap_fromSpec U.2 (𝟙 Γ(X, U.1)) (h1 ▸ hpre)
    have h3 : GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre = 𝟙 _ := by
      have key : ∀ (x : Spec Γ(X, U.1) ⟶ X) (hx : x = CechDR.affPt s U) (h : ⊤ ≤ x ⁻¹ᵁ U.1),
          GlobalTheory.Points.valMap x U.1 h = GlobalTheory.Points.valMap (CechDR.affPt s U) U.1 hpre := by
        rintro _ rfl _; rfl
      exact (key _ h1 _).symm.trans h2
    rw [h3]; rfl
  rw [← a.pt, GlobalTheory.Points.valR_spMap_comp _ _ _ hpre, hid]
  rfl

theorem eq_of_valR_eq_on_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {J : Type} (W : J → X.Opens)
    (hW : ⨆ j, W j = ⊤) (V : X.Opens) (f g : Γ(X, V))
    (h : ∀ (P : Pt s) (j : J), P.In V → P.In (W j) → valR P.x V f = valR P.x V g) : f = g := by
  refine TopCat.Presheaf.section_ext X.sheaf V f g fun x hx ↦ ?_
  have hxW : x ∈ ⨆ j, W j := by rw [hW]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxW
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ W j) ⟨hx, hj⟩
  have hle : U' ≤ V ⊓ W j := hsub
  have hleV : U' ≤ V := hle.trans inf_le_left
  let Ua : X.affineOpens := ⟨U', hU'⟩
  have hPU : (Pt.aff s Ua).In U' := hU'.fromSpec_preimage_self.ge
  have hv := h (Pt.aff s Ua) j (hPU.mono hleV) (hPU.mono (hle.trans inf_le_right))
  have key : ∀ b : Γ(X, V), valR (Pt.aff s Ua).x V b = (X.presheaf.map (homOfLE hleV).op).hom b := by
    intro b
    rw [← GlobalTheory.Points.valR_res (Pt.aff s Ua).x hleV hPU b]
    exact (Pt.affHom_ρ_eq_valR s Ua (Pt.aff s Ua) (Pt.Hom.id _) _).symm
  rw [key, key] at hv
  have := congrArg (X.presheaf.germ U' x hxU') hv
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at this

theorem Pt.affHom_subsingleton {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) (P : Pt s)
    (a a' : (Pt.aff s U).Hom P) : a = a' := by
  obtain ⟨ρ, e⟩ := a
  obtain ⟨ρ', e'⟩ := a'
  have : ρ = ρ' := AlgHom.ext fun b ↦ (Pt.affHom_ρ_eq_valR s U P ⟨ρ, e⟩ b).trans (Pt.affHom_ρ_eq_valR s U P ⟨ρ', e'⟩ b).symm
  subst this; rfl

theorem Pt.Hom.comp_triv {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {P Q T : Pt s}
    (φ : P.Hom Q) (ψ : Q.Hom T) : (φ.comp ψ).triv = φ.triv ≫ ψ.triv :=
  Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)

theorem h1_mk_mem_f1_of_isRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  intro R _ X s J W hW c hc
  obtain ⟨G, hG1, hG2⟩ := hc
  have hG : ∀ j j' (P : Pt s), P.In (W j) → P.In (W j') → G j P = G j' P := fun j j' P h h' ↦
    sub_eq_zero.1 (hG2 j j' P h h')
  change toH1O s (H1.mk _ c) = 0
  refine (injective_iff_map_eq_zero (GlobalTheory.CechDR.cmpO s)).1
    (GlobalTheory.CechDR.cmpO_injective R X s) _ ?_
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine H1.mk_eq_zero.2 ?_
  classical
  let aP : ∀ (U : X.affineOpens) (P : Pt s), P.In U.1 → (Pt.aff s U).Hom P :=
    fun U P h ↦ (Pt.nonempty_affHom_of_in s U P h).some
  let FU : X.affineOpens → PtFn s := fun U P ↦
    if h : P.In U.1 ∧ ∃ j, P.In (W j) then G h.2.choose P - ev c (aP U P h.1).triv else 0
  have FU_eq : ∀ U (P : Pt s) j (hU : P.In U.1), P.In (W j) → FU U P = G j P - ev c (aP U P hU).triv := by
    intro U P j hU hj
    have h : P.In U.1 ∧ ∃ j, P.In (W j) := ⟨hU, j, hj⟩
    simp only [FU, dif_pos h]
    rw [hG _ j P h.2.choose_spec hj]
  have ex : ∀ U : X.affineOpens, ∃ f : Γ(X, U.1), ∀ (j : J) (P : Pt s), P.In (U.1 ⊓ W j) →
      FU U P = valR P.x U.1 f := by
    intro U
    refine GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover R X s J (fun j ↦ U.1 ⊓ W j) U.1 (fun j ↦ inf_le_left) ?_ (FU U) ?_
    · rw [← inf_iSup_eq, hW, inf_top_eq]
    · intro j P Q φ hP
      have hU : P.In U.1 := hP.mono inf_le_left
      have hj : P.In (W j) := hP.mono inf_le_right
      rw [FU_eq U P j hU hj, FU_eq U Q j (hU.map φ) (hj.map φ),
        Pt.affHom_subsingleton s U Q (aP U Q (hU.map φ)) ((aP U P hU).comp φ), Pt.Hom.comp_triv, ev_comp,
        hG1 j P Q φ hj, map_sub]
      have e : φ.triv.φ (ev c (aP U P hU).triv) = φ.ρ (ev c (aP U P hU).triv) := rfl
      rw [e]; ring
  choose f hf using ex
  refine ⟨fun U ↦ f U.unop, ?_⟩
  funext U V a
  have hle : V.unop.1 ≤ U.unop.1 := leOfHom a.unop
  refine eq_of_valR_eq_on_cover s W hW V.unop.1 _ _ fun P j hV hj ↦ ?_
  change valR P.x V.unop.1 (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
    (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) = valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv)
  have hU : P.In U.unop.1 := hV.mono hle
  set b := aP V.unop P hV
  have e1 : valR P.x V.unop.1 (f V.unop) = FU V.unop P := (hf V.unop j P (hV.inf hj)).symm
  have e2 : valR P.x V.unop.1 (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) = FU U.unop P :=
    (GlobalTheory.Points.valR_res P.x hle hV (f U.unop)).trans (hf U.unop j P (hU.inf hj)).symm
  have e3 : aP U.unop P hU = (Pt.affHom s hle).comp b := Pt.affHom_subsingleton s _ P _ _
  have e4 : ev c (aP U.unop P hU).triv = b.ρ (ev c (Pt.affHom s hle).triv) + ev c b.triv := by
    rw [e3, Pt.Hom.comp_triv, ev_comp]; rfl
  have e5 : valR P.x V.unop.1 (ev c (Pt.affHom s hle).triv) = b.ρ (ev c (Pt.affHom s hle).triv) :=
    (Pt.affHom_ρ_eq_valR s V.unop P b _).symm
  have e6 : b.ρ (@HSub.hSub Γ(X, V.unop.1) Γ(X, V.unop.1) Γ(X, V.unop.1) _ (f V.unop)
      (GlobalTheory.CechDR.Sec.res s hle (f U.unop))) =
      b.ρ (f V.unop) - b.ρ (GlobalTheory.CechDR.Sec.res s hle (f U.unop)) := map_sub b.ρ _ _
  rw [e5, ← Pt.affHom_ρ_eq_valR s V.unop P b, e6, Pt.affHom_ρ_eq_valR s V.unop P b (f V.unop),
    Pt.affHom_ρ_eq_valR s V.unop P b (GlobalTheory.CechDR.Sec.res s hle (f U.unop)), e1, e2,
    FU_eq V.unop P j hV hj, FU_eq U.unop P j hU hj, e4]
  ring

end GlobalTheory.CechKS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZeroStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineClass_mem_hodgeFiltration_of_cechRep_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) (W : J → X.Opens), ⨆ j, W j = ⊤ → ∀ c : Z1 (O (dp0 R) s), IsRep W c 0 → H1.mk _ c ∈ F1 s := by
  first | exact @GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero | exact GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero | (intros; apply GlobalTheory.CechKS.h1_mk_mem_f1_of_isRep_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorMatchIdOneMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

attribute [local instance] GlobalTheory.TorusExt.gtGroup

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

theorem alg_eq {R F : Type} [CommRing R] [IsDomain R] [Field F] (i₁ i₂ : Algebra (FractionRing R) F)
    (h : ∀ r, @algebraMap _ _ _ _ i₁ (algebraMap R (FractionRing R) r) =
      @algebraMap _ _ _ _ i₂ (algebraMap R (FractionRing R) r)) : i₁ = i₂ := by
  apply Algebra.algebra_ext
  intro x
  have e := IsLocalization.ringHom_ext (M := nonZeroDivisors R) (S := FractionRing R)
    (j := @algebraMap _ _ _ _ i₁) (k := @algebraMap _ _ _ _ i₂) (RingHom.ext h)
  exact RingHom.congr_fun e x

theorem qk_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {k : ℕ} {q q' : QkPt D F k} (hy : q.y = q'.y) (hg : q.g = q'.g) : q = q' := by
  cases q; cases q'; cases hy; cases hg; rfl

theorem tor_eq {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {τ : Multiplicative D.X →* Fˣ} {g : GtPtF D F} (h : GlobalTheory.UT.IsTor τ g) :
    g = GlobalTheory.TorusExt.torusPt D F (Additive.ofMul τ) :=
  (GlobalTheory.TorusExt.isTorusPtF_iff_eq g τ).1 ((GlobalTheory.UT.isTor_iff τ g).1 h)

theorem one_le_of_isUnit {R : Type} [CommRing R] [IsDomain R] {k : ℕ} (hk : IsUnit (k : R)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp at hk
  · exact h

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem tors_fun (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] {k : ℕ} (hk : IsUnit (k : R)) :
    ∃ f : QkPt D.toPre F k → (TFK (R := R) F ⟶ A.A), (∀ p x, QkToAkU U.toUnifPre F k p x ↔ x = f p) ∧
      (∀ p p', f p = f p' ↔ QkPt.Equiv D.toPre F p p') ∧ (∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') := by
  haveI := hR.2
  obtain ⟨f, ⟨h1, -, h3, h4, -⟩, -⟩ :=
    GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR.1 D A G hG U F k (one_le_of_isUnit hk)
  exact ⟨f, h1, h3, h4⟩

theorem push {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))}
    (U : Unif (maximalIdeal R) D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    ∃ e : (TFK (R := R) F ⟶ A.A) ≃* (Over.mk (jFK (R := R) F ≫ jK R) ⟶ G), ∀ x, (e x).left = x.left ≫ genMap U :=
  GlobalTheory.LiePull.exists_pushEquiv (GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre) (TFK (R := R) F) _ rfl

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8.TorMatchLaws

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem torMatch_id (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G) :
    TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, -, -⟩ := tors_fun hR hG U F hk
  have e : τ = τ' := MonoidHom.ext fun x => hρ (Multiplicative.toAdd x)
  subst e
  have hqq : q = q' := qk_eq (hy.trans hy'.symm) ((tor_eq hτ).trans (tor_eq hτ').symm)
  subst hqq
  rw [(h1 q a).1 hq, (h1 q a').1 hq', Category.comp_id]

theorem torMatch_one (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') :
    TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' _ hρ hy hτ _ _ hq _
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  have e : τ = 1 := MonoidHom.ext fun x => by
    rw [MonoidHom.one_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.zero_apply, ofAdd_zero, map_one]
  subst e
  have hg : q.g = 0 := by rw [tor_eq hτ, ofMul_one, map_zero]
  have hadd : QkAdd q q q := ⟨q, by rw [hy, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (by rw [hg, add_zero]),
    (h3 q q).1 rfl⟩
  have ha : a = 1 := by
    rw [(h1 q a).1 hq]
    exact mul_eq_left.1 (h4 q q q hadd).symm
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have key : eU a = eU' a' ≫ (1 : G' ⟶ G) := by rw [comp_one, ha, map_one]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

theorem torMatch_mul (hR : GlobalTheory.Mum.Base R) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} (U : Unif (maximalIdeal R) D A G)
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {D' : DegData R (maximalIdeal R)} {A' : PolAV (Sp (FractionRing R))}
    (U' : Unif (maximalIdeal R) D' A' G') (p p' : G' ⟶ G) (ρ ρ' : D.toPre.X →+ D'.toPre.X)
    (hp : TorMatch U U' (RingHom.id R) p.left ρ) (hp' : TorMatch U U' (RingHom.id R) p'.left ρ') :
    TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro F _ _ i₁ i₂ hF
  obtain rfl : i₁ = i₂ := alg_eq i₁ i₂ hF
  intro k hk τ τ' q q' a a' hτk hρ hy hτ hy' hτ' hq hq'
  obtain ⟨f, h1, h3, h4⟩ := tors_fun hR hG U F hk
  let τ₁ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ)
  let τ₂ : Multiplicative D.toPre.X →* Fˣ := τ'.comp (AddMonoidHom.toMultiplicative ρ')
  have pw : ∀ σ : D.toPre.X →+ D'.toPre.X, (τ'.comp (AddMonoidHom.toMultiplicative σ)) ^ k = 1 := fun σ =>
    MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hτk, MonoidHom.one_apply,
        MonoidHom.one_apply]
  obtain ⟨q₁, hy₁, hτ₁⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₁ (pw ρ)
  obtain ⟨q₂, hy₂, hτ₂⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor D.tau_bimult τ₂ (pw ρ')
  have e₁ := hp F hF k hk τ₁ τ' q₁ q' (f q₁) a' hτk (fun _ => rfl) hy₁ hτ₁ hy' hτ' ((h1 q₁ _).2 rfl) hq'
  have e₂ := hp' F hF k hk τ₂ τ' q₂ q' (f q₂) a' hτk (fun _ => rfl) hy₂ hτ₂ hy' hτ' ((h1 q₂ _).2 rfl) hq'
  have hτe : τ = τ₁ * τ₂ := MonoidHom.ext fun x => by
    rw [MonoidHom.mul_apply]
    refine (hρ (Multiplicative.toAdd x)).trans ?_
    rw [AddMonoidHom.add_apply, ofAdd_add, map_mul]
    rfl
  have hg : q.g = q₁.g + q₂.g := by
    rw [tor_eq hτ, tor_eq hτ₁, tor_eq hτ₂, hτe, ofMul_mul, map_add (f := _)]
  have hadd : QkAdd q₁ q₂ q := ⟨q, by rw [hy, hy₁, hy₂, add_zero], (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 hg,
    (h3 q q).1 rfl⟩
  have ha : a = f q₁ * f q₂ := by rw [(h1 q a).1 hq]; exact h4 q₁ q₂ q hadd
  obtain ⟨eU, heU⟩ := push U F
  obtain ⟨eU', heU'⟩ := push U' F
  have k₁ : eU (f q₁) = eU' a' ≫ p := Over.OverMorphism.ext (by rw [heU, e₁, Over.comp_left, heU', Category.assoc])
  have k₂ : eU (f q₂) = eU' a' ≫ p' := Over.OverMorphism.ext (by rw [heU, e₂, Over.comp_left, heU', Category.assoc])
  have key : eU a = eU' a' ≫ (p * p') := by rw [comp_mul, ha, map_mul, k₁, k₂]
  rw [← heU, key, Over.comp_left, heU', Category.assoc]

end GlobalTheory.Poinc.Eq8.TorMatchLaws

namespace GlobalTheory.Poinc.Eq8


open TorMatchLaws in
theorem torMatch_id_one_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G'), TorMatch U U (RingHom.id R) (𝟙 G.left) (AddMonoidHom.id _) ∧ TorMatch U U' (RingHom.id R) (1 : G' ⟶ G).left 0 ∧ ∀ (p p' : G' ⟶ G) ρ ρ', TorMatch U U' (RingHom.id R) p.left ρ → TorMatch U U' (RingHom.id R) p'.left ρ' → TorMatch U U' (RingHom.id R) (p * p').left (ρ + ρ') := by
  intro R _ _ _ hR G _ _ hG D A U G' _ _ _ D' A' U'
  exact ⟨torMatch_id hR hG U, torMatch_one hR hG U U', fun p p' ρ ρ' hp hp' => torMatch_mul hR hG U U' p p' ρ ρ' hp hp'⟩

end GlobalTheory.Poinc.Eq8
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.LinCombComp

variable {X Y Z : Scheme.{0}}

theorem gm_gen {M : LB Y} {t : LB.Gen M} (ht : t.IsGen) (f : Z ⟶ Y) (z : Z) {i j : M.ι}
    (hi : f z ∈ M.U i) (hj : f z ∈ M.U j) :
    gm f z (M.U i) (t.s i) = gm f z (M.U i ⊓ M.U j) (M.g i j) * gm f z (M.U j) (t.s j) := by
  have hm : f z ∈ M.U i ⊓ M.U j := ⟨hi, hj⟩
  exact (gm_res f z _ hm _).symm.trans ((congrArg (gm f z _) (ht i j)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res f z _ hm _))))

theorem gm_div (M N : LB Y) (f : Z ⟶ Y) (z : Z) (p q : (LB.div M N).ι)
    (hp : f z ∈ (LB.div M N).U p) (hq : f z ∈ (LB.div M N).U q) :
    gm f z ((LB.div M N).U p ⊓ (LB.div M N).U q) ((LB.div M N).g p q) =
      gm f z (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) * (gm f z (N.U p.2 ⊓ N.U q.2) (N.g p.2 q.2))⁻¹ := by
  have hm : f z ∈ (LB.div M N).U p ⊓ (LB.div M N).U q := ⟨hp, hq⟩
  show gm f z _ (res _ (M.g p.1 q.1) * (res _ (N.g p.2 q.2))⁻¹) = _
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f z _ hm _)
    ((map_inv _ _).trans (congrArg _ (gm_res f z _ hm _))))

theorem trF_self {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) : trF φ ε r z j j = 1 :=
  Finset.prod_eq_one fun k _ => by
    rw [gm_self hL (r ≫ φ k) z (Set.mem_iInter.1 hj k), one_zpow]

theorem trF_sum {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ)
    (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (r : Z ⟶ Y) (z : Z) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) :
    trF (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)) r z (Sum.elim j₁ j₀) (Sum.elim j₁' j₀') =
      trF φ₁ ε₁ r z j₁ j₁' * (trF φ₀ ε₀ r z j₀ j₀')⁻¹ := by
  rw [trF, trF, trF, Fintype.prod_sum_type, ← Finset.prod_inv_distrib]
  congr 1
  exact Finset.prod_congr rfl fun k _ => zpow_neg _ _

theorem wchart_sum_le (L : LB X) {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X))
    (φ₁ : K₁ → (Y ⟶ X)) (j₁ : K₁ → L.ι) (j₀ : K → L.ι) :
    LB.wchart L φ₁ j₁ ⊓ LB.wchart L φ₀ j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) :=
  fun _ hy => Set.mem_iInter.2 fun k => by
    cases k with
    | inl k => exact Set.mem_iInter.1 hy.1 k
    | inr k => exact Set.mem_iInter.1 hy.2 k

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_iso_linComb {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K : Type} [Fintype K]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (y : Y) (j₀ j₀' : K → L.ι) (a a' : A.ι) (h0 : y ∈ LB.wchart L φ₀ j₀) (ha : y ∈ A.U a)
    (h0' : y ∈ LB.wchart L φ₀ j₀') (ha' : y ∈ A.U a') :
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) =
      (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹) *
        gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a')) := by
  have hp : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀, a) := ⟨h0, ha⟩
  have hq : (𝟙 Y) y ∈ (LB.div (LB.LinComb L φ₀ ε₀) A).U (j₀', a') := ⟨h0', ha'⟩
  have e1 := gm_gen hu (𝟙 Y) y hp hq
  have e2 := gm_div (LB.LinComb L φ₀ ε₀) A (𝟙 Y) y (j₀, a) (j₀', a') hp hq
  have e3 : gm (𝟙 Y) y (LB.wchart L φ₀ j₀ ⊓ LB.wchart L φ₀ j₀') ((LB.LinComb L φ₀ ε₀).g j₀ j₀') =
      trF φ₀ ε₀ (𝟙 Y) y j₀ j₀' := gm_linComb L φ₀ ε₀ (𝟙 Y) y j₀ j₀' h0 h0'
  rw [e2] at e1
  exact e1.trans (congrArg (fun t => t * (gm (𝟙 Y) y (A.U a ⊓ A.U a') (A.g a a'))⁻¹ *
    gm (𝟙 Y) y (LB.wchart L φ₀ j₀' ⊓ A.U a') (u.s (j₀', a'))) e3)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem gm_gen_sum {X Y : Scheme.{0}} {L : LB X} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen)
    (y : Y) (j₁ j₁' : K₁ → L.ι) (j₀ j₀' : K → L.ι) (h1 : y ∈ LB.wchart L φ₁ j₁) (h0 : y ∈ LB.wchart L φ₀ j₀)
    (h1' : y ∈ LB.wchart L φ₁ j₁') (h0' : y ∈ LB.wchart L φ₀ j₀') :
    gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) =
      (trF φ₁ ε₁ (𝟙 Y) y j₁ j₁' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
        gm (𝟙 Y) y (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁' j₀')) (c.s (Sum.elim j₁' j₀')) := by
  rw [← trF_sum]
  exact gen_trans hc (𝟙 Y) y (wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨h1, h0⟩) (wchart_sum_le L φ₀ φ₁ j₁' j₀' ⟨h1', h0'⟩)

end GlobalTheory.LinCombComp

namespace GlobalTheory.LinCombComp

theorem exists_iso_comp_val {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁]
    (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (hL : L.IsLB) (hA : A.IsLB)
    (u : LB.Iso A (LB.LinComb L φ₀ ε₀)) (hu : u.IsGen)
    (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))) (hc : c.IsGen) :
    ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z)
      (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J →
      gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  have eu := gm_iso_linComb φ₀ ε₀ u hu
  have ec := gm_gen_sum φ₀ ε₀ φ₁ ε₁ c hc
  have glue : ∀ (j₁ : K₁ → L.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart L φ₁ j₁ ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι), q z ∈ LB.wchart L φ₁ j₁ → q z ∈ A.U a →
        q z ∈ LB.wchart L φ₀ j₀ →
        gm q z (LB.wchart L φ₁ j₁ ⊓ A.U a) s =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j₁ a
    obtain ⟨W, hW⟩ : ∃ W : (K → L.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart L φ₁ j₁ ⊓ A.U a ⊓ LB.wchart L φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart L φ₁ j₁ ⊓ A.U a := fun j₀ => (hW j₀).le.trans inf_le_left
    have l₁ : ∀ j₀, W j₀ ≤ LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀) := fun j₀ y hy => by
      rw [hW] at hy; exact wchart_sum_le L φ₀ φ₁ j₁ j₀ ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L φ₀ j₀ ⊓ A.U a := fun j₀ y hy => by
      rw [hW] at hy; exact ⟨hy.2, hy.1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K → L.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z (LB.wchart L (Sum.elim φ₁ φ₀) (Sum.elim j₁ j₀)) (c.s (Sum.elim j₁ j₀)) *
            gm q z (LB.wchart L φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (c.s (Sum.elim j₁ j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart L φ₁ j₁ ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart L φ₁ j₁ ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ec y j₁ j₁ j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha, trF_self hL φ₁ ε₁ (𝟙 Y) y j₁ h1,
          gm_self hA (𝟙 Y) y ha, _root_.one_mul, _root_.inv_one, _root_.mul_one, _root_.mul_mul_mul_comm, _root_.inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J a ha hJ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL (φ₀ k y)
    have h0 : y ∈ LB.wchart L φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart L φ₁ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ₁ ε₁ (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart L φ₁ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ec y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha', trF_self hL φ₀ ε₀ (𝟙 Y) y j₀ h0,
        _root_.inv_one, _root_.mul_one, _root_.one_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
    have hm : y ∈ (LB.div (LB.LinComb L φ₁ ε₁) A).U p ⊓ (LB.div (LB.LinComb L φ₁ ε₁) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb L φ₁ ε₁ (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · have h1 := hJ.mem φ₁ q
    have h0 := hJ.mem φ₀ q
    refine (hs _ a Z q z (fun k => J (q ≫ φ₀ k)) h1 ha h0).trans ((mul_comm _ _).trans (congrArg _ ?_))
    exact (val_of c q z J _ (fun k => by cases k <;> rfl)).symm

end GlobalTheory.LinCombComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_comp_linCombGenerator : ∀ {X Y : Scheme.{0}} {L : LB X} {A : LB Y} {K K₁ : Type} [Fintype K] [Fintype K₁] (φ₀ : K → (Y ⟶ X)) (ε₀ : K → ℤ) (φ₁ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ), L.IsLB → A.IsLB → ∀ (u : LB.Iso A (LB.LinComb L φ₀ ε₀)), u.IsGen → ∀ (c : LB.Gen (LB.LinComb L (Sum.elim φ₁ φ₀) (Sum.elim ε₁ (fun k => -ε₀ k)))), c.IsGen → ∃ u' : LB.Iso A (LB.LinComb L φ₁ ε₁), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (a : A.ι), q z ∈ A.U a → Good L z J → gm q z _ (u'.s (fun k => J (q ≫ φ₁ k), a)) = gm q z _ (u.s (fun k => J (q ≫ φ₀ k), a)) * val c q z J := by
  first | exact @GlobalTheory.LinCombComp.exists_iso_comp_val | exact GlobalTheory.LinCombComp.exists_iso_comp_val | (intros; apply GlobalTheory.LinCombComp.exists_iso_comp_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenTransl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

abbrev genOver : Over (Sp R) := Over.mk (pullback.snd G.hom (jK R) ≫ jK R)

def genPr : genOver G ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

def genPt (a : Over.mk (jK R) ⟶ G) : genOver G ⟶ G :=
  Over.homMk (pullback.snd G.hom (jK R) ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)

def IsGenTransl [GrpObj G] (L L₁ : LB G.left) (a : Over.mk (jK R) ⟶ G) : Prop :=
  LBIso (L₁.pull (pullback.fst G.hom (jK R))) (L.pull ((genPr G * genPt G a).left))

end GlobalTheory.GenTransl
end
end
