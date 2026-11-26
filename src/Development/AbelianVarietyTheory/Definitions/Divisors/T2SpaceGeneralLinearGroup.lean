module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZetaValueIdeals
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise

noncomputable section
namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem mem_KO_iff (g : GL n k) :
    g ∈ KO k n ↔ (∀ i j, g.val i j ∈ 𝒪[k]) ∧ ∀ i j, (g⁻¹).val i j ∈ 𝒪[k] := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨fun i j => (u.val i j).2, fun i j => ?_⟩
    rw [← map_inv]; exact ((u⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix (m := n)) :=
      fun A B h => by ext i j; exact congrFun (congrFun h i) j
    let A : Matrix n n 𝒪[k] := fun i j => ⟨g.val i j, h1 i j⟩
    let B : Matrix n n 𝒪[k] := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    have hB : (algebraMap 𝒪[k] k).mapMatrix B = (g⁻¹).val := rfl
    refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, Units.mul_inv]
    · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem isEmbedding_val_GL : IsEmbedding (fun g : GL n k => g.val) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  refine Units.isEmbedding_val_mk' (f := fun A : Matrix n n k => A⁻¹) (fun A hA => ?_) fun u => by simp
  refine (continuousAt_matrix_inv A ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero

instance t2Space_general_linear_group : T2Space (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  infer_instance

instance secondCountable_GL : SecondCountableTopology (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have : SecondCountableTopology (Matrix n n k) := inferInstanceAs (SecondCountableTopology (n → n → k))
  exact isEmbedding_val_GL.secondCountableTopology

instance locallyCompact_GL : LocallyCompactSpace (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have : LocallyCompactSpace (Matrix n n k) := inferInstanceAs (LocallyCompactSpace (n → n → k))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

omit [DecidableEq n] in
theorem isOpen_intMatrix {m : Type*} [Fintype m] : IsOpen {A : Matrix m n k | ∀ i j, A i j ∈ 𝒪[k]} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_int.preimage (f := fun A : Matrix m n k => A i j) (by fun_prop)

omit [DecidableEq n] [Fintype n] in
theorem isCompact_intMatrix {m : Type*} : IsCompact {A : Matrix m n k | ∀ i j, A i j ∈ 𝒪[k]} := by
  have h : IsCompact (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : n => (𝒪[k] : Set k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int
  have e : {A : Matrix m n k | ∀ i j, A i j ∈ 𝒪[k]} =
      (Set.pi Set.univ fun _ : m => Set.pi Set.univ fun _ : n => (𝒪[k] : Set k)) :=
    Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
  rw [e]; exact h

theorem isOpen_KO : IsOpen (KO k n : Set (GL n k)) := by
  have h1 := (isOpen_intMatrix (k := k) (m := n) (n := n)).preimage (Units.continuous_val (M := Matrix n n k))
  have h2 := (isOpen_intMatrix (k := k) (m := n) (n := n)).preimage (Units.continuous_coe_inv (M := Matrix n n k))
  convert h1.inter h2 using 1
  exact Set.ext mem_KO_iff

theorem isCompact_KO : IsCompact (KO k n : Set (GL n k)) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have hK := isCompact_intMatrix (k := k) (m := n) (n := n)
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [SetLike.mem_coe, mem_KO_iff, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def diagGL (c : n → kˣ) : GL n k :=
  ⟨diagonal fun i => (c i : k), diagonal fun i => ((c i)⁻¹ : kˣ), by simp [diagonal_mul_diagonal],
    by simp [diagonal_mul_diagonal]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
@[simp] theorem diagGL_val (c : n → kˣ) : (diagGL c).val = diagonal fun i => (c i : k) := rfl

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_diagGL (c : n → kˣ) : Matrix.GeneralLinearGroup.det (diagGL c) = ∏ i, c i := by
  ext; simp [Matrix.GeneralLinearGroup.val_det_apply]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
def diagHom : (n → kˣ) →* GL n k where
  toFun := diagGL
  map_one' := Units.ext (by simp)
  map_mul' c c' := Units.ext (by simp [diagonal_mul_diagonal])


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_eq_one_of_center (Δ : GL n k →* ℝ≥0) (hc : ∀ g, (∀ h, g * h = h * g) → Δ g = 1) (g : GL n k) :
    Δ g = 1 := by
  have pos : ∀ g, Δ g ≠ 0 := fun g => ((Group.isUnit g).map Δ).ne_zero
  have conj : ∀ x y p : GL n k, p * x = y * p → Δ x = Δ y := fun x y p h => by
    have := congrArg Δ h
    rw [map_mul, map_mul, mul_comm] at this
    exact mul_right_cancel₀ (pos p) this
  have hdiag : ∀ c : n → kˣ, Δ (diagGL c) = 1 := fun c => by
    have h1 : ∀ σ : Equiv.Perm n, Δ (diagGL c) = Δ (diagGL (c ∘ σ)) := fun σ =>
      conj _ _ (Matrix.GeneralLinearGroup.mkOfDetNeZero (σ.permMatrix k) (by
        rw [Matrix.det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h])) (Units.ext (by
        ext i j
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, diagGL_val, mul_diagonal,
          diagonal_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
          Option.some.injEq, Function.comp]
        split_ifs with h <;> simp [h]))
    have h2 : Δ (diagHom (∏ σ : Equiv.Perm n, c ∘ σ)) = 1 := hc _ fun h => Units.ext (by
      rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
      · exact Subsingleton.elim _ _
      have : (∏ σ : Equiv.Perm n, c ∘ σ) = fun _ => ∏ σ : Equiv.Perm n, c (σ i₀) := by
        funext i
        rw [Finset.prod_apply]
        exact (Fintype.prod_equiv (Equiv.mulRight (Equiv.swap i₀ i)) _ _ fun σ => by simp)
      rw [this]
      simp only [diagHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, diagGL_val, ← smul_one_eq_diagonal]
      simp)
    rw [← MonoidHom.comp_apply, map_prod] at h2
    have h3 : ∏ σ : Equiv.Perm n, Δ (diagGL c) = 1 := by
      rw [← h2]; exact Finset.prod_congr rfl fun σ _ => h1 σ
    rw [Finset.prod_const] at h3
    exact (pow_eq_one_iff_of_nonneg zero_le (Finset.card_ne_zero.2 Finset.univ_nonempty)).1 h3
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → Δ g = 1) g.val g.det_ne_zero ?_ ?_ ?_ g rfl
  · intro D hD g hg
    rw [det_diagonal, Finset.prod_ne_zero_iff] at hD
    rw [show g = diagGL fun i => Units.mk0 (D i) (hD i (Finset.mem_univ _)) from Units.ext hg]
    exact hdiag _
  · rintro ⟨i, j, hij, c⟩ g hg
    have hinv : (g⁻¹).val = transvection i j (-c) := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hg, TransvectionStruct.toMatrix_mk, transvection_mul_transvection_same _ _ hij]
      simp
    have h1 : Δ g = Δ g⁻¹ := conj _ _ (diagGL fun l => if l = i then -1 else 1) (Units.ext (by
      ext a b
      rw [Units.val_mul, Units.val_mul, hinv, hg, TransvectionStruct.toMatrix_mk]
      simp only [diagGL_val, mul_diagonal, diagonal_mul, transvection, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]
      clear conj hdiag hc pos hinv hg
      simp only [apply_ite (Units.val : kˣ → k), Units.val_neg, Units.val_one]
      split_ifs <;> first | (exfalso; grind) | ring))
    have h2 : Δ g ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 2 [h1]; rw [← map_mul, mul_inv_cancel, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  · intro A B hA hB pA pB g hg
    rw [show g = Matrix.GeneralLinearGroup.mkOfDetNeZero A hA * Matrix.GeneralLinearGroup.mkOfDetNeZero B hB from
      Units.ext hg, map_mul, pA _ rfl, pB _ rfl, one_mul]

variable [MeasurableSpace k] [BorelSpace k]

instance borel_GL : BorelSpace (GL n k) := by
  obtain ⟨_, _⟩ := secondCountable_and_t2_local_field (k := k)
  have hB : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  exact (measurableEmbedding_val n).borelSpace isEmbedding_val_GL.isInducing

instance isMulRightInvariant_of_haar (μ : Measure (GL n k)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : Measure.modularCharacter g = 1 := by
    refine hom_eq_one_of_center Measure.modularCharacter (fun z hz => ?_) g
    have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
    rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
    have h2 := congrArg (fun m : Measure (GL n k) => m (KO k n)) h1
    have hne : μ (KO k n) ≠ 0 := (isOpen_KO.measure_pos μ ⟨1, one_mem _⟩).ne'
    have hnt : μ (KO k n) ≠ ⊤ := isCompact_KO.measure_lt_top.ne
    simp only [Measure.coe_nnreal_smul_apply] at h2
    have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
    exact_mod_cast h3
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h, one_smul]

def haarVol (J : Subgroup (GL n k)) : Measure (GL n k) :=
  ((Measure.haar : Measure (GL n k)) J)⁻¹ • Measure.haar

theorem haar_ne_zero_ne_top (μ : Measure (GL n k)) [μ.IsHaarMeasure] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) : μ J ≠ 0 ∧ μ J ≠ ⊤ :=
  ⟨(ho.measure_pos μ ⟨1, one_mem _⟩).ne', ((measure_mono hK).trans_lt isCompact_KO.measure_lt_top).ne⟩

theorem isHaarMeasure_haarVol {J : Subgroup (GL n k)} (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    (haarVol J).IsHaarMeasure :=
  have h := haar_ne_zero_ne_top Measure.haar ho hK
  Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h.2) (ENNReal.inv_ne_top.2 h.1)

theorem haarVol_self {J : Subgroup (GL n k)} (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    haarVol J J = 1 := by
  have h := haar_ne_zero_ne_top Measure.haar ho hK
  simp [haarVol, ENNReal.inv_mul_cancel h.1 h.2]

theorem eq_haarVol (μ : Measure (GL n k)) [μ.IsHaarMeasure] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) (h1 : μ J = 1) : μ = haarVol J := by
  have := isHaarMeasure_haarVol ho hK
  have h := Measure.isMulLeftInvariant_eq_smul μ (haarVol J)
  have h2 := congrArg (fun m : Measure (GL n k) => m J) h
  simp only [Measure.coe_nnreal_smul_apply, haarVol_self ho hK, h1, mul_one] at h2
  rw [h, show Measure.haarScalarFactor μ (haarVol J) = 1 by exact_mod_cast h2.symm, one_smul]

instance isHaarMeasure_haarVol_KO : (haarVol (KO k n)).IsHaarMeasure := isHaarMeasure_haarVol isOpen_KO le_rfl

end GlobalTheory.SplitFlip
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

open CategoryTheory GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}


set_option autoImplicit false in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_nil {O : Type} [CommRing O] [Algebra ℂ O] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ O (Fin g → O)).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]


variable (K) in
@[reducible] def jet (k : K.K) : K.Obj where
  k := k
  C := TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))
  alg := ((TrivSqZeroExt.inlHom _ _).comp (K.cst k)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (K.W k)) (Fin g → Hol (K.W k))).toRingHom
  nil := tsze_nil
  ρ := TrivSqZeroExt.inlHom _ _
  ρ_cst _ := rfl

def tszeSec {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) : O →+* TrivSqZeroExt O (Fin g → O) where
  toFun h := TrivSqZeroExt.inl h + TrivSqZeroExt.inr fun a ↦ D a h
  map_one' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_zero' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)


set_option autoImplicit false in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.fst_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).fst = h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]


set_option autoImplicit false in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.snd_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) (a : Fin g) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).snd a = D a h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

def jetSec (k : K.K) : Hol (K.W k) →+* TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) := tszeSec dw


set_option autoImplicit false in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in
theorem _root_.GlobalTheory.AnPer.Charts.tsze_expand {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + TrivSqZeroExt.inr v : TrivSqZeroExt O (Fin g → O)) = TrivSqZeroExt.inl h +
      ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) := by
  congr 1
  simp only [TrivSqZeroExt.inl_mul_inr]
  ext b
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

def jet0 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  ptHom (K.jet k) (K.le_refl k)

def jet1 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  fromTriv (K.jet k) (K.le_refl k) (jetSec k)
    (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, sh_refl]
        exact tsze_expand h fun a ↦ dw a h⟩)

end GlobalTheory.AnPer.Charts
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
namespace GlobalTheory.OTY

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def jz (A : WeightedAtlas n Y ι La) (z : Y → V n) (i : ι) (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (z ∘ (A.chart i).symm) (A.chart i y)

def jdet (A : WeightedAtlas n Y ι La) (z : Y → V n) : ι → Y → ℂ :=
  fun i y => (jz A z i y).det

structure Etale (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) : Prop where
  isOpen : IsOpen U
  holo : ∀ i, DifferentiableOn ℂ (z ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)
  det_ne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → jdet A z i y ≠ 0

def nz (A : WeightedAtlas n Y ι La) (τ : ι → Y → ℂ) : Set Y := {y | τ (A.pick y) y ≠ 0}

structure Cover (A : WeightedAtlas n Y ι La) where

  m : ℕ

  idx : Fin m → ι

  c : Fin m → V n

  r : Fin m → ℝ

  chi : Fin m → Y → ℝ
  r_pos : ∀ a, 0 < r a
  sub : ∀ a, Metric.closedBall (c a) (r a) ⊆ (A.chart (idx a)).target
  smooth : ∀ a, A.SmoothFn (chi a)
  supp : ∀ a, tsupport (chi a) ⊆
    (A.chart (idx a)).source ∩ A.chart (idx a) ⁻¹' Metric.ball (c a) (r a)
  nonneg : ∀ a y, 0 ≤ chi a y
  sum_one : ∀ y, ∑ a, chi a y = 1

def n0 (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y) ∂A.mu

def n1 {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∑ a, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
    ((∑ j, ‖wdb n j (F (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
      Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))

def CurvGe {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (t : ℝ) : Prop :=
  ∀ a, ∀ v ∈ Metric.ball (C.c a) (C.r a), ∀ ξ : Fin n → ℂ,
    t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt (C.idx a) (A.ph la (C.idx a)) ((A.chart (C.idx a)).symm v) ξ

def glue {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) :
    ι → Y → ℂ :=
  fun i y => ∑ a, (C.chi a y : ℂ) * A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y)

def wT (T x : ℝ) : ℝ := 1 / (1 + min (x ^ 2) ((T + 1) ^ 2))

def IsCut (T : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ x, x ≤ -T - 1 → θ x = 1) ∧ (∀ x, -T + 1 ≤ x → θ x = 0) ∧
    (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x, |deriv θ x| ≤ 3 / 4

end

end GlobalTheory.OTY
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

variable {p O Λ}

abbrev rhoTA {ε : PreTilt O p} {h : ℕ} (D : Datum ε h Λ) (l : Λ) :
    Matrix (Fin h) (Fin h) (Ainf p O) := (D.ρT l).map (ofPadic p O)

end GlobalTheory.DetInv
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
noncomputable section

open scoped TensorProduct Quaternion

namespace GlobalTheory.QSA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def nrm {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : R :=
  x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2

def coords {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : Fin 4 → R :=
  ![x.re, x.imI, x.imJ, x.imK]

scoped instance top {R : Type*} [CommRing R] [TopologicalSpace R] {a b : R} : TopologicalSpace ℍ[R, a, b] :=
  TopologicalSpace.induced coords inferInstance

variable (F : Type) [Field F] [NumberField F]

abbrev DA (a b : F) : Type := ℍ[AF F, algebraMap F (AF F) a, algebraMap F (AF F) b]

variable {F}

def rat {a b : F} (x : ℍ[F, a, b]) : DA F a b :=
  ⟨algebraMap F (AF F) x.re, algebraMap F (AF F) x.imI, algebraMap F (AF F) x.imJ, algebraMap F (AF F) x.imK⟩

def H0 {a b : F} (ε : AF F) : Set (DA F a b) :=
  {x | ∃ γ : ℍ[F, a, b], nrm γ = 1 ∧ ∃ h : DA F a b, nrm h = 1 ∧ ε • (h - 1) = h - 1 ∧ x = rat γ * h}

theorem nrm_mul {R : Type*} [CommRing R] {a b : R} (x y : ℍ[R, a, b]) : nrm (x * y) = nrm x * nrm y := by
  simp only [nrm, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem mul_star_eq {R : Type*} [CommRing R] {a b : R} (x : ℍ[R, a, b]) : x * star x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem nrm_rat {a b : F} (x : ℍ[F, a, b]) : nrm (rat x) = algebraMap F (AF F) (nrm x) := by
  simp [nrm, rat]

theorem one_mem_H0_weight_zero {a b : F} (ε : AF F) : (1 : DA F a b) ∈ H0 ε :=
  ⟨1, by simp [nrm], 1, by simp [nrm], by simp, by ext <;> simp [rat]⟩

end GlobalTheory.QSA
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Abstract

variable {k : Type} [Field k] {M M' M₁ M₂ M₃ : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

structure Cx (k M : Type) [Field k] [AddCommGroup M] [Module k M] where

  C : ℤ → Submodule k M

  D : M →ₗ[k] M

namespace Cx

def IsCx (K : Cx k M) : Prop := ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

abbrev H (K : Cx k M) (n : ℤ) : Type := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

end Cx

def Adj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop :=
  ∀ n, ∃ ε : ℤˣ, ∀ a ∈ K.C n, ∀ b ∈ L.C (N - n - 1), β (K.D a) b = ε • β a (L.D b)

def IsMap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') : Prop := ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

def pt (k : Type) [Field k] : Cx k k := ⟨fun n => if n = 0 then ⊤ else ⊥, 0⟩

end Abstract

section Cech

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]


variable (k ι E) in
def deltaL : (Finset ι → E) →ₗ[k] (Finset ι → E) where
  toFun := GlobalTheory.DI.delta
  map_add' a b := by
    funext t
    simp [GlobalTheory.DI.delta, Finset.sum_add_distrib]
  map_smul' r a := by
    funext t
    simp only [GlobalTheory.DI.delta, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def cechC (F : Finset ι → Submodule k E) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥

def cech (F : Finset ι → Submodule k E) : Cx k (Finset ι → E) := ⟨cechC F, deltaL k ι E⟩

def totD (d : E →ₗ[k] E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  deltaL k ι E + LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • (d ∘ₗ LinearMap.proj s)

def totC (T : ℕ → Finset ι → Submodule k E) (a b : ℕ) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s =>
    if s.Nonempty ∧ (a : ℤ) ≤ n + 1 - s.card ∧ n + 1 - s.card < b then T (n + 1 - s.card).toNat s else ⊥

def cupPair [Fintype ι] {E' : Type} [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) :
    (Finset ι → E) →ₗ[k] (Finset ι → E') →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j))) (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end Cech

section Alg

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [Ring E] [Algebra k E]

end Alg

end GlobalTheory.PD
end
end
