module

public import GroundTheory.AutomorphicForms.DixmierMalliavinBasic
public import GroundTheory.GlobalFields.IdeleGroups.Restricted
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.HaarCosets
noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [IsFiniteMeasureOnCompacts μ]

theorem integral_eq_smul_finsum_coset (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    ∫ g, f g ∂μ = μ.real (K : Set G) • ∑ᶠ x : G ⧸ (K : Subgroup G), f x.out := by
  set S := (finite_image_mk_tsupport K hf).toFinset with hS
  have hmeas : ∀ g : G, MeasurableSet (g • (K : Set G)) := fun g =>
    (K.isOpen.smul g).measurableSet
  have hfin : ∀ g : G, μ (g • (K : Set G)) ≠ ∞ := fun g =>
    (hKc.smul g).measure_lt_top.ne
  have hvol : ∀ g : G, μ.real (g • (K : Set G)) = μ.real (K : Set G) := fun g => by
    simp [Measure.real, measure_smul]
  have hdec := eq_sum_indicator_coset K hf hK
  rw [finsum_eq_sum_of_support_subset (s := S)]
  · calc ∫ g, f g ∂μ
        = ∫ g, ∑ x ∈ S, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_congr_ae (Eventually.of_forall fun g => by
            rw [congrFun hdec g, Finset.sum_apply])
      _ = ∑ x ∈ S, ∫ g, (x.out • (K : Set G)).indicator (fun _ => f x.out) g ∂μ :=
          integral_finsetSum _ fun x _ =>
            (integrable_indicator_iff (hmeas _)).2 (integrableOn_const (hfin _))
      _ = μ.real (K : Set G) • ∑ x ∈ S, f x.out := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [integral_indicator_const _ (hmeas _), hvol]
  · intro x hx
    rw [hS, Set.Finite.coe_toFinset]
    exact ⟨x.out, subset_tsupport f hx, QuotientGroup.out_eq' x⟩

end Integral

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.RestrictedProductMatrix
namespace GroundTheory.Automorphic

open Filter Topology Set
open scoped RestrictedProduct

noncomputable section

section Units

variable {A B : Type*} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]

def unitsCongr (e : A ≃* B) (he : Continuous e) (he' : Continuous e.symm) : Aˣ ≃ₜ* Bˣ where
  toMulEquiv := Units.mapEquiv e
  continuous_toFun :=
    Units.continuous_iff.2 ⟨he.comp Units.continuous_val, he.comp Units.continuous_coe_inv⟩
  continuous_invFun :=
    Units.continuous_iff.2 ⟨he'.comp Units.continuous_val, he'.comp Units.continuous_coe_inv⟩

end Units

section Prod

variable (m : Type*) [Fintype m] (R₁ R₂ : Type*) [Ring R₁] [Ring R₂]

def matrixProdRingEquiv : Matrix m m (R₁ × R₂) ≃+* Matrix m m R₁ × Matrix m m R₂ where
  toFun M := (M.map Prod.fst, M.map Prod.snd)
  invFun p := Matrix.of fun a b => (p.1 a b, p.2 a b)
  left_inv M := rfl
  right_inv p := rfl
  map_mul' M N := by
    ext a b
    · change ((M * N) a b).1 = (M.map Prod.fst * N.map Prod.fst) a b
      simp [Matrix.mul_apply, Prod.fst_sum]
    · change ((M * N) a b).2 = (M.map Prod.snd * N.map Prod.snd) a b
      simp [Matrix.mul_apply, Prod.snd_sum]
  map_add' M N := rfl

variable [TopologicalSpace R₁] [TopologicalSpace R₂]

theorem continuous_matrixProdRingEquiv : Continuous (matrixProdRingEquiv m R₁ R₂) :=
  (continuous_pi fun a => continuous_pi fun b =>
      continuous_fst.comp ((continuous_apply b).comp (continuous_apply a))).prodMk
    (continuous_pi fun a => continuous_pi fun b =>
      continuous_snd.comp ((continuous_apply b).comp (continuous_apply a)))

theorem continuous_matrixProdRingEquiv_symm : Continuous (matrixProdRingEquiv m R₁ R₂).symm :=
  continuous_pi fun a => continuous_pi fun b =>
    ((continuous_apply_apply a b).comp continuous_fst).prodMk
      ((continuous_apply_apply a b).comp continuous_snd)

variable [DecidableEq m]

def glProdEquiv : GL m (R₁ × R₂) ≃ₜ* GL m R₁ × GL m R₂ :=
  (unitsCongr (matrixProdRingEquiv m R₁ R₂).toMulEquiv (continuous_matrixProdRingEquiv m R₁ R₂)
    (continuous_matrixProdRingEquiv_symm m R₁ R₂)).trans
    { toMulEquiv := MulEquiv.prodUnits
      continuous_toFun := (Homeomorph.prodUnits (α := Matrix m m R₁)
        (β := Matrix m m R₂)).continuous_toFun
      continuous_invFun := (Homeomorph.prodUnits (α := Matrix m m R₁)
        (β := Matrix m m R₂)).continuous_invFun }

end Prod

section Pi

variable (m : Type*) [Fintype m] {ι : Type*} (R : ι → Type*) [∀ j, Ring (R j)]

def matrixPiRingEquiv : Matrix m m (Π j, R j) ≃+* Π j, Matrix m m (R j) where
  toFun M j := Matrix.of fun a b => M a b j
  invFun p := Matrix.of fun a b j => p j a b
  left_inv M := rfl
  right_inv p := rfl
  map_mul' M N := by
    ext j a b
    simp [Matrix.mul_apply, Finset.sum_apply]
  map_add' M N := rfl

variable [∀ j, TopologicalSpace (R j)]

theorem continuous_matrixPiRingEquiv : Continuous (matrixPiRingEquiv m R) :=
  continuous_pi fun j => continuous_pi fun a => continuous_pi fun b =>
    (continuous_apply j).comp ((continuous_apply b).comp (continuous_apply a))

theorem continuous_matrixPiRingEquiv_symm : Continuous (matrixPiRingEquiv m R).symm :=
  continuous_pi fun a => continuous_pi fun b => continuous_pi fun j =>
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply j))

variable [DecidableEq m]

def glPiEquiv : GL m (Π j, R j) ≃ₜ* Π j, GL m (R j) :=
  (unitsCongr (matrixPiRingEquiv m R).toMulEquiv (continuous_matrixPiRingEquiv m R)
    (continuous_matrixPiRingEquiv_symm m R)).trans ContinuousMulEquiv.piUnits

end Pi

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]

def congrSets {A A' : (i : ι) → Set (R i)} (h : ∀ i, A i = A' i) :
    Πʳ i, [R i, A i] ≃ₜ Πʳ i, [R i, A' i] where
  toFun x := _root_.RestrictedProduct.mk x.1 (x.2.mono fun i hi =>
    (congrArg (x.1 i ∈ ·) (h i)).mp hi)
  invFun x := _root_.RestrictedProduct.mk x.1 (x.2.mono fun i hi =>
    (congrArg (x.1 i ∈ ·) (h i)).mpr hi)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    _root_.RestrictedProduct.mapAlong_continuous R R id tendsto_id (A₁ := A) (A₂ := A')
      (fun _ x => x) (.of_forall fun i x hx => (congrArg (x ∈ ·) (h i)).mp hx)
      fun _ => continuous_id
  continuous_invFun :=
    _root_.RestrictedProduct.mapAlong_continuous R R id tendsto_id (A₁ := A') (A₂ := A)
      (fun _ x => x) (.of_forall fun i x hx => (congrArg (x ∈ ·) (h i)).mpr hx)
      fun _ => continuous_id

def congrSetsMul [∀ i, Monoid (R i)] {S S' : ι → Type*} [∀ i, SetLike (S i) (R i)]
    [∀ i, SubmonoidClass (S i) (R i)] [∀ i, SetLike (S' i) (R i)]
    [∀ i, SubmonoidClass (S' i) (R i)] {B : Π i, S i} {B' : Π i, S' i}
    (h : ∀ i, (B i : Set (R i)) = B' i) :
    Πʳ i, [R i, B i] ≃ₜ* Πʳ i, [R i, B' i] where
  toEquiv := (congrSets h).toEquiv
  map_mul' _ _ := rfl
  continuous_toFun := (congrSets h).continuous
  continuous_invFun := (congrSets h).symm.continuous

section Pi

variable (m : Type*) [Finite m] {A : (i : ι) → Set (R i)}

def piEquiv (hA : ∀ i, IsOpen (A i)) :
    (m → Πʳ i, [R i, A i]) ≃ₜ Πʳ i, [m → R i, Set.pi univ fun _ => A i] where
  toFun x := _root_.RestrictedProduct.mk (A := fun i => Set.pi univ fun _ => A i)
    (fun i a => x a i)
    (((eventually_all (ι := m)).2 fun a => (x a).2).mono fun _ hi a _ => hi a)
  invFun y a := _root_.RestrictedProduct.mk (A := A) (fun i => y i a)
    (y.2.mono fun _ hi => hi a (mem_univ a))
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    refine (_root_.RestrictedProduct.continuous_dom_pi (A := fun _ i => R i)
      (C := fun _ i => A i) fun _ => hA).2 fun S hS => ?_
    exact (_root_.RestrictedProduct.continuous_inclusion hS).comp
      (f := fun x : (m → Πʳ i, [R i, A i]_[𝓟 S]) =>
        _root_.RestrictedProduct.mk (A := fun i => Set.pi univ fun _ => A i) (𝓕 := 𝓟 S)
          (fun i a => x a i) (eventually_principal.2 fun i hi a _ =>
            eventually_principal.1 (x a).2 i hi))
      (_root_.RestrictedProduct.continuous_rng_of_principal.2
        (continuous_pi fun i => continuous_pi fun a =>
          (_root_.RestrictedProduct.continuous_eval i).comp (continuous_apply a)))
  continuous_invFun := continuous_pi fun a =>
    _root_.RestrictedProduct.mapAlong_continuous (fun i => m → R i) R id tendsto_id
      (A₁ := fun i => Set.pi univ fun _ => A i) (A₂ := A)
      (fun _ y => y a) (.of_forall fun _ _ hy => hy a (mem_univ a)) fun _ => continuous_apply a

end Pi

section Matrix

variable (m : Type*) [Fintype m] [DecidableEq m]

def matrixHomeomorphSets {A : (i : ι) → Set (R i)} (hA : ∀ i, IsOpen (A i)) :
    Matrix m m (Πʳ i, [R i, A i]) ≃ₜ Πʳ i, [Matrix m m (R i), {M | ∀ a b, M a b ∈ A i}] :=
  ((Homeomorph.piCongrRight fun _ : m => piEquiv m hA).trans
    (piEquiv m fun i => isOpen_set_pi finite_univ fun _ _ => hA i)).trans
    (congrSets fun _ => Set.ext fun _ =>
      ⟨fun h a b => h a (mem_univ a) b (mem_univ b), fun h a _ b _ => h a b⟩)

variable [∀ i, Ring (R i)] {S : ι → Type*} [∀ i, SetLike (S i) (R i)]
  [∀ i, SubringClass (S i) (R i)] {B : Π i, S i} {C : Π i, Subring (Matrix m m (R i))}

def matrixRingEquiv (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i) :
    Matrix m m (Πʳ i, [R i, B i]) ≃+* Πʳ i, [Matrix m m (R i), C i] where
  toFun M := _root_.RestrictedProduct.mk (A := fun i => (C i : Set (Matrix m m (R i))))
    (fun i => Matrix.of fun a b => M a b i)
    (((eventually_all (ι := m)).2 fun a => (eventually_all (ι := m)).2 fun b =>
      (M a b).2).mono fun i hi => (hC i _).2 fun a b => hi a b)
  invFun x := Matrix.of fun a b =>
    _root_.RestrictedProduct.mk (A := fun i => (B i : Set (R i))) (fun i => x i a b)
      (x.2.mono fun i hi => (hC i _).1 hi a b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' M N := by
    ext i a b
    change (M * N) a b i = ((Matrix.of fun a b => M a b i) * Matrix.of fun a b => N a b i) a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact map_sum (_root_.RestrictedProduct.evalRingHom R i) _ _
  map_add' _ _ := rfl


omit [∀ i, TopologicalSpace (R i)] [∀ i, SubringClass (S i) (R i)] in
theorem coe_eq_setOf (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i) (i : ι) :
    (C i : Set (Matrix m m (R i))) = {M | ∀ a b, M a b ∈ B i} :=
  Set.ext fun M => hC i M

def matrixHomeomorph (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) :
    Matrix m m (Πʳ i, [R i, B i]) ≃ₜ Πʳ i, [Matrix m m (R i), C i] :=
  (matrixHomeomorphSets m hB).trans (congrSets fun i => (coe_eq_setOf m hC i).symm)


omit [∀ i, SubringClass (S i) (R i)] in
theorem isOpen_coe_of_forall (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) (i : ι) : IsOpen (C i : Set (Matrix m m (R i))) := by
  rw [coe_eq_setOf m hC i]
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    (hB i).preimage (continuous_apply_apply a b)

def matrixUnitsEquiv (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) :
    GL m (Πʳ i, [R i, B i]) ≃ₜ* Πʳ i, [GL m (R i), (Submonoid.ofClass (C i)).units] :=
  (unitsCongr (matrixRingEquiv m hC).toMulEquiv (matrixHomeomorph m hC hB).continuous
    (matrixHomeomorph m hC hB).symm.continuous).trans
    (GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv (isOpen_coe_of_forall m hC hB))

end Matrix

end RestrictedProduct

end

end GroundTheory.Automorphic
end

section -- merged from GroundTheory.AutomorphicForms.DixmierMalliavinProducts
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

set_option linter.unusedSectionVars false

theorem integral_fin_succ_cons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d : ℕ}
    {F : (Fin (d + 1) → ℝ) → E} (hF : Integrable F) :
    ∫ t, F t = ∫ s, ∫ t', F (Fin.cons s t') := by
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have h1 := hmp.symm.integral_comp' F
  have hint : Integrable (fun p : ℝ × (Fin d → ℝ) =>
      F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm p))
      ((volume : Measure ℝ).prod (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← h1]
  refine (integral_prod _ hint).trans ?_
  congr 1; funext s; congr 1; funext t'
  congr 1
  simp [MeasurableEquiv.piFinSuccAbove]

theorem contDiff_cons_kernel {d : ℕ} {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ} (ha : ContDiff ℝ ∞ a)
    (hK : ContDiff ℝ ∞ K) : ContDiff ℝ ∞ (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) :=
  (ha.comp (contDiff_apply ℝ (fun _ => ℝ) 0)).mul
    (hK.comp (contDiff_pi.2 fun j => contDiff_apply ℝ (fun _ => ℝ) j.succ))

theorem tsupport_cons_kernel {d : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ} {K : (Fin d → ℝ) → ℂ}
    (has : tsupport a ⊆ Icc (-ε) ε)
    (hKs : tsupport K ⊆ Metric.closedBall 0 ε) :
    tsupport (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t)) ⊆ Metric.closedBall 0 ε := by
  intro t ht
  have h1 := tsupport_mul_subset_left ht
  have h2 := tsupport_mul_subset_right ht
  have h1' : t 0 ∈ tsupport a :=
    tsupport_comp_subset_preimage a (f := fun t : Fin (d + 1) → ℝ => t 0) (continuous_apply 0) h1
  have h2' : Fin.tail t ∈ tsupport K :=
    tsupport_comp_subset_preimage K (f := fun t : Fin (d + 1) → ℝ => Fin.tail t)
      (continuous_pi fun j => continuous_apply j.succ) h2
  have ha' := has h1'
  have hK' := hKs h2'
  rw [mem_closedBall_zero_iff] at hK' ⊢
  refine (pi_norm_le_iff_of_nonneg hε).2 fun j => ?_
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [Real.norm_eq_abs, abs_le]; exact ha'
  · exact (norm_le_pi_norm (Fin.tail t) j).trans hK'

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def revProdExp {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) : G :=
  (List.ofFn fun i => h.expG (t i • X i)).reverse.prod

theorem revProdExp_zero (X : Fin 0 → 𝔤) (t : Fin 0 → ℝ) : h.revProdExp X t = 1 := by
  simp [revProdExp]

theorem revProdExp_succ {d : ℕ} (X : Fin (d + 1) → 𝔤) (t : Fin (d + 1) → ℝ) :
    h.revProdExp X t = h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) := by
  simp [revProdExp, List.ofFn_succ, Fin.tail]

theorem continuous_revProdExp {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.revProdExp X) := by
  induction d with
  | zero =>
    have hconst : h.revProdExp X = fun _ => 1 := funext (h.revProdExp_zero X)
    rw [hconst]
    exact continuous_const
  | succ d ih =>
    have hsucc : h.revProdExp X =
        fun t => h.revProdExp (Fin.tail X) (Fin.tail t) * h.expG (t 0 • X 0) :=
      funext (h.revProdExp_succ X)
    rw [hsucc]
    exact ((ih (Fin.tail X)).comp
      (continuous_pi fun j => continuous_apply j.succ)).mul
      (h.continuous_expG.comp ((continuous_apply 0).smul continuous_const))

theorem revProdExp_inv {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (h.revProdExp X t)⁻¹ = h.prodExp X (-t) := by
  rw [revProdExp, List.prod_inv_reverse, List.map_reverse, List.reverse_reverse, prodExp,
    List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
  simp [neg_smul, h.expG_neg]

theorem integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε) {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    ∫ t, a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x) =
      ∫ s, ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x))) := by
  have hint : Integrable
      (fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t) * F (h.revProdExp X t * x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((ha.comp (continuous_apply 0)).mul
        (hK.comp (continuous_pi fun j => continuous_apply j.succ))).mul
        (hF.comp ((h.continuous_revProdExp X).mul continuous_const))
    · exact HasCompactSupport.mul_right (f := fun t : Fin (d + 1) → ℝ => a (t 0) * K (Fin.tail t))
        ((isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _)
          (tsupport_cons_kernel hε has hKs))
  rw [integral_fin_succ_cons hint]
  congr 1; funext s; congr 1; funext t'
  simp only [Fin.cons_zero, Fin.tail_cons, h.revProdExp_succ, mul_assoc]

theorem integrable_integral_cons_kernel {d : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} {a : ℝ → ℂ}
    (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε) {K : (Fin d → ℝ) → ℂ}
    (hK : Continuous K) (hKs : tsupport K ⊆ Metric.closedBall 0 ε) {F : G → ℂ}
    (hF : Continuous F) (x : G) :
    Integrable (fun s : ℝ =>
      ∫ t', a s * (K t' * F (h.revProdExp (Fin.tail X) t' * (h.expG (s • X 0) * x)))) := by
  have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) :=
    (ha.comp continuous_fst).mul ((hK.comp continuous_snd).mul (hF.comp
      (((h.continuous_revProdExp (Fin.tail X)).comp continuous_snd).mul
        ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_const))))
  have hs : HasCompactSupport (fun p : ℝ × (Fin d → ℝ) =>
      a p.1 * (K p.2 * F (h.revProdExp (Fin.tail X) p.2 * (h.expG (p.1 • X 0) * x)))) := by
    refine HasCompactSupport.intro
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_closedBall (0 : Fin d → ℝ) ε)) ?_
    intro p hp
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (has h')), zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hp (hKs h')), zero_mul, mul_zero]
  exact (hc.integrable_of_hasCompactSupport hs).integral_prod_left

theorem sum_integral_cons_kernel {d m : ℕ} (X : Fin (d + 1) → 𝔤) {ε : ℝ} (hε : 0 ≤ ε)
    {a : ℝ → ℂ} (ha : Continuous a) (has : tsupport a ⊆ Icc (-ε) ε)
    {K : Fin m → (Fin d → ℝ) → ℂ} (hK : ∀ i, Continuous (K i))
    (hKs : ∀ i, tsupport (K i) ⊆ Metric.closedBall 0 ε) {F : Fin m → G → ℂ}
    (hF : ∀ i, Continuous (F i)) {f₁ : G → ℂ}
    (hd : ∀ y, f₁ y = ∑ i, ∫ t', K i t' * F i (h.revProdExp (Fin.tail X) t' * y)) (x : G) :
    ∑ i, ∫ t, a (t 0) * K i (Fin.tail t) * F i (h.revProdExp X t * x) =
      ∫ s, a s * f₁ (h.expG (s • X 0) * x) := by
  rw [Finset.sum_congr rfl fun i _ => h.integral_cons_kernel X hε ha has (hK i) (hKs i) (hF i) x,
    ← integral_finsetSum _ fun i _ =>
      h.integrable_integral_cons_kernel X ha has (hK i) (hKs i) (hF i) x]
  congr 1; funext s
  rw [hd, Finset.mul_sum]
  congr 1; funext i
  rw [← integral_const_mul]

end IsExpLieAlgebra

end GroundTheory.Automorphic
end
