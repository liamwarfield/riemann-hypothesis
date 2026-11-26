module

public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferOfFacts
public import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag
public import Lemmata.RankOneOrbitForms.RankOneForm
public import Formalism.LocalToGlobal.GlobalTheory.DivPassage

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferHolds
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
open Module NumberField Matrix

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace BlockMetrics

section Forms

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem fc_smul (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]

def fcA : V →+ (ι → ℂ) :=
  AddMonoidHom.mk' (Formalism.HermitianLatticesTheory.fcoord b X v) (Formalism.HermitianLatticesTheory.fcoord_add b X v)

theorem fc_sum {α : Type} (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ a ∈ s, f a) = ∑ a ∈ s, Formalism.HermitianLatticesTheory.fcoord b X v (f a) := by
  exact map_sum (fcA b X v) f s

theorem maj_sum_left {α : Type} (s : Finset α) (c : α → K) (f : α → V) (y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (∑ a ∈ s, c a • f a) y =
      ∑ a ∈ s, star (v.embedding (c a)) * Formalism.HermitianLatticesTheory.majAt b X v (f a) y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_sum_right {α : Type} (s : Finset α) (c : α → K) (f : α → V) (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (∑ a ∈ s, c a • f a) =
      ∑ a ∈ s, v.embedding (c a) * Formalism.HermitianLatticesTheory.majAt b X v x (f a) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_smul_left (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) y = starRingEnd ℂ (v.embedding a) * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply]
  ring

theorem maj_smul_right (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_self (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' _

theorem normAt_eq_sqrt (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [maj_self, Complex.ofReal_re, Real.sqrt_sq]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  exact Real.sqrt_nonneg _

theorem normAt_eq_norm (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x =
      ‖(WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

theorem fcoord_map (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (φ x) =
      ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (φ x) =
      ((LinearMap.toMatrix b b φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b φ x, RingHom.map_mulVec]
    rfl
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]

end Forms

theorem dense_emb {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  rcases Complex.subfield_eq_of_closed (v.embedding.fieldRange.isClosed_topologicalClosure) with h | h
  · exfalso
    have hr : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure :=
        v.embedding.fieldRange.le_topologicalClosure (RingHom.mem_fieldRange.2 ⟨x, rfl⟩)
      rw [h] at hx
      obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.1 hx
      rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
      simp
    exact (InfinitePlace.isComplex_iff.1 hv) hr
  · intro z
    have hz : z ∈ v.embedding.fieldRange.topologicalClosure := by
      rw [h]; exact Subfield.mem_top z
    have hc : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (Set.range v.embedding) := by
      rw [← RingHom.coe_fieldRange]; rfl
    rw [← hc]; exact hz

theorem dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have hemb : DenseRange v.embedding := dense_emb v (IsTotallyComplex.isComplex v)
  have h1 : DenseRange fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x := by
    have hpi : DenseRange (Pi.map fun _ : ι => v.embedding) := DenseRange.piMap fun _ => hemb
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (Pi.map fun _ : ι => v.embedding) := by
      ext u; constructor
      · rintro ⟨x, rfl⟩; exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨c, rfl⟩
        refine ⟨b.equivFun.symm c, ?_⟩
        funext i
        have hc := congr_fun (b.equivFun.apply_symm_apply c) i
        rw [Basis.equivFun_apply] at hc
        show v.embedding (b.repr (b.equivFun.symm c) i) = v.embedding (c i)
        rw [hc]
    rw [DenseRange, hr]; exact hpi
  have h2 : Continuous fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have h3 : Function.Surjective fun u : ι → ℂ =>
      (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    intro w
    refine ⟨(X v).mulVec (WithLp.ofLp w), ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]
  exact h3.denseRange.comp h1 h2

theorem opNormAt_le_of_points {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] V) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b X v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b X v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v)) with hTd
  refine ContinuousLinearMap.opNorm_le_bound T hC fun u => ?_
  refine (dense_fcoord b X hX v).induction_on (p := fun w => ‖T w‖ ≤ C * ‖w‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hT : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)) =
        WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (φ f)) := by
      rw [fcoord_map b X v hX φ f]; rfl
    show ‖T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f))‖ ≤ C * ‖WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)‖
    rw [hT, ← normAt_eq_norm, ← normAt_eq_norm]
    exact h f

end BlockMetrics

open BlockMetrics

private theorem normAt_smul_indefinite_real {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (a • x) = ‖v.embedding a‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [normAt_eq_norm, normAt_eq_norm, fc_smul, WithLp.toLp_smul, norm_smul]

private theorem normAt_add_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + y) ≤ Formalism.HermitianLatticesTheory.normAt b X v x + Formalism.HermitianLatticesTheory.normAt b X v y := by
  rw [normAt_eq_norm, normAt_eq_norm, normAt_eq_norm, Formalism.HermitianLatticesTheory.fcoord_add, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem normAt_finset_sum_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {α : Type} (s : Finset α)
    (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (normAt_smul_indefinite_real b X v (0 : K) (0 : V)).le
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (normAt_add_le b X v _ _).trans (add_le_add le_rfl ih)

theorem metric : Metric := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hX hU
  have hinv : ∀ (g : G) (y : V), ρ g (ρ g⁻¹ y) = y := by
    intro g y
    show (ρ g * ρ g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρ : ∀ (v : InfinitePlace K) (g : G) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := by
    intro v g x y
    calc Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y
        = Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g (ρ g⁻¹ y)) := by rw [hinv]
      _ = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := hU v g x _
  refine ⟨fun T _ _ _ τ v x y => ?_, fun H χ g v => ?_⟩
  · have hc := fun g => (charFacts K G T τ g).2 v.embedding
    have hc1 : starRingEnd ℂ (v.embedding (charOf τ 1 / (Fintype.card G : K))) =
        v.embedding (charOf τ 1 / (Fintype.card G : K)) := by
      have h1 := (hc 1).1
      rw [inv_one] at h1
      simp only [map_div₀, map_natCast]
      rw [starRingEnd_apply, ← h1]
    simp only [Formalism.IndefR.TransferLatticeStatement.eS, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [maj_smul_left, maj_smul_right, maj_sum_left, maj_sum_right, hc1]
    congr 1
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    have hg := (hc g⁻¹).1
    rw [inv_inv] at hg
    simp only [Equiv.inv_apply, inv_inv]
    rw [hρ, ← hg]
  · have hρn : ∀ (k : G) (z : V), Formalism.HermitianLatticesTheory.normAt b X v (ρ k z) = Formalism.HermitianLatticesTheory.normAt b X v z := by
      intro k z; rw [normAt_eq_sqrt, hU, ← normAt_eq_sqrt]
    have hχ : ∀ h : H, ‖v.embedding (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
      intro h
      rw [InfinitePlace.norm_embedding_eq]
      have ht : χ h⁻¹ ∈ NumberField.Units.torsion K := χ.isOfFinOrder (isOfFinOrder_of_finite h⁻¹)
      exact (NumberField.Units.mem_torsion K).1 ht v
    refine opNormAt_le_of_points b X hX _ v 1 zero_le_one fun f => ?_
    rw [one_mul, LinearMap.comp_apply]
    simp only [Formalism.IndefR.TransferLatticeStatement.epP, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [normAt_smul_indefinite_real]
    refine (mul_le_mul_of_nonneg_left (normAt_finset_sum_le b X v _ _) (norm_nonneg _)).trans ?_
    simp only [normAt_smul_indefinite_real, hχ, hρn, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
    rw [Fintype.card_eq_nat_card, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'), one_mul]

end Formalism.IndefR.LatticeTransfer
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinrankIntSelf
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace IdempotentLemmas

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

lemma charOf_conj {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (g h : G) : charOf τ (h * g * h⁻¹) = charOf τ g := by
  unfold charOf
  by_cases hf : Module.Finite K T
  · rw [map_mul τ, map_mul τ, LinearMap.trace_mul_comm K (τ h * τ g), ← mul_assoc, ← map_mul τ,
      inv_mul_cancel, map_one, one_mul]
  · have h0 : LinearMap.trace K T = 0 := by
      first
      | exact LinearMap.trace_eq_zero_of_not_finite hf
      | exact LinearMap.trace_eq_zero_of_not_finite (R := K) (M := T) hf
      | (rw [LinearMap.trace, dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
      | (unfold LinearMap.trace; rw [dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
    simp [h0]

lemma eS_mul_rho {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (y : G) :
    eS τ ρ * ρ y = (charOf τ 1 / (Fintype.card G : K)) • ∑ g : G, charOf τ (y * g⁻¹) • ρ g := by
  unfold eS
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp_rw [smul_mul_assoc, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => by simp [mul_inv_rev])

lemma eS_mul_asAlg {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (a : MonoidAlgebra K G) :
    eS τ ρ * ρ.asAlgebraHom a = (charOf τ 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K T (τ.asAlgebraHom a * τ g⁻¹) • ρ g := by
  induction a using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of, eS_mul_rho]
    simp only [charOf, ← map_mul]
  | add f g hf hg =>
    rw [map_add (f := _), mul_add, hf, hg, ← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_add (f := _), add_mul, map_add (f := _), add_smul]
  | smul r f hf =>
    rw [map_smul, mul_smul_comm, hf, smul_comm r, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, smul_mul_assoc, map_smul, smul_eq_mul, mul_smul]

lemma eS_comm {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (g : G) :
    eS τ ρ * ρ g = ρ g * eS τ ρ := by
  rw [eS_mul_rho]
  unfold eS
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [show g * (g * x)⁻¹ = g * x⁻¹ * g⁻¹ by group, charOf_conj]

lemma trace_eS {T U : Type} [AddCommGroup T] [Module K T] [AddCommGroup U] [Module K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    LinearMap.trace K U (eS τ σ) =
      charOf τ 1 / (Fintype.card G : K) * ∑ x : G, charOf τ x⁻¹ * charOf σ x := by
  unfold eS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

lemma sum_char_eq [CharZero K] {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    ∑ x : G, charOf τ x⁻¹ * charOf σ x =
      (Fintype.card G : K) * finrank K (Representation.IntertwiningMap τ σ) := by
  have hc : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card G : K) := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  rw [← Nat.card_eq_fintype_card, ← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_comm]
  rfl

lemma finrank_int_self {T : Type} [AddCommGroup T] [Module K T] [Nontrivial T]
    (τ : Representation K G T)
    (h : ∀ f : T →ₗ[K] T, (∀ g : G, f ∘ₗ τ g = τ g ∘ₗ f) → ∃ c : K, f = c • LinearMap.id) :
    finrank K (Representation.IntertwiningMap τ τ) = 1 := by
  have hne : Representation.IntertwiningMap.id τ ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : T)
    intro h0
    apply hv
    have := congrArg (fun f : Representation.IntertwiningMap τ τ => f v) h0
    simpa using this
  rw [finrank_eq_one_iff_of_nonzero' _ hne]
  intro w
  obtain ⟨c, hc⟩ := h w.toLinearMap (fun g => w.isIntertwining' g)
  refine ⟨c, ?_⟩
  apply DFunLike.ext
  intro v
  have hv : w v = c • v := by
    rw [← Representation.IntertwiningMap.toLinearMap_apply, hc]
    simp
  rw [hv]
  simp

lemma int_eq_zero {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U)
    (hτ : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hσ : ∀ W : Submodule K U, (∀ g : G, ∀ w ∈ W, σ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hch : charOf τ ≠ charOf σ) (f : Representation.IntertwiningMap τ σ) : f = 0 := by
  by_contra hf
  have hf' : f.toLinearMap ≠ 0 := fun h =>
    hf (Representation.IntertwiningMap.ext (by simpa using h))
  have hker : LinearMap.ker f.toLinearMap = ⊥ := by
    rcases hτ (LinearMap.ker f.toLinearMap) (fun g w hw => by
      simp only [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply] at hw ⊢
      rw [f.isIntertwining, hw, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hf'
  have hrange : LinearMap.range f.toLinearMap = ⊤ := by
    rcases hσ (LinearMap.range f.toLinearMap) (fun g w hw => by
      obtain ⟨v, rfl⟩ := hw
      exact ⟨τ g v, LinearMap.congr_fun (f.isIntertwining' g) v⟩) with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) hf'
    · exact h
  let e : T ≃ₗ[K] U := LinearEquiv.ofBijective f.toLinearMap
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  have he : ∀ x, e x = f x := fun x => rfl
  apply hch
  funext g
  have hconj : e.conj (τ g) = σ g := by
    apply LinearMap.ext
    intro u
    rw [LinearEquiv.conj_apply_apply, he, f.isIntertwining, ← he, LinearEquiv.apply_symm_apply]
  show LinearMap.trace K T (τ g) = LinearMap.trace K U (σ g)
  rw [← hconj, LinearMap.trace_conj']

def eAlg {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) :
    MonoidAlgebra K G :=
  ∑ x : G, MonoidAlgebra.single x (charOf τ 1 / (Fintype.card G : K) * charOf τ x⁻¹)

lemma asAlg_eAlg {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) :
    ρ.asAlgebraHom (eAlg τ) = eS τ ρ := by
  unfold eAlg eS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, mul_smul]

lemma comm_epP [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) (X : Module.End K V) (hX : ∀ g, X * ρ g = ρ g * X)
    (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : X * epP H χ ρ = epP H χ ρ * X := by
  unfold epP
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, hX]

lemma idem_gen {V : Type} [AddCommGroup V] [Module K V] {H : Type} [Group H] {_ : Fintype H}
    (a : H → K) (ha : ∀ h k, a h * a k = a (h * k)) (π : H →* Module.End K V)
    (hn : (Nat.card H : K) ≠ 0) :
    ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) * ((Nat.card H : K)⁻¹ • ∑ h : H, a h • π h) =
      (Nat.card H : K)⁻¹ • ∑ h : H, a h • π h := by
  have key : (∑ h : H, a h • π h) * (∑ h : H, a h • π h) = (Nat.card H : K) • ∑ h : H, a h • π h := by
    rw [Finset.sum_mul]
    have e0 : ∀ h : H, (a h • π h) * ∑ k : H, a k • π k = ∑ m : H, a m • π m := by
      intro h
      rw [Finset.mul_sum]
      have e : ∀ k : H, (a h • π h) * (a k • π k) = a (h * k) • π (h * k) := by
        intro k
        rw [smul_mul_smul_comm, ha, map_mul]
      simp_rw [e]
      exact Equiv.sum_comp (Equiv.mulLeft h) (fun m => a m • π m)
    simp_rw [e0]
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card]
  rw [smul_mul_smul_comm, key, smul_smul]
  congr 1
  field_simp

end IdempotentLemmas

open IdempotentLemmas

theorem keyZero : KeyZero := by
  intro K _ G _ _ T _ _ τ V _ _ ρ a ha
  rw [← Module.End.mul_eq_comp]
  simpa [ha] using eS_mul_asAlg τ ρ a

theorem schur : Schur := by
  intro K _ _ G _ _ S T _ _ _ τ hgood
  obtain ⟨hnt, hirr, habs, hinj⟩ := hgood
  have hcomm : ∀ s t, ∃ c : K, eS (τ s) (τ t) = c • LinearMap.id := fun s t =>
    habs t _ (fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact eS_comm (τ s) (τ t) g)
  have hdim : ∀ s, charOf (τ s) 1 = (finrank K (T s) : K) := fun s => by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hpos : ∀ s, (finrank K (T s) : K) ≠ 0 := fun s => by
    haveI := hnt s
    exact_mod_cast (Module.finrank_pos (R := K) (M := T s)).ne'
  have hcard : (Fintype.card G : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htr : ∀ s t, LinearMap.trace K (T t) (eS (τ s) (τ t)) =
      (finrank K (T s) : K) * finrank K (Representation.IntertwiningMap (τ s) (τ t)) := by
    intro s t
    rw [trace_eS, sum_char_eq, hdim]
    field_simp
  have hone : ∀ s, finrank K (Representation.IntertwiningMap (τ s) (τ s)) = 1 := fun s => by
    haveI := hnt s
    exact finrank_int_self (τ s) (habs s)
  have hsum : ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K) := by
    intro s
    rw [sum_char_eq, hone s, Nat.cast_one, mul_one]
  refine ⟨fun s => ?_, fun s t hst => ?_, hsum⟩
  · obtain ⟨c, hc⟩ := hcomm s s
    have h1 := htr s s
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, hone s, Nat.cast_one, mul_one] at h1
    have h2 : (c - 1) * (finrank K (T s) : K) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    have h3 : c = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (hpos s))
    rw [hc, h3, one_smul]
  · obtain ⟨c, hc⟩ := hcomm s t
    have hne : charOf (τ s) ≠ charOf (τ t) := fun h => hst (hinj s t h)
    haveI : Subsingleton (Representation.IntertwiningMap (τ s) (τ t)) :=
      ⟨fun f g => (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne f).trans
        (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne g).symm⟩
    have h1 := htr s t
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul,
      Module.finrank_zero_of_subsingleton (R := K) (M := Representation.IntertwiningMap (τ s) (τ t)),
      Nat.cast_zero, mul_zero] at h1
    have h3 : c = 0 := (mul_eq_zero.1 h1).resolve_right (hpos t)
    rw [hc, h3, zero_smul]

theorem idemE : IdemE := by
  intro K _ _ G _ _ S T _ _ _ τ hgood V _ _ ρ
  obtain ⟨h1, h2, -⟩ := schur K G S T τ hgood
  have key : ∀ s t, eS (τ s) ρ ∘ₗ eS (τ t) ρ = (charOf (τ s) 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K (T s) (eS (τ t) (τ s) * τ s g⁻¹) • ρ g := by
    intro s t
    rw [← Module.End.mul_eq_comp, ← asAlg_eAlg (τ t) ρ, eS_mul_asAlg, asAlg_eAlg]
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · rw [key, h1 s]
    unfold eS
    congr 1
  · rw [key, h2 t s (Ne.symm hst)]
    simp

theorem idemP_of (h : CharFacts) : IdemP := by
  intro K _ _ G _ _ V _ _ _ _ ρ
  have hs' : ∀ (r : 𝓞 K) (v : V), ((r : K)) • v = r • v := fun r v => algebraMap_smul K r v
  have hcard : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨fun T _ _ _ τ => ⟨fun g => eS_comm τ ρ g,
    fun H χ => comm_epP ρ (eS τ ρ) (fun g => eS_comm τ ρ g) H χ, fun A hA a ha => ?_⟩,
    fun H χ => ⟨?_, fun A hA a ha => ?_⟩⟩
  · have hint : ∀ x : G, IsIntegral ℤ (charOf τ 1 * charOf τ x⁻¹) :=
      fun x => (h K G T τ 1).1.mul (h K G T τ x⁻¹).1
    have hd : (Fintype.card G : K) * (charOf τ 1 / (Fintype.card G : K)) = charOf τ 1 := by
      field_simp
    rw [← hs', show ((Fintype.card G : 𝓞 K) : K) = (Fintype.card G : K) by simp, eS,
      LinearMap.smul_apply, smul_smul, hd, LinearMap.sum_apply, Finset.smul_sum]
    refine A.sum_mem fun x _ => ?_
    rw [LinearMap.smul_apply, smul_smul]
    have hx : charOf τ 1 * charOf τ x⁻¹ ∈ integralClosure ℤ K := hint x
    let r : 𝓞 K := ⟨_, hx⟩
    have hm := A.smul_mem r (hA x a ha)
    have he : (charOf τ 1 * charOf τ x⁻¹) • ρ x a = r • ρ x a := hs' r (ρ x a)
    rw [he]
    exact hm
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    show epP H χ ρ * epP H χ ρ = epP H χ ρ
    unfold epP
    exact idem_gen (fun h : H => (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))
      (fun h k => by simp only [mul_inv_rev, map_mul, Units.val_mul]; ring)
      (ρ.comp H.subtype) hn
  · have hn : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hI : ((Fintype.card G : 𝓞 K) : K) * (Nat.card H : K)⁻¹ = ((H.index : 𝓞 K) : K) := by
      have hG : (Fintype.card G : K) = (Nat.card H : K) * H.index := by
        rw [← Nat.card_eq_fintype_card, ← H.card_mul_index, Nat.cast_mul]
      simp only [map_natCast]
      rw [hG]
      field_simp
    rw [← hs']
    unfold epP
    rw [LinearMap.smul_apply, smul_smul, hI, hs', LinearMap.sum_apply]
    refine A.smul_mem _ (A.sum_mem fun h _ => ?_)
    rw [LinearMap.smul_apply, hs']
    exact A.smul_mem _ (hA _ _ ha)

end Formalism.IndefR.LatticeTransfer
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing
open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace NormTraceLemmas

section Lin

variable {K : Type} [Field K] {G : Type} [Group G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

theorem exists_strictHenselian_absolutely_closed_local_ring (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  first | exact Bl.RankOneOrbitForms.goal1 .. | (apply Bl.RankOneOrbitForms.goal1 <;> assumption) | (intros; apply Bl.RankOneOrbitForms.goal1 <;> assumption)

end Lin

section Char

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]


open Classical in
theorem trace_formula (τ : Representation K G T) (H₀ H : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (χ : H →* (𝓞 K)ˣ) (a b : G) :
    LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) =
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹) *
        ∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← Module.End.mul_eq_comp, epP, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, map_sum, smul_eq_mul, ← map_mul, charOf, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h₀ _ => Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (algebraMap (𝓞 K) K)]
  ring

theorem norm_chi (H : Subgroup G) [Finite H] (χ : H →* (𝓞 K)ˣ) (h : H) (σ : K →+* ℂ) :
    ‖σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
  have hu : ((χ h : (𝓞 K)ˣ) : 𝓞 K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) ^ Nat.card H = 1 := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hu
    rw [map_pow, map_one] at this
    exact this
  exact Complex.norm_eq_one_of_pow_eq_one h2 Nat.card_pos.ne'

variable [NumberField K]

theorem norm_trace_le (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b))‖ ≤ (finrank K T : ℝ) := by
  classical
  rw [trace_formula, map_mul, norm_mul]
  have hA : ‖σ ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹)‖ =
      (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by
    simp [map_mul, map_inv₀, map_natCast, norm_inv]
  rw [hA]
  have hB : ‖σ (∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b))‖ ≤
      ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine norm_sum_le_of_le _ fun h₀ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine norm_sum_le_of_le _ fun h _ => ?_
    rw [map_mul, map_mul, norm_mul, norm_mul, norm_chi, norm_chi, one_mul, one_mul]
    exact ((hC K G T τ _).2 σ).2
  have hpos : (0 : ℝ) ≤ (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by positivity
  calc (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ‖_‖ ≤
        (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) :=
        mul_le_mul_of_nonneg_left hB hpos
    _ = (finrank K T : ℝ) := by
        have h0 : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        have h1 : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        field_simp

theorem integral_mem (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) :
    (Fintype.card G : K) ^ 2 * LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) ∈
      integralClosure ℤ K := by
  classical
  rw [trace_formula]
  have hG0 : (Fintype.card G : K) = (Nat.card H₀ : K) * (H₀.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hG1 : (Fintype.card G : K) = (Nat.card H : K) * (H.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hsq : (Fintype.card G : K) ^ 2 =
      ((Nat.card H₀ : K) * (H₀.index : K)) * ((Nat.card H : K) * (H.index : K)) := by
    rw [sq]
    nth_rw 1 [hG0]
    rw [hG1]
  have h0 : (Nat.card H₀ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsq, show ∀ x : K, (Nat.card H₀ : K) * (H₀.index : K) * ((Nat.card H : K) * (H.index : K)) *
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹ * x) = (H₀.index : K) * (H.index : K) * x from
      fun x => by field_simp]
  refine mul_mem (mul_mem (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
    (Subalgebra.sum_mem _ fun h₀ _ => Subalgebra.sum_mem _ fun h _ => mul_mem (mul_mem ?_ ?_) ?_)
  · exact RingOfIntegers.isIntegral_coe _
  · exact RingOfIntegers.isIntegral_coe _
  · exact (hC K G T τ _).1

end Char

section Alg

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]


open Classical in
def epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : MonoidAlgebra K G :=
  ((Nat.card H : ℕ) : K)⁻¹ •
    ∑ h : H, MonoidAlgebra.single (h : G) ((((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))

theorem asAlg_epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : ρ.asAlgebraHom (epA H χ) = epP H χ ρ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [epA, epP, map_smul, map_sum, Representation.asAlgebraHom_single]

def eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) : MonoidAlgebra K G :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, MonoidAlgebra.single x (charOf τ x⁻¹)

theorem asAlg_eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) :
    ρ.asAlgebraHom (eA τ) = eS τ ρ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eA, eS, map_smul, map_sum, Representation.asAlgebraHom_single]

end Alg

end NormTraceLemmas


open NormTraceLemmas in
theorem core_of (hC : CharFacts) (hK : KeyZero) (hS : Schur) (hP : IdemP) : Core := by
  intro K _ _ G _ _ S T _ _ _ τ H₀ χ₀ H χ hgood hM1 s
  obtain ⟨γ, δ, c, hdet, htr, he1, he2⟩ :=
    exists_strictHenselian_absolutely_closed_local_ring (τ s) (hgood.2.1 s) (epP H₀ χ₀ (τ s)) (epP H χ (τ s)) (hM1 s)
  refine ⟨γ, δ, c, fun i j => ⟨(Fintype.card G : K) ^ 2 * c i j, ?_⟩, hdet, fun i j => rfl, ?_, ?_⟩
  · rw [htr i j]
    exact integral_mem hC (τ s) H₀ H χ₀ χ (δ i) (γ j)
  · intro i j σ
    rw [htr i j]
    exact norm_trace_le hC (τ s) H₀ H χ₀ χ (δ i) (γ j) σ
  · intro V _ _ ρ
    let _ : Module (𝓞 K) V := Module.compHom V (algebraMap (𝓞 K) K)
    have : IsScalarTower (𝓞 K) K V := ⟨fun x y v => by
      change (x • y) • v = (algebraMap (𝓞 K) K x) • (y • v)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨hPe, hPε⟩ := hP K G V ρ
    obtain ⟨hcg, hcε, -⟩ := hPe (T s) (τ s)
    have ce_g : ∀ g x, eS (τ s) ρ (ρ g x) = ρ g (eS (τ s) ρ x) :=
      fun g x => LinearMap.congr_fun (hcg g) x
    have ce₀ : ∀ x, eS (τ s) ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H₀ χ₀) x
    have ce : ∀ x, eS (τ s) ρ (epP H χ ρ x) = epP H χ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H χ) x
    have ii₀ : ∀ x, epP H₀ χ₀ ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ x :=
      fun x => LinearMap.congr_fun (hPε H₀ χ₀).1 x
    have ii : ∀ x, epP H χ ρ (epP H χ ρ x) = epP H χ ρ x :=
      fun x => LinearMap.congr_fun (hPε H χ).1 x
    have hee : ∀ x, eS (τ s) ρ (eS (τ s) ρ x) = eS (τ s) ρ x := by
      intro x
      have h0 : (τ s).asAlgebraHom (eA (τ s) - 1) = 0 := by
        rw [map_sub, asAlg_eA, (hS K G S T τ hgood).1 s, map_one, Module.End.one_eq_id, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ h0) x
      simp only [LinearMap.comp_apply, map_sub, asAlg_eA, map_one, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.zero_apply, sub_eq_zero] at this
      exact this
    constructor
    · intro i j a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce₀, hee, ha]
      have e0a : epP H₀ χ₀ ρ a = a := by
        calc epP H₀ χ₀ ρ a = epP H₀ χ₀ ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii₀, ha]
      have hx : (τ s).asAlgebraHom (epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ *
          MonoidAlgebra.of K G (γ j) * epA H₀ χ₀ - c i j • epA H₀ χ₀) = 0 := by
        simp only [map_sub, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he1 i j, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hx) a
      simp only [LinearMap.comp_apply, map_sub, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, e0a, sub_eq_zero] at this
      exact this
    · intro a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce, hee, ha]
      have Ea : epP H χ ρ a = a := by
        calc epP H χ ρ a = epP H χ ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii, ha]
      have hy : (τ s).asAlgebraHom (∑ j, ∑ i, c⁻¹ j i • (epA H χ * MonoidAlgebra.of K G (γ j) *
          epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ) - epA H χ) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sub, map_sum, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he2, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hy) a
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.comp_apply, map_sub, map_sum, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, LinearMap.sum_apply,
        Module.End.mul_apply, LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, Ea,
        sub_eq_zero] at this
      exact this

end Formalism.IndefR.LatticeTransfer
end
end

namespace Formalism.IndefR.LatticeTransfer

theorem dimSq : DimSq := dimSq_of schur

theorem idemP : IdemP := idemP_of charFacts

theorem core : Core := core_of charFacts keyZero schur idemP

theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
end

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.L2.GlobalTheoryTheory.DivPassage

theorem levelAmb_transfer
    {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {D0 D1 : ℕ}
    (A : LevelAmb K D0 D1) {G : Type} [Group G] [Fintype G] {T : A.S → Type}
    [∀ s, AddCommGroup (T s)] [∀ s, Module K (T s)] [∀ s, FiniteDimensional K (T s)]
    (τ : ∀ s, Representation K G (T s)) (H₀ : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ) (H : Subgroup G)
    (χ : H →* (𝓞 K)ˣ) (ρ : Representation K G (Fin A.Dg → K))
    (hτ : IsGood τ) (hM : M1 τ H₀ χ₀)
    (h0 : A.ep0.mulVecLin = epP H₀ χ₀ ρ) (h1 : A.ep1.mulVecLin = epP H χ ρ)
    (hs : ∀ s, (A.es s).mulVecLin = eS (τ s) ρ) (hn : ∀ s, A.nS s = nS (τ s) H χ)
    (hG : A.G = Fintype.card G) (hgood : eGood τ ρ = LinearMap.id)
    (hX : A.FramesG) (hL : Submodule.IsFullLattice K A.Rg) (hst : ∀ g : G, ∀ a ∈ A.Rg, ρ g a ∈ A.Rg)
    (hU : IsUnitaryRep (Pi.basisFun K (Fin A.Dg)) A.Xg ρ) :
    A.Ranks ∧ A.Deg0 ∧ A.Deg1 ∧ (A.latticeAtSharpLevel ≠ ⊥ → A.MaxT) := by
  have h15 := all_parts_transfer_holds
  have hlat : IsGLat ρ A.Rg := by
    have : Submodule.IsFullLattice K A.Rg := hL
    exact ⟨Submodule.IsLattice.fg K A.Rg, Submodule.IsFullLattice.span_eq_top, hst⟩
  have p := h15 K G A.S T τ H₀ χ₀ H χ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have q := h15 K G A.S T τ H₀ χ₀ H₀ χ₀ hτ hM _ _ (Pi.basisFun K (Fin A.Dg)) A.Xg ρ hX hU A.Rg hlat
  have e0 : A.latticeAtBaseLevel = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h0]; rfl
  have e1 : A.latticeAtSharpLevel = cut A.Rg (epP H χ ρ ∘ₗ eGood τ ρ) := by
    rw [hgood, LinearMap.comp_id, ← h1]; rfl
  have es : ∀ s, A.Rs s = cut A.Rg (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s => by
    rw [← h0, ← hs, ← Matrix.mulVecLin_mul]; rfl
  unfold TransferLatticeConditions at p q
  dsimp only at p q
  simp only [← e0, ← e1, ← es, ← hn, ← hG] at p
  have hM' : ∀ s, nS (τ s) H₀ χ₀ = 1 := hM
  simp only [← e0, ← es, hM', one_mul] at q
  obtain ⟨⟨-, r1⟩, ⟨-, -, -, -, -, -, d0⟩, -, ⟨d1, -⟩, m⟩ := p
  have r0 := q.1.2
  have h85 : (8.5 : ℝ) = 17 / 2 := by norm_num
  rw [h85] at d1 m
  refine ⟨⟨r0, r1⟩, ?_, ?_, fun h => (m h).1⟩
  · unfold LevelAmb.Deg0
    rw [r0, Nat.cast_sum]
    exact sub_le_iff_le_add'.1 d0
  · unfold LevelAmb.Deg1
    rw [r1]
    have := (abs_le.1 d1).1
    exact sub_le_iff_le_add.2 (by
      have h2 := neg_le_sub_iff_le_add.1 this
      exact h2)

end Formalism.IndefR.LatticeTransfer
