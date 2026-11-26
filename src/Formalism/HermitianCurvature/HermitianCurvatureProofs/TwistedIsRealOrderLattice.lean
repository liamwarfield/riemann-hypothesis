module

public import Formalism.HermitianCurvature.PrimeToDifferent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cauchy
public import Formalism.HermitianCurvature.StatementLE

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
namespace Formalism.FourierDecayAlt.P.S6x5

open Module MeasureTheory

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem covolume_index (μ : Measure V) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ V)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂]
    (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ := by
  classical
  have : Module.Free ℤ L₁ := ZLattice.module_free ℝ L₁
  have : Module.Free ℤ L₂ := ZLattice.module_free ℝ L₂
  have : Module.Finite ℤ L₁ := ZLattice.module_finite ℝ L₁
  have : Module.Finite ℤ L₂ := ZLattice.module_finite ℝ L₂
  let b₂ := Free.chooseBasis ℤ L₂
  let b₁ := (Free.chooseBasis ℤ L₁).reindex (Fintype.equivOfCardEq
    (β := Free.ChooseBasisIndex ℤ L₂)
    (by rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      ZLattice.rank ℝ, ZLattice.rank ℝ]))
  rw [ZLattice.covolume_eq_det_mul_measureReal L₁ μ b₁ (b₂.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_det_mul_measureReal L₂ μ b₂ (b₂.ofZLatticeBasis ℝ), ← mul_assoc]
  congr 1
  have h2 : (b₂.ofZLatticeBasis ℝ).det ((↑) ∘ b₂) = 1 := by
    have : ((↑) ∘ b₂ : _ → V) = b₂.ofZLatticeBasis ℝ := by ext; simp
    rw [this, Basis.det_self]
  have hrel : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup =
      (b₂.det (fun i => (⟨b₁ i, h (SetLike.coe_mem _)⟩ : L₂))).natAbs :=
    AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂
  rw [h2, abs_one, mul_one, hrel, Nat.cast_natAbs, Int.cast_abs]
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (SetLike.coe_mem _)⟩ i)

noncomputable abbrev scal (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) : V →ₗ[ℤ] V :=
  (c • (LinearMap.id : V →ₗ[ℝ] V)).restrictScalars ℤ

noncomputable def scalInv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ) (hc : c ≠ 0) :
    V ≃L[ℝ] V :=
  ContinuousLinearEquiv.equivOfInverse (c⁻¹ • ContinuousLinearMap.id ℝ V)
    (c • ContinuousLinearMap.id ℝ V) (fun x => by simp [smul_smul, hc])
    (fun x => by simp [smul_smul, hc])

theorem scalInv_apply (c : ℝ) (hc : c ≠ 0) (x : V) : scalInv V c hc x = c⁻¹ • x := rfl

theorem map_scal_eq_comap (c : ℝ) (hc : c ≠ 0) (L : Submodule ℤ V) :
    L.map (scal V c) = ZLattice.comap ℝ L (scalInv V c hc).toLinearMap := by
  ext x
  simp only [Submodule.mem_map, ZLattice.comap, Submodule.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : (scalInv V c hc) (c • y) = y := by rw [scalInv_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
    show (scalInv V c hc) (c • y) ∈ L
    rw [this]; exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    show c • (scalInv V c hc) x = x
    rw [scalInv_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem covolume_scal (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) (hc : c ≠ 0) :
    ZLattice.covolume (ZLattice.comap ℝ L (scalInv V c hc).toLinearMap) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume L μ := by
  classical
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b := Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ
      (b.ofZLatticeComap ℝ L (scalInv V c hc).toLinearEquiv) (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_det_mul_measureReal L μ b (b.ofZLatticeBasis ℝ), ← mul_assoc]
  congr 1
  have h1 : ((↑) ∘ (b.ofZLatticeComap ℝ L (scalInv V c hc).toLinearEquiv) : _ → V)
      = fun i => c • ((↑) ∘ b : _ → V) i := by
    ext i
    rw [Function.comp_apply, Basis.ofZLatticeComap_apply]
    rfl
  have h2 := (b.ofZLatticeBasis ℝ).det.toMultilinearMap.map_smul_univ (fun _ => c)
    ((↑) ∘ b : _ → V)
  rw [h1]
  erw [h2]
  simp only [Finset.prod_const, Finset.card_univ, smul_eq_mul, abs_mul, abs_pow]
  rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]
  rfl

theorem lattice_of_index (μ : Measure V) [μ.IsAddHaarMeasure] (M₁ M₂ : Submodule ℤ V)
    [DiscreteTopology M₁] [IsZLattice ℝ M₁] (h : M₁ ≤ M₂)
    (hn : M₁.toAddSubgroup.relIndex M₂.toAddSubgroup ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    DiscreteTopology (M₂.map (scal V c)) ∧
    Submodule.span ℝ (M₂.map (scal V c) : Set V) = ⊤ ∧
    ZLattice.covolume (M₂.map (scal V c)) μ =
      |c| ^ finrank ℝ V * ZLattice.covolume M₁ μ /
        (M₁.toAddSubgroup.relIndex M₂.toAddSubgroup : ℝ) := by
  set n := M₁.toAddSubgroup.relIndex M₂.toAddSubgroup with hn'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn

  have hsub : M₂ ≤ ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap := by
    intro x hx
    show (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)) x ∈ M₁
    rw [scalInv_apply, inv_inv, Nat.cast_smul_eq_nsmul]
    have := AddSubgroup.nsmul_index_mem (M₁.toAddSubgroup.addSubgroupOf M₂.toAddSubgroup) ⟨x, hx⟩
    exact this
  have hd : DiscreteTopology M₂ := DiscreteTopology.of_subset (t := (M₂ : Set V))
    (s := (ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap : Set V))
    (inferInstanceAs (DiscreteTopology
      (ZLattice.comap ℝ M₁ (scalInv V (n : ℝ)⁻¹ (inv_ne_zero hnR)).toLinearMap))) hsub
  have hz : IsZLattice ℝ M₂ := ⟨by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := M₁)]
    exact Submodule.span_mono h⟩
  rw [map_scal_eq_comap c hc]
  refine ⟨inferInstance, IsZLattice.span_top, ?_⟩
  rw [covolume_scal μ M₂ c hc, covolume_index μ M₁ M₂ h, ← hn']
  field_simp

end General
end Formalism.FourierDecayAlt.P.S6x5

namespace Formalism.FourierDecayAlt.P.S6x5

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

noncomputable abbrev emb (E : Type) [Field E] [NumberField E] : E →ₗ[ℤ] mixedEmbedding.mixedSpace E :=
  (mixedEmbedding E).toAddMonoidHom.toIntLinearMap

theorem map_zsub_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (B : FI E) (hB : B ≠ 0) :
    (zsub E B).map (emb E) = mixedEmbedding.idealLattice E (Units.mk0 B hB) := by
  ext x
  rw [mixedEmbedding.mem_idealLattice, Submodule.mem_map]
  rfl

theorem finrank_eq (E : Type) [Field E] [NumberField E] [IsCMField E] :
    finrank ℚ E = 2 * deg E := by
  have h2 : finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  unfold deg; omega

theorem mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem conj_real (E : Type) [Field E] [NumberField E] [IsCMField E]
    (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)

theorem smul_mem_FI (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this

theorem exists_nat_mul_mem (E : Type) [Field E] [NumberField E] (B : FI E) (hB : B ≠ 0) (t : E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ B := by
  obtain ⟨b, hb, hb0⟩ : ∃ b ∈ B, b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hB ((FractionalIdeal.eq_zero_iff).2 hcon)
  have halg : IsAlgebraic ℤ (t / b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (t / b))
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  have h1 : (y : E) * t ∈ B := by
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y • (t / b) :=
      ⟨⟨y • (t / b), hy⟩, rfl⟩
    have := (B : Submodule (𝓞 E) E).smul_mem z hb
    rw [Algebra.smul_def, hz, zsmul_eq_mul] at this
    have h2 : (y : E) * (t / b) * b = (y : E) * t := by field_simp
    rw [h2] at this
    exact this
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact h1
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact (B : Submodule (𝓞 E) E).neg_mem h1

end Formalism.FourierDecayAlt.P.S6x5

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x5
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors


open scoped Classical in
theorem covolumeIndex : Formalism.FourierDecayAlt.S6.CovolumeIndex := by
  intro E _ _ _ B L c hB hc hBL hn
  have hinj : Function.Injective (emb E).toAddMonoidHom := (mixedEmbedding E).injective
  have hidx : ((zsub E B).map (emb E)).toAddSubgroup.relIndex (L.map (emb E)).toAddSubgroup
      = idx E (zsub E B) L := by
    unfold idx
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hle : (zsub E B).map (emb E) ≤ L.map (emb E) := Submodule.map_mono hBL
  rw [map_zsub_eq E B hB] at hidx hle
  have key := lattice_of_index (volume : Measure (mixedEmbedding.mixedSpace E))
    (mixedEmbedding.idealLattice E (Units.mk0 B hB)) (L.map (emb E)) hle (by rw [hidx]; exact hn)
    c hc
  refine ⟨key.1, key.2.1, ?_⟩
  have h1 : InfinitePlace.nrComplexPlaces E = deg E := by
    have h5 := IsTotallyComplex.finrank E
    have := finrank_eq E
    omega
  have h3 := key.2.2
  rw [hidx, mixedEmbedding.covolume_idealLattice, mixedEmbedding.finrank, finrank_eq E, h1] at h3
  unfold frameLat
  rw [h3]
  simp [mul_assoc]

theorem twistedIsRealOrderLattice : Formalism.FourierDecayAlt.S6.TwIsFLattice := by
  intro E _ _ _ A B s hB hBA hconj
  refine ⟨fun a t ht => ?_, fun t => ?_⟩
  · rw [mem_twLat] at ht ⊢
    refine ⟨smul_mem_FI E A a t ht.1, ?_⟩
    have := smul_mem_FI E B a _ ht.2
    rw [map_mul, conj_real]
    convert this using 1
    ring
  · obtain ⟨n, hn, hmem⟩ := exists_nat_mul_mem E B hB t
    refine ⟨n, hn, ?_⟩
    rw [mem_twLat]
    refine ⟨hBA hmem, ?_⟩
    have h1 : complexConj E ((n : E) * t) ∈ B := hconj _ hmem
    have h2 : (-1 : E) ^ s * complexConj E ((n : E) * t) ∈ B := by
      rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
      · simpa using h1
      · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
    exact B.coeToSubmodule.sub_mem hmem h2

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RootPushforwardDensity
open MeasureTheory Set Polynomial

noncomputable section

namespace Formalism.FourierDecayAlt.P.NthRootMeasurability

open Formalism.FourierDecayAlt.crystallineComparison

theorem detC (d : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ).det = ‖d‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq,
    Complex.normSq_eq_norm_sq]

def zeta (s : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / s)

def R (s k : ℕ) (w : ℂ) : ℂ := zeta s ^ k * w ^ ((s : ℂ)⁻¹)

def A (s k : ℕ) : Set ℂ := {z | z ≠ 0 ∧ R s k (z ^ s) = z}

theorem measurable_R (s k : ℕ) : Measurable (R s k) := by
  unfold R; fun_prop

theorem measurableSet_A (s k : ℕ) : MeasurableSet (A s k) := by
  have h1 : MeasurableSet {z : ℂ | z ≠ 0} := (measurableSet_singleton (0 : ℂ)).compl
  have h2 : MeasurableSet {z : ℂ | R s k (z ^ s) = z} :=
    measurableSet_eq_fun ((measurable_R s k).comp (by fun_prop)) measurable_id
  exact h1.inter h2

theorem R_pow (s k : ℕ) (hs : s ≠ 0) (w : ℂ) : R s k w ^ s = w := by
  unfold R zeta
  rw [mul_pow, ← pow_mul, mul_comm k s, pow_mul, (Complex.isPrimitiveRoot_exp s hs).pow_eq_one,
    one_pow, one_mul, Complex.cpow_nat_inv_pow w hs]

theorem nthRoots_eq_R (s : ℕ) (hs : s ≠ 0) (w : ℂ) :
    nthRoots s w = (Multiset.range s).map (fun k => R s k w) :=
  (Complex.isPrimitiveRoot_exp s hs).nthRoots_eq (Complex.cpow_nat_inv_pow w hs)

theorem A_disjoint (s : ℕ) (hs : s ≠ 0) :
    Set.PairwiseDisjoint (↑(Finset.range s) : Set ℕ) (A s) := by
  intro j hj k hk hjk
  rw [Function.onFun, Set.disjoint_left]
  intro z hzj hzk
  apply hjk
  simp only [Finset.coe_range, Set.mem_Iio] at hj hk
  have e : zeta s ^ j * (z ^ s) ^ ((s : ℂ)⁻¹) = zeta s ^ k * (z ^ s) ^ ((s : ℂ)⁻¹) := by
    have := hzj.2.trans hzk.2.symm
    simpa [R] using this
  have hα : (z ^ s) ^ ((s : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have := hzj.2
    simp only [R, h0, mul_zero] at this
    exact hzj.1 this.symm
  exact (Complex.isPrimitiveRoot_exp s hs).pow_inj hj hk (mul_right_cancel₀ hα e)

theorem A_union (s : ℕ) (hs : s ≠ 0) : (⋃ k ∈ Finset.range s, A s k) = {0}ᶜ := by
  ext z
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff, A,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, _, hz, _⟩; exact hz
  · intro hz
    have hmem : z ∈ nthRoots s (z ^ s) := (mem_nthRoots (Nat.pos_of_ne_zero hs)).mpr rfl
    rw [nthRoots_eq_R s hs, Multiset.mem_map] at hmem
    obtain ⟨k, hk, hkz⟩ := hmem
    exact ⟨k, Multiset.mem_range.mp hk, hz, hkz⟩

theorem image_A (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) :
    (fun z => u⁻¹ * z ^ s) '' A s k = {0}ᶜ := by
  ext c
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, ⟨hz, _⟩, rfl⟩
    exact mul_ne_zero (inv_ne_zero hu) (pow_ne_zero _ hz)
  · intro hc
    refine ⟨R s k (u * c), ⟨?_, ?_⟩, ?_⟩
    · intro h0
      have := R_pow s k hs (u * c)
      rw [h0, zero_pow hs] at this
      exact mul_ne_zero hu hc this.symm
    · rw [R_pow s k hs]
    · rw [R_pow s k hs, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]

theorem injOn_A (s k : ℕ) (u : ℂ) (hu : u ≠ 0) : InjOn (fun z => u⁻¹ * z ^ s) (A s k) := by
  intro z hz z' hz' e
  have e' : z ^ s = z' ^ s := mul_left_cancel₀ (inv_ne_zero hu) e
  rw [← hz.2, ← hz'.2, e']

end Formalism.FourierDecayAlt.P.NthRootMeasurability
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeanBoundsLimits
open Filter Topology Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.MeanBoundsLimits

open Classical

open Formalism.FourierDecayAlt.crystallineComparison

section Mean

variable {Λ : Type} [AddCommGroup Λ] {LIM : (Λ → ℂ) → ℂ}

theorem bdd_const (c : ℂ) : Bdd (fun _ : Λ => c) := ⟨‖c‖, fun _ => le_rfl⟩

theorem lim_const (hM : IsMean LIM) (c : ℂ) : LIM (fun _ : Λ => c) = c := by
  have e : (fun _ : Λ => c) = c • (fun _ : Λ => (1 : ℂ)) := by funext; simp
  rw [e, hM.2.1 c _ (bdd_const 1), hM.2.2.2.1, mul_one]

theorem lim_real (hM : IsMean LIM) (q : Λ → ℂ) (B : ℝ) (hq : ∀ x, ‖q x‖ ≤ B)
    (hr : ∀ x, (q x).im = 0) : (LIM q).im = 0 ∧ (LIM q).re ≤ B := by
  have hqb : Bdd q := ⟨B, hq⟩
  have hre : ∀ x, |(q x).re| ≤ B := fun x => (Complex.abs_re_le_norm _).trans (hq x)
  have h1 := hM.2.2.1 (q + fun _ => (B : ℂ)) (Bdd_add hqb) (fun x => by
    simp only [Pi.add_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
      hr x, add_zero]
    exact ⟨by linarith [(abs_le.mp (hre x)).1], trivial⟩)
  rw [hM.1 _ _ hqb (bdd_const _), lim_const hM] at h1
  have hneg : Bdd ((-1 : ℂ) • q) := ⟨B, fun x => by simpa using hq x⟩
  have h2 := hM.2.2.1 ((fun _ => (B : ℂ)) + (-1 : ℂ) • q) (bdd_const_add hneg) (fun x => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.ofReal_re,
      Complex.add_im, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, hr x]
    norm_num
    linarith [(abs_le.mp (hre x)).2])
  rw [hM.1 _ _ (bdd_const _) hneg, lim_const hM, hM.2.1 _ _ hqb] at h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.add_re, Complex.ofReal_re] at h1 h2
  constructor
  · linarith [h1.2]
  · simp at h2; linarith [h2.1]
where
  Bdd_add {g : Λ → ℂ} (hg : Bdd g) : Bdd (g + fun _ => (B : ℂ)) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' hg (bdd_const _)
  bdd_const_add {g : Λ → ℂ} (hg : Bdd g) : Bdd ((fun _ => (B : ℂ)) + g) :=
    Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_const _) hg

theorem meanBound_ok : MeanBound := by
  intro Λ _ LIM g B hM hg
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  set z := LIM g with hz
  by_cases z0 : z = 0
  · rw [z0, norm_zero]; exact hB
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr z0
  set u : ℂ := starRingEnd ℂ z / ‖z‖ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self]
    exact norm_ne_zero_iff.mpr z0
  have hgb : Bdd g := ⟨B, hg⟩
  set h := u • g with hh
  have hhb : ∀ x, ‖h x‖ ≤ B := fun x => by
    simp only [hh, Pi.smul_apply, smul_eq_mul, norm_mul, hu1, one_mul]; exact hg x
  have hLh : LIM h = ‖z‖ := by
    rw [hh, hM.2.1 u g hgb, ← hz, hu, div_mul_eq_mul_div, Complex.conj_mul', pow_two,
      mul_div_assoc, div_self hn, mul_one]
  set hr : Λ → ℂ := fun x => ((h x).re : ℂ)
  set hi : Λ → ℂ := fun x => ((h x).im : ℂ)
  have hrb : ∀ x, ‖hr x‖ ≤ B := fun x => by
    simp only [hr, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hhb x)
  have hib : ∀ x, ‖hi x‖ ≤ B := fun x => by
    simp only [hi, Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_im_le_norm _).trans (hhb x)
  have hsplit : h = hr + Complex.I • hi := by
    funext x; simp only [hr, hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im (h x)).symm
  have hL := congrArg LIM hsplit
  rw [hM.1 _ _ ⟨B, hrb⟩ (Formalism.FourierDecayAlt.P.E2.bdd_smul' _ ⟨B, hib⟩), hM.2.1 _ _ ⟨B, hib⟩, hLh] at hL
  have R := lim_real hM hr B hrb (fun x => by simp [hr])
  have I := lim_real hM hi B hib (fun x => by simp [hi])
  have := congrArg Complex.re hL
  simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, I.1, zero_sub, neg_zero, add_zero] at this
  linarith [R.2]

end Mean

theorem bdd_inner {f : ℕ} {Λ : AddSubgroup (V f)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (p q : V f → H) (B : ℝ) (hp : ∀ x, ‖p x‖ ≤ B) (hq : ∀ x, ‖q x‖ ≤ B)
    (σ : V f) : Bdd (fun x : Λ => inner ℂ (p x) (q ((x : V f) + σ))) :=
  ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
    (mul_le_mul (hp _) (hq _) (norm_nonneg _) ((norm_nonneg _).trans (hp x)))⟩

theorem lim_of_tendsto {f : ℕ} {Λ : AddSubgroup (V f)} {LIM : (Λ → ℂ) → ℂ}
    (hM : IsMeanInf Λ LIM) (F : V f → ℂ) (L : ℂ) (hF : Bdd (fun x : Λ => F x))
    (ht : Tendsto F (atInfAll f) (𝓝 L)) : LIM (fun x : Λ => F x) = L := by
  have hD : Bdd (fun x : Λ => F x - L) := by
    obtain ⟨b, hb⟩ := hF
    exact ⟨b + ‖L‖, fun x => (norm_sub_le _ _).trans (by linarith [hb x])⟩
  have h0 : LIM (fun x : Λ => F x - L) = 0 := by
    apply hM.2 _ hD
    have := (ht.comp (tendsto_comap (f := fun x : Λ => (x : V f)))).sub_const L
    simpa [Function.comp_def] using this
  have e : (fun x : Λ => F x) = (fun x : Λ => F x - L) + (fun _ => L) := by funext; simp
  rw [e, hM.1.1 _ _ hD (bdd_const L), h0, lim_const hM.1, zero_add]

theorem meanSplit_ok : MeanSplit := by
  intro f Λ LIM H _ _ a r Nh B hM hb haa har hra
  have hpa : ∀ x, ‖a x‖ ≤ B := fun x => (hb x).1
  have hpr : ∀ x, ‖r x‖ ≤ B := fun x => (hb x).2
  constructor
  · intro σ hσ
    have e : (fun x : Λ => inner ℂ (a x + r x) (a ((x : V f) + σ) + r ((x : V f) + σ))) =
        (fun x : Λ => inner ℂ (a x) (a ((x : V f) + σ))) +
        (fun x : Λ => inner ℂ (a x) (r ((x : V f) + σ))) +
        ((fun x : Λ => inner ℂ (r x) (a ((x : V f) + σ))) +
         (fun x : Λ => inner ℂ (r x) (r ((x : V f) + σ)))) := by
      funext x; simp only [Pi.add_apply, inner_add_left, inner_add_right]; ring
    rw [e, hM.1.1 _ _ (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ))
        (Formalism.FourierDecayAlt.P.E2.bdd_add' (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ)),
      hM.1.1 _ _ (bdd_inner a a B hpa hpa σ) (bdd_inner a r B hpa hpr σ),
      hM.1.1 _ _ (bdd_inner r a B hpr hpa σ) (bdd_inner r r B hpr hpr σ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (a (x + σ))) (Nh σ) (bdd_inner a a B hpa hpa σ)
        (haa σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (a x) (r (x + σ))) 0 (bdd_inner a r B hpa hpr σ)
        (har σ hσ),
      lim_of_tendsto hM (fun x => inner ℂ (r x) (a (x + σ))) 0 (bdd_inner r a B hpr hpa σ)
        (hra σ hσ)]
    ring
  · intro S c hS
    have hS' : ∀ σ ∈ S, σ ∈ Λ := hS
    have hpd := Formalism.FourierDecayAlt.P.mean_matrix_posDef Λ H LIM hM.1.1 hM.1.2.1
      (fun g hg hpos => (hM.1.2.2.1 g hg hpos).1) hM.1.2.2.2.2 (fun x => r x) B (fun x => hpr x)
      (S.subtype (fun x => x ∈ Λ)) (fun σ => c σ)
    have eq : (∑ σ ∈ S, ∑ σ' ∈ S, (LIM fun x : Λ => inner ℂ (r x) (r ((x : V f) + (σ - σ')))) *
        c σ * starRingEnd ℂ (c σ')) =
        ∑ σ ∈ S.subtype (fun x => x ∈ Λ), ∑ σ' ∈ S.subtype (fun x => x ∈ Λ),
          (LIM fun x : Λ => inner ℂ (r x) (r ((x + (σ - σ') : Λ) : V f))) * c σ *
            starRingEnd ℂ (c σ') := by
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [← Finset.sum_subtype_of_mem (p := fun x => x ∈ Λ) _ hS']
      refine Finset.sum_congr rfl (fun σ' _ => ?_)
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub]
    beta_reduce
    rw [eq]
    exact hpd

end Formalism.FourierDecayAlt.P.MeanBoundsLimits

theorem Formalism.FourierDecayAlt.P.mean_bound_estimate : Formalism.FourierDecayAlt.crystallineComparison.MeanBound := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanBound_ok
theorem Formalism.FourierDecayAlt.P.mean_split_identity : Formalism.FourierDecayAlt.crystallineComparison.MeanSplit := Formalism.FourierDecayAlt.P.MeanBoundsLimits.meanSplit_ok
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SplitPrimeToDifferent
namespace Formalism.FourierDecayAlt.P.S6x4

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem mem_idl (E : Type) [Field E] [NumberField E] (g : ℕ) (k ν : ℤ) (t : E) (hg : 0 < g) :
    t ∈ idl E g k ν ↔ t / (g : E) ^ k ∈ dd E ^ ν := by
  have hg' : ((g : E) ^ k) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hg.ne')
  unfold idl
  rw [mul_comm, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_div_cancel_left₀ _ hg']
  · intro h
    exact ⟨_, h, by field_simp⟩

theorem trace_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    Algebra.trace ℚ E (complexConj E x) = Algebra.trace ℚ E x :=
  Algebra.trace_eq_of_algEquiv ((complexConj E).restrictScalars ℚ) x

theorem trace_rel (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E) :
    algebraMap (maximalRealSubfield E) E (Algebra.trace (maximalRealSubfield E) E x)
      = x + complexConj E x := by
  classical
  rw [trace_eq_sum_automorphisms]
  have hu : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, complexConj E} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      Algebra.IsQuadraticExtension.finrank_eq_two,
      Finset.card_pair (complexConj_ne_one E).symm]
  rw [hu, Finset.sum_pair (complexConj_ne_one E).symm]
  rfl

theorem exists_theta (E : Type) [Field E] [NumberField E] [IsCMField E]
    (h1 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤) :
    ∃ θ : 𝓞 E, (θ : E) + complexConj E (θ : E) = 1 := by
  set F := maximalRealSubfield E with hF
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FI E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [h1, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  let I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E))
  have hI0 : (I : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    intro hb
    have : Algebra.intTrace (𝓞 F) (𝓞 E) 1 ∈ I := ⟨1, rfl⟩
    rw [hb, Ideal.mem_bot] at this
    have h2 := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) 1
    rw [this, map_zero, map_one, ← map_one (algebraMap F E), Algebra.trace_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two] at h2
    norm_num at h2
  have hinv : (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ ≤ 1 := by
    intro a ha
    rw [FractionalIdeal.mem_inv_iff hI0] at ha
    have hmem : algebraMap F E a ∈ FractionalIdeal.dual (𝓞 F) F (1 : FI E) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)]
      intro b hb
      rw [FractionalIdeal.mem_one_iff] at hb
      obtain ⟨z, rfl⟩ := hb
      rw [Algebra.traceForm_apply, ← Algebra.smul_def, map_smul, smul_eq_mul,
        ← Algebra.algebraMap_intTrace (A := 𝓞 F)]
      have := ha (algebraMap (𝓞 F) F (Algebra.intTrace (𝓞 F) (𝓞 E) z))
        ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, ⟨z, rfl⟩, rfl⟩)
      rw [FractionalIdeal.mem_one_iff] at this
      exact this
    rw [hdual, FractionalIdeal.mem_one_iff] at hmem
    obtain ⟨z, hz⟩ := hmem
    have hint : IsIntegral ℤ a := by
      rw [← isIntegral_algebraMap_iff (B := E), ← hz]
      exact z.isIntegral_coe
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨⟨a, hint⟩, rfl⟩
  have hone : (1 : FractionalIdeal (𝓞 F)⁰ F) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 F)⁰ F) = I * (I : FractionalIdeal (𝓞 F)⁰ F)⁻¹ :=
          (mul_inv_cancel₀ hI0).symm
      _ ≤ I * 1 := mul_le_mul_right hinv _
      _ = I := mul_one _
  have h1I : (1 : F) ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := hone (FractionalIdeal.one_mem_one _)
  rw [FractionalIdeal.mem_coeIdeal] at h1I
  obtain ⟨w, ⟨θ, hθ⟩, hw⟩ := h1I
  refine ⟨θ, ?_⟩
  rw [← trace_rel, ← hF]
  have h2 := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) θ
  rw [hθ, hw] at h2
  rw [show ((θ : E)) = algebraMap (𝓞 E) E θ from rfl, ← h2, map_one]

end Formalism.FourierDecayAlt.P.S6x4

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x4
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem traceDualGe : Formalism.FourierDecayAlt.S6.DualSupset := by
  intro E _ _ _ hU g ν s hg l hl t ht
  have hrel : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ
      (𝓞 (maximalRealSubfield E)) (𝓞 E)
    unfold Unram at hU
    have h0 : (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
        (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
      rw [← hU]; exact differentIdeal_ne_bot
    rw [hU] at h
    have h2 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) *
        (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
        1 * (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by rw [one_mul]; exact h.symm
    simpa using mul_right_cancel₀ h0 h2
  obtain ⟨θ, hθ⟩ := exists_theta E hrel
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg.ne'
  have hd : dd E ≠ 0 := by
    unfold dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  have hdual : dd E ^ (-(ν + 1)) * dd E ^ ν = FractionalIdeal.dual ℤ ℚ (1 : FI E) := by
    rw [← zpow_add₀ hd, show -(ν + 1) + ν = -1 by ring, zpow_neg_one]
    unfold dd
    rw [coeIdeal_differentIdeal ℤ ℚ, inv_inv]
  unfold perLat at ht
  unfold dualIdl at hl
  rw [mem_twLat, mem_idl E g _ _ _ hg, mem_idl E g _ _ _ hg] at hl ht
  obtain ⟨hl1, hl2⟩ := hl
  obtain ⟨ht1, ht2⟩ := ht
  set ε : E := (-1) ^ s with hε
  have hεε : ε * ε = 1 := by rw [hε, ← pow_add, ← two_mul, pow_mul]; simp
  have hεc : complexConj E ε = ε := by rw [hε, map_pow, map_neg, map_one]
  set x : E := l * t / g with hx
  have hy : x + complexConj E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FI E) := by
    rw [← hdual]
    have m1 := FractionalIdeal.mul_mem_mul hl2 ht1
    have m2 := FractionalIdeal.mul_mem_mul hl2 ht2
    have m3 := FractionalIdeal.mul_mem_mul hl1 ht2
    have m2' := (dd E ^ (-(ν + 1)) * dd E ^ ν : FI E).coeToSubmodule.smul_mem (g : 𝓞 E) m2
    have m := (dd E ^ (-(ν + 1)) * dd E ^ ν : FI E).coeToSubmodule.add_mem
      ((dd E ^ (-(ν + 1)) * dd E ^ ν : FI E).coeToSubmodule.sub_mem m1 m2') m3
    have e : x + complexConj E x =
        (l - (-1) ^ (s + 1) * complexConj E l) / (g : E) ^ (0 : ℤ) * (t / (g : E) ^ (1 : ℤ))
          - (g : 𝓞 E) • ((l - (-1) ^ (s + 1) * complexConj E l) / (g : E) ^ (0 : ℤ)
            * ((t - ε * complexConj E t) / (g : E) ^ (2 : ℤ)))
          + l / (g : E) ^ (-1 : ℤ) * ((t - ε * complexConj E t) / (g : E) ^ (2 : ℤ)) := by
      rw [Algebra.smul_def, hx, map_div₀, map_mul, map_natCast, map_natCast, pow_succ, ← hε,
        zpow_zero, zpow_one, zpow_neg_one, zpow_ofNat]
      field_simp
      linear_combination (-(complexConj E l * complexConj E t)) * hεε
    rw [e]
    exact m
  have hz := (FractionalIdeal.mem_dual (one_ne_zero : (1 : FI E) ≠ 0)).1 hy (θ : E)
    ((FractionalIdeal.mem_one_iff _).2 ⟨θ, rfl⟩)
  rw [Algebra.traceForm_apply] at hz
  have e : Algebra.trace ℚ E ((x + complexConj E x) * (θ : E)) = Algebra.trace ℚ E x := by
    rw [add_mul, map_add (f := _), ← trace_conj E (complexConj E x * (θ : E)), map_mul (complexConj E),
      complexConj_apply_apply, ← map_add, ← mul_add, hθ, mul_one]
  rw [e] at hz
  exact hz

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasIterDeriv
namespace Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

def DsMeas : Prop := ∀ (B : Base) (S : Step B), S.Meas → S.I4 → ∀ Y ∈ S.J, ∀ (p : ℕ) k, Measurable fun ω => S.ds Y p ω k

theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := by
  intro p
  induction p with
  | zero => intro s; simpa using hm s
  | succ p ih =>
    intro s
    have hlim : ∀ ω, Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) atTop
        (𝓝 (iteratedDeriv (p + 1) (fun s => F s ω) s)) := by
      intro ω
      have hd : Differentiable ℝ (iteratedDeriv p (fun s => F s ω)) :=
        (hsm ω).differentiable_iteratedDeriv p (by exact_mod_cast WithTop.coe_lt_top _)
      have h1 := (hd s).hasDerivAt.tendsto_slope_zero
      rw [iteratedDeriv_succ]
      refine h1.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => by
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact this.ne')
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) ω => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) ?_ ?_
    · intro n
      exact ((ih _).sub (ih _)).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)
    · exact tendsto_pi_nhds.2 hlim

theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

end
end Formalism.FourierDecayAlt.P.LEx2.A3
end
