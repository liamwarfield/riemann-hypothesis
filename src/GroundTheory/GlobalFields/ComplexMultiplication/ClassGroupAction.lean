module

public import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionIso

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupActionLattice
open NumberField Module
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

abbrev periodLatticeEnd (L : PeriodPair) : Subring ℂ where
  carrier := {a | ∀ z ∈ L.lattice, a * z ∈ L.lattice}
  zero_mem' z _ := by rw [zero_mul]; exact zero_mem _
  one_mem' z hz := by simpa only [one_mul] using hz
  add_mem' ha hb z hz := by rw [add_mul]; exact add_mem (ha z hz) (hb z hz)
  neg_mem' ha z hz := by rw [neg_mul]; exact neg_mem (ha z hz)
  mul_mem' ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ)

def idealLattice (σ : K →+* ℂ) (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule ℤ ℂ :=
  Submodule.map σ.toIntAlgHom.toLinearMap ((I : Submodule (𝓞 K) K).restrictScalars ℤ)

theorem mem_idealLattice {I : FractionalIdeal (𝓞 K)⁰ K} {z : ℂ} :
    z ∈ idealLattice σ I ↔ ∃ x ∈ I, σ x = z :=
  Iff.rfl

theorem map_mem_idealLattice {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) :
    σ x ∈ idealLattice σ I :=
  ⟨x, hx, rfl⟩

theorem mem_of_map_mem_idealLattice {I : FractionalIdeal (𝓞 K)⁰ K} {x : K}
    (hx : σ x ∈ idealLattice σ I) : x ∈ I := by
  obtain ⟨y, hy, e⟩ := (mem_idealLattice σ).1 hx
  rwa [← σ.injective e]

theorem idealLattice_mul (I J : FractionalIdeal (𝓞 K)⁰ K) :
    idealLattice σ (I * J) = idealLattice σ I * idealLattice σ J := by
  rw [idealLattice, FractionalIdeal.coe_mul, Submodule.restrictScalars_mul, Submodule.map_mul]
  rfl

def cmRing : Subring ℂ := (σ.comp (algebraMap (𝓞 K) K)).range

theorem mem_cmRing {z : ℂ} : z ∈ cmRing σ ↔ ∃ a : 𝓞 K, σ (algebraMap (𝓞 K) K a) = z :=
  Iff.rfl

def cmRingEquiv : 𝓞 K ≃+* cmRing σ :=
  RingEquiv.ofBijective (σ.comp (algebraMap (𝓞 K) K)).rangeRestrict
    ⟨fun a b h ↦ (FaithfulSMul.algebraMap_injective (𝓞 K) K) (σ.injective (congrArg Subtype.val h)),
      (σ.comp (algebraMap (𝓞 K) K)).rangeRestrict_surjective⟩

section Quadratic

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]
include hK

theorem exists_rat_eq_of_im_eq_zero {x : K} (hx : (σ x).im = 0) : ∃ q : ℚ, algebraMap ℚ K q = x := by
  by_contra hq
  push_neg at hq
  have hind : LinearIndependent ℚ ![1, x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply hq (-(s / t))
      rw [Algebra.algebraMap_eq_smul_one] at *
      have : t • x = -(s • (1 : K)) := eq_neg_of_add_eq_zero_right hst
      calc (-(s / t)) • (1 : K) = t⁻¹ • (-(s • (1 : K))) := by
            rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
        _ = x := by rw [← this, smul_smul, inv_mul_cancel₀ ht, one_smul]
  let b := basisOfLinearIndependentOfCardEqFinrank hind (by rw [hK]; rfl)
  have hreal : ∀ y : K, (σ y).im = 0 := by
    intro y
    rw [← b.sum_repr y, Fin.sum_univ_two]
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, map_add, Rat.smul_def, map_mul, map_one,
      mul_one, map_ratCast, Complex.add_im, Complex.mul_im, Complex.ratCast_im, Complex.ratCast_re,
      hx, Complex.one_im, zero_mul, mul_zero, add_zero]
  have hR : ComplexEmbedding.IsReal σ := by
    rw [ComplexEmbedding.isReal_iff]
    ext y
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
    exact hreal y
  exact InfinitePlace.isComplex_mk_iff.mp (IsTotallyComplex.isComplex _) hR

theorem exists_ringOfIntegers_not_rat : ∃ θ : 𝓞 K, ∀ q : ℚ, algebraMap ℚ K q ≠ algebraMap (𝓞 K) K θ := by
  by_contra hall
  push_neg at hall
  have hsurj : ∀ x : K, ∃ q : ℚ, algebraMap ℚ K q = x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    obtain ⟨qa, ha⟩ := hall a
    obtain ⟨qb, hb⟩ := hall b
    exact ⟨qa / qb, by rw [map_div₀, ha, hb]⟩
  have htop : (⊥ : Subalgebra ℚ K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨q, rfl⟩ := hsurj x
    exact Subalgebra.algebraMap_mem _ q
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  omega

omit [_root_.NumberField.IsTotallyComplex K] in
theorem card_chooseBasisIndex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Fintype.card (Free.ChooseBasisIndex ℤ I) = 2 := by
  rw [← hK, ← finrank_eq_card_basis (basisOfFractionalIdeal K I)]

def idealBasis (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Basis (Fin 2) ℚ K :=
  (basisOfFractionalIdeal K I).reindex (Fintype.equivFinOfCardEq (card_chooseBasisIndex hK I))

omit [_root_.NumberField.IsTotallyComplex K] in
theorem mem_span_idealBasis {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} :
    x ∈ Submodule.span ℤ (Set.range (idealBasis hK I)) ↔ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [idealBasis, Basis.range_reindex]
  exact mem_span_basisOfFractionalIdeal K

omit [_root_.NumberField.IsTotallyComplex K] in
theorem idealBasis_mem (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (i : Fin 2) :
    idealBasis hK I i ∈ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  (mem_span_idealBasis hK).1 (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_real {a c : K} (h : LinearIndependent ℚ ![a, c]) :
    LinearIndependent ℝ ![σ a, σ c] := by
  have ha : a ≠ 0 := by simpa using h.ne_zero 0
  have hσa : σ a ≠ 0 := (map_ne_zero σ).2 ha
  rw [LinearIndependent.pair_iff] at h ⊢
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero, Complex.real_smul, mul_eq_zero] at hst
    exact ⟨by exact_mod_cast hst.resolve_right hσa, rfl⟩
  · exfalso
    rw [Complex.real_smul, Complex.real_smul] at hst
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have hc : σ (c / a) = ((-(s / t) : ℝ) : ℂ) := by
      rw [map_div₀, div_eq_iff hσa]
      push_cast
      field_simp
      linear_combination hst
    obtain ⟨q, hq⟩ := exists_rat_eq_of_im_eq_zero σ hK (x := c / a) (by rw [hc, Complex.ofReal_im])
    have hq' : (q : K) = c / a := hq
    have e : q • a + (-1 : ℚ) • c = 0 := by
      rw [Rat.smul_def, Rat.smul_def, hq', div_mul_cancel₀ _ ha]
      simp
    exact absurd (h q (-1) e).2 (by norm_num)

def idealPeriodPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : PeriodPair where
  ω₁ := σ (idealBasis hK I 0)
  ω₂ := σ (idealBasis hK I 1)
  indep := by
    apply linearIndependent_real σ hK
    have := (idealBasis hK I).linearIndependent
    convert this using 1
    ext i
    fin_cases i <;> rfl

theorem lattice_idealPeriodPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (idealPeriodPair σ hK I).lattice = idealLattice σ I := by
  ext z
  rw [PeriodPair.mem_lattice, mem_idealLattice]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m • idealBasis hK I 0 + n • idealBasis hK I 1, ?_, ?_⟩
    · rw [← FractionalIdeal.mem_coe]
      exact Submodule.add_mem _
        (Submodule.smul_of_tower_mem _ m (FractionalIdeal.mem_coe.2 (idealBasis_mem hK I 0)))
        (Submodule.smul_of_tower_mem _ n (FractionalIdeal.mem_coe.2 (idealBasis_mem hK I 1)))
    · simp [idealPeriodPair, zsmul_eq_mul]
  · rintro ⟨x, hx, rfl⟩
    rw [← mem_span_idealBasis hK (I := I), Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨c 0, c 1, ?_⟩
    simp [Fin.sum_univ_two, idealPeriodPair, zsmul_eq_mul]

theorem latticeEnd_idealPeriodPair (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    periodLatticeEnd (idealPeriodPair σ hK I) = cmRing σ := by
  ext α
  show (∀ l ∈ (idealPeriodPair σ hK I).lattice, α * l ∈ (idealPeriodPair σ hK I).lattice) ↔ _
  rw [lattice_idealPeriodPair]
  constructor
  · intro hα
    set x₀ := idealBasis hK I 0
    have hx₀ : x₀ ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := idealBasis_mem hK I 0
    have hx₀0 : x₀ ≠ 0 := (idealBasis hK I).ne_zero 0
    obtain ⟨y, -, hy⟩ := (mem_idealLattice σ).1 (hα _ (map_mem_idealLattice σ hx₀))
    set k := y / x₀
    have hαk : α = σ k := by
      rw [map_div₀, hy, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hx₀0)]
    have hkI : ∀ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), k * x ∈ (I : FractionalIdeal (𝓞 K)⁰ K) := by
      intro x hx
      apply mem_of_map_mem_idealLattice σ
      rw [map_mul, ← hαk]
      exact hα _ (map_mem_idealLattice σ hx)
    have h1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) ≤ I := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hz
      exact hkI x hx
    have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 K)⁰ k
          = FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) *
            ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
            rw [mul_assoc, Units.mul_inv, mul_one]
        _ ≤ (I : FractionalIdeal (𝓞 K)⁰ K) *
            ((I⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :=
            mul_le_mul_left h1 _
        _ = 1 := Units.mul_inv I
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1
      (FractionalIdeal.spanSingleton_le_iff_mem.1 h2)
    exact ⟨a, by rw [RingHom.comp_apply, ha, hαk]⟩
  · rintro ⟨a, rfl⟩ l hl
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ).1 hl
    rw [RingHom.comp_apply, ← map_mul, ← Algebra.smul_def]
    exact map_mem_idealLattice σ (Submodule.smul_mem _ a hx)

theorem exists_idealLattice_of_latticeEnd_eq (L : PeriodPair) (hL : periodLatticeEnd L = cmRing σ) :
    ∃ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (c : ℂ), c ≠ 0 ∧
      (L.lattice : Set ℂ) = (c * ·) '' idealLattice σ I := by
  have hω : L.ω₁ ≠ 0 := by simpa using L.indep.ne_zero 0
  obtain ⟨θ, hθ⟩ := exists_ringOfIntegers_not_rat hK (K := K)
  have hθL : σ (algebraMap (𝓞 K) K θ) ∈ periodLatticeEnd L := by rw [hL]; exact ⟨θ, rfl⟩
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 (hθL _ L.ω₁_mem_lattice)
  have hn : n ≠ 0 := by
    rintro rfl
    apply hθ m
    apply σ.injective
    simp only [Int.cast_zero, zero_mul, add_zero] at hmn
    have h0 : (σ (algebraMap (𝓞 K) K θ) - m) * L.ω₁ = 0 := by linear_combination -hmn
    have h2 : σ (algebraMap (𝓞 K) K θ) = m := by
      linear_combination (mul_eq_zero.1 h0).resolve_right hω
    rw [h2]
    simp
  set y : K := (algebraMap (𝓞 K) K θ - m) / n
  have hy : σ y * L.ω₁ = L.ω₂ := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [show σ y = (σ (algebraMap (𝓞 K) K θ) - m) / n by simp [y], div_mul_eq_mul_div,
      div_eq_iff hn']
    linear_combination -hmn

  let M : Submodule (𝓞 K) K :=
    { carrier := {x | σ x * L.ω₁ ∈ L.lattice}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at *
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a x hx ↦ by
        simp only [Set.mem_setOf_eq] at *
        rw [Algebra.smul_def, map_mul, mul_assoc]
        have ha : σ (algebraMap (𝓞 K) K a) ∈ periodLatticeEnd L := by rw [hL]; exact ⟨a, rfl⟩
        exact ha _ hx }
  have hmem : ∀ x : K, x ∈ M ↔ σ x * L.ω₁ ∈ L.lattice := fun _ ↦ Iff.rfl
  have h1 : (1 : K) ∈ M := by rw [hmem, map_one, one_mul]; exact L.ω₁_mem_lattice
  have hyM : y ∈ M := by rw [hmem, hy]; exact L.ω₂_mem_lattice
  have hM : ∀ x ∈ M, ∃ a b : ℤ, x = a + b * y := by
    intro x hx
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.1 ((hmem x).1 hx)
    refine ⟨a, b, σ.injective ?_⟩
    apply mul_right_cancel₀ hω
    rw [← hab, map_add (f := _), map_mul, map_intCast, map_intCast, add_mul, mul_assoc, hy]
  have hspan : M = Submodule.span (𝓞 K) {1, y} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, b, rfl⟩ := hM x hx
      refine add_mem ?_ ?_
      · rw [← mul_one (a : K), ← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ a (Submodule.subset_span (by simp))
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ b (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      rintro z (rfl | rfl)
      · exact h1
      · exact hyM
  have hfg : M.FG := by
    rw [hspan]
    exact Submodule.fg_span (Set.toFinite _)
  let I₀ : FractionalIdeal (𝓞 K)⁰ K := ⟨M, FractionalIdeal.isFractional_of_fg hfg⟩
  have hI₀ : I₀ ≠ 0 := by
    intro h
    have : (1 : K) ∈ I₀ := h1
    rw [h, FractionalIdeal.mem_zero_iff] at this
    exact one_ne_zero this
  refine ⟨Units.mk0 I₀ hI₀, L.ω₁, hω, ?_⟩
  ext z
  simp only [SetLike.mem_coe, Set.mem_image]
  constructor
  · intro hz
    obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
    refine ⟨σ (a + b * y), map_mem_idealLattice σ (x := a + b * y) ?_, ?_⟩
    · show (a + b * y : K) ∈ M
      rw [hspan]
      refine add_mem ?_ ?_
      · rw [← mul_one (a : K), ← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ a (Submodule.subset_span (by simp))
      · rw [← zsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ b (Submodule.subset_span (by simp))
    · rw [map_add (f := _), map_mul, map_intCast, map_intCast]
      linear_combination (b : ℂ) * hy
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (mem_idealLattice σ).1 hw
    rw [mul_comm]
    exact (hmem x).1 hx

theorem latticeEnd_eq_cmRing_of_ringEquiv (L : PeriodPair) (e : periodLatticeEnd L ≃+* 𝓞 K) :
    periodLatticeEnd L = cmRing σ := by
  have : Algebra.IsQuadraticExtension ℚ K := { finrank_eq_two' := hK }
  let g : 𝓞 K →+* ℂ := (periodLatticeEnd L).subtype.comp e.symm.toRingHom
  have hg : Function.Injective g := Subtype.val_injective.comp e.symm.injective
  let τ : K →+* ℂ := IsFractionRing.lift hg
  have hτ : ∀ a : 𝓞 K, τ (algebraMap (𝓞 K) K a) = g a := IsFractionRing.lift_algebraMap hg

  have hrange : ∀ (φ ψ : K →+* ℂ), ∀ x : K, ∃ y : K, ψ y = φ x := by
    intro φ ψ x
    have hN : Normal ℚ K := Algebra.IsQuadraticExtension.normal ℚ K
    let E : IntermediateField ℚ ℂ := ψ.toRatAlgHom.fieldRange
    have e₁ : K ≃ₐ[ℚ] E := AlgEquiv.ofInjectiveField ψ.toRatAlgHom
    have hE := @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ E
      (Normal.of_algEquiv (h := hN) e₁)
      (φ.toRatAlgHom.comp e₁.symm.toAlgHom)
    have hx : φ x ∈ (φ.toRatAlgHom.comp e₁.symm.toAlgHom).fieldRange := ⟨e₁ x, by simp⟩
    have hx' : φ x ∈ E := hE ▸ hx
    obtain ⟨y, hy⟩ := hx'
    exact ⟨y, hy⟩

  have hint : ∀ (φ : K →+* ℂ) (y : K), IsIntegral ℤ (φ y) → ∃ b : 𝓞 K, algebraMap (𝓞 K) K b = y := by
    intro φ y hy
    have : IsIntegral ℤ y := (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 hy
    exact ⟨⟨y, (mem_integralClosure_iff ℤ K).2 this⟩, rfl⟩
  have hintσ : ∀ (φ : K →+* ℂ) (a : 𝓞 K), IsIntegral ℤ (φ (algebraMap (𝓞 K) K a)) := by
    intro φ a
    exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).2 a.isIntegral_coe
  ext z
  constructor
  · intro hz
    set a := e ⟨z, hz⟩
    have hza : g a = z := by simp [g, a]
    obtain ⟨y, hy⟩ := hrange τ σ (algebraMap (𝓞 K) K a)
    have hyint : IsIntegral ℤ (σ y) := by rw [hy]; exact hintσ τ a
    obtain ⟨b, rfl⟩ := hint σ y hyint
    refine ⟨b, ?_⟩
    rw [RingHom.comp_apply, hy, hτ, hza]
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := hrange σ τ (algebraMap (𝓞 K) K a)
    have hyint : IsIntegral ℤ (τ y) := by rw [hy]; exact hintσ σ a
    obtain ⟨b, rfl⟩ := hint τ y hyint
    rw [RingHom.comp_apply, ← hy, hτ]
    exact (e.symm b).2

theorem classGroup_mk_eq_iff (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ClassGroup.mk K I = ClassGroup.mk K J ↔
      ∃ c : ℂ, c ≠ 0 ∧ (idealLattice σ J : Set ℂ) = (c * ·) '' idealLattice σ I := by
  constructor
  · intro h
    have h1 : ClassGroup.mk K (I⁻¹ * J) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    rw [ClassGroup.mk_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1.principal
    have hJ : (J : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) := by
      have e : ((I⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
          FractionalIdeal.spanSingleton (𝓞 K)⁰ k := by
        apply FractionalIdeal.coeToSubmodule_injective
        show ((↑(I⁻¹ * J) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
          ((FractionalIdeal.spanSingleton (𝓞 K)⁰ k : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
        rw [FractionalIdeal.coe_spanSingleton]
        exact hk
      calc (J : FractionalIdeal (𝓞 K)⁰ K)
          = (I : FractionalIdeal (𝓞 K)⁰ K) * ((I⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
              FractionalIdeal (𝓞 K)⁰ K) := by
            rw [Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
        _ = _ := by rw [e, mul_comm]
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [FractionalIdeal.spanSingleton_zero, zero_mul] at hJ
      exact J.ne_zero hJ
    refine ⟨σ k, (map_ne_zero σ).2 hk0, ?_⟩
    ext z
    simp only [SetLike.mem_coe, Set.mem_image, mem_idealLattice, hJ, FractionalIdeal.mem_singleton_mul]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨σ y, ⟨y, hy, rfl⟩, (map_mul σ k y).symm⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨k * y, ⟨y, hy, rfl⟩, map_mul σ k y⟩
  · rintro ⟨c, hc, hJ⟩
    obtain ⟨x₀, hx₀, hx₀0⟩ : ∃ x ∈ (I : FractionalIdeal (𝓞 K)⁰ K), x ≠ 0 :=
      ⟨idealBasis hK I 0, idealBasis_mem hK I 0, (idealBasis hK I).ne_zero 0⟩
    have hcx : c * σ x₀ ∈ (idealLattice σ J : Set ℂ) := by
      rw [hJ]; exact ⟨σ x₀, map_mem_idealLattice σ hx₀, rfl⟩
    obtain ⟨y₀, -, hy₀⟩ := (mem_idealLattice σ).1 hcx
    set k := y₀ / x₀
    have hck : c = σ k := by
      rw [map_div₀, hy₀, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hx₀0)]
    have hk0 : k ≠ 0 := by
      rintro h
      rw [h, map_zero] at hck
      exact hc hck
    have hJk : (J : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ k * (I : FractionalIdeal (𝓞 K)⁰ K) := by
      ext x
      rw [FractionalIdeal.mem_singleton_mul]
      constructor
      · intro hx
        have : σ x ∈ (idealLattice σ J : Set ℂ) := map_mem_idealLattice σ hx
        rw [hJ] at this
        obtain ⟨w, hw, hwx⟩ := this
        obtain ⟨y, hy, rfl⟩ := (mem_idealLattice σ).1 hw
        refine ⟨y, hy, σ.injective ?_⟩
        rw [← hwx, map_mul, hck]
      · rintro ⟨y, hy, rfl⟩
        apply mem_of_map_mem_idealLattice σ
        have : c * σ y ∈ (idealLattice σ J : Set ℂ) := by
          rw [hJ]; exact ⟨σ y, map_mem_idealLattice σ hy, rfl⟩
        rwa [map_mul, ← hck]
    have hJ' : J = toPrincipalIdeal (𝓞 K) K (Units.mk0 k hk0) * I := by
      apply Units.ext
      rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hJk]
    rw [hJ', map_mul]
    have : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K (Units.mk0 k hk0)) = 1 := by
      rw [ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
      exact ⟨⟨k, rfl⟩⟩
    rw [this, one_mul]

end Quadratic

end Elliptic
end GroundTheory.Global
end
end

abbrev cmRingOfEmbedding {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℂ) : Subring ℂ :=
  (σ.comp (algebraMap (NumberField.RingOfIntegers K) K)).range

open NumberField Module WeierstrassCurve GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem exists_variableChange_iff_homothetic (L L' : PeriodPair) :
    (∃ C : VariableChange ℂ, C • weierstrassCurve L = weierstrassCurve L') ↔
      ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  rw [← weierstrassCurve_j_eq_iff]
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨h₂, h₃⟩ := g₂_g₃_of_variableChange hC
    exact weierstrassCurve_j_eq_of_g₂_g₃ (C.u⁻¹).ne_zero h₂ h₃
  · intro h
    exact exists_variableChange_of_j_eq _ _ h

theorem latticeEnd_eq_of_homothetic {L L' : PeriodPair} {c : ℂ} (hc : c ≠ 0)
    (h : (L'.lattice : Set ℂ) = (c * ·) '' L.lattice) : periodLatticeEnd L' = periodLatticeEnd L := by
  have hmem : ∀ z, z ∈ L'.lattice ↔ ∃ l ∈ L.lattice, c * l = z := fun z ↦ by
    rw [← SetLike.mem_coe, h]; rfl
  ext α
  show (∀ l ∈ L'.lattice, α * l ∈ L'.lattice) ↔ (∀ l ∈ L.lattice, α * l ∈ L.lattice)
  constructor
  · intro hα l hl
    obtain ⟨l', hl', e⟩ := (hmem _).1 (hα (c * l) ((hmem _).2 ⟨l, hl, rfl⟩))
    have : l' = α * l := mul_left_cancel₀ hc (by rw [e]; ring)
    rwa [← this]
  · intro hα l hl
    obtain ⟨l', hl', rfl⟩ := (hmem l).1 hl
    exact (hmem _).2 ⟨α * l', hα l' hl', by ring⟩

variable {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ)

theorem idealLattice_mul_homothetic (I J : FractionalIdeal (𝓞 K)⁰ K) {c : ℂ} {Λ : Submodule ℤ ℂ}
    (h : (Λ : Set ℂ) = (c * ·) '' idealLattice σ I) :
    ((idealLattice σ J * Λ : Submodule ℤ ℂ) : Set ℂ) = (c * ·) '' idealLattice σ (J * I) := by
  have hΛ : Λ = (idealLattice σ I).map (LinearMap.mulLeft ℤ c) := by
    apply SetLike.coe_injective
    rw [h, Submodule.map_coe]
    rfl
  have key : idealLattice σ J * (idealLattice σ I).map (LinearMap.mulLeft ℤ c) =
      (idealLattice σ J * idealLattice σ I).map (LinearMap.mulLeft ℤ c) := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro m hm x hx
      obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.1 hx
      refine Submodule.mem_map.2 ⟨m * n, Submodule.mul_mem_mul hm hn, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      ring
    · rw [Submodule.map_le_iff_le_comap, Submodule.mul_le]
      intro m hm n hn
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply, show c * (m * n) = m * (c * n) by ring]
      exact Submodule.mul_mem_mul hm (Submodule.mem_map.2 ⟨n, hn, rfl⟩)
  rw [hΛ, key, idealLattice_mul, Submodule.map_coe]
  rfl

variable (K)

structure CMCurve where

  curve : WeierstrassCurve ℂ
  [isElliptic : curve.IsElliptic]

  endIso : Nonempty (isogEnd curve ≃+* 𝓞 K)

attribute [instance] CMCurve.isElliptic

def CMCurve.setoid : Setoid (CMCurve K) where
  r E E' := ∃ C : VariableChange ℂ, C • E.curve = E'.curve
  iseqv :=
    { refl := fun E ↦ ⟨1, one_smul _ _⟩
      symm := fun ⟨C, h⟩ ↦ ⟨C⁻¹, inv_smul_eq_of_smul_eq C h⟩
      trans := fun ⟨C, h⟩ ⟨C', h'⟩ ↦ ⟨C' * C, by rw [mul_smul, h, h']⟩ }

def ELL : Type _ := Quotient (CMCurve.setoid K)

variable {K}

def CMCurve.toEll (E : CMCurve K) : ELL K := Quotient.mk (CMCurve.setoid K) E

theorem CMCurve.toEll_eq_iff (E E' : CMCurve K) :
    E.toEll = E'.toEll ↔ ∃ C : VariableChange ℂ, C • E.curve = E'.curve :=
  Quotient.eq (r := CMCurve.setoid K)

theorem ELL.exists_eq (x : ELL K) : ∃ E : CMCurve K, E.toEll = x :=
  Quotient.exists_rep x

def CMCurve.ofLattice (L : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ) : CMCurve K where
  curve := weierstrassCurve L
  endIso := ⟨(latticeEndEquiv L).symm.trans ((RingEquiv.subringCongr hL).trans (cmRingEquiv σ).symm)⟩

def ellOf (L : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ) : ELL K := (CMCurve.ofLattice σ L hL).toEll

theorem ellOf_eq_ellOf_iff {L L' : PeriodPair} (hL : periodLatticeEnd L = cmRingOfEmbedding σ)
    (hL' : periodLatticeEnd L' = cmRingOfEmbedding σ) :
    ellOf σ L hL = ellOf σ L' hL' ↔ ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = (c * ·) '' L.lattice := by
  rw [ellOf, ellOf, CMCurve.toEll_eq_iff]
  exact exists_variableChange_iff_homothetic L L'

section Quadratic

variable (hK : finrank ℚ K = 2) [_root_.NumberField.IsTotallyComplex K]
include hK

theorem CMCurve.exists_lattice (E : CMCurve K) :
    ∃ (L : PeriodPair) (C : VariableChange ℂ) (hL : periodLatticeEnd L = cmRingOfEmbedding σ),
      C • E.curve = weierstrassCurve L ∧ (CMCurve.ofLattice σ L hL).toEll = E.toEll := by
  obtain ⟨L, C, hC⟩ := exists_variableChange_eq_weierstrassCurve E.curve
  have hL : periodLatticeEnd L = cmRingOfEmbedding σ := latticeEnd_eq_cmRing_of_ringEquiv σ hK L
    ((latticeEndEquiv L).trans ((vcEndEquiv C hC).symm.trans E.endIso.some))
  refine ⟨L, C, hL, hC, ?_⟩
  rw [CMCurve.toEll_eq_iff]
  exact ⟨C⁻¹, inv_smul_eq_of_smul_eq C hC⟩

theorem latticeEnd_ideal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    periodLatticeEnd (idealPeriodPair σ hK I) = cmRingOfEmbedding σ :=
  latticeEnd_idealPeriodPair σ hK I

def ellOfIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ELL K :=
  ellOf σ (idealPeriodPair σ hK I⁻¹) (latticeEnd_ideal σ hK I⁻¹)

theorem ellOfIdeal_eq_iff (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ellOfIdeal σ hK I = ellOfIdeal σ hK J ↔ ClassGroup.mk K I = ClassGroup.mk K J := by
  rw [ellOfIdeal, ellOfIdeal, ellOf_eq_ellOf_iff, lattice_idealPeriodPair, lattice_idealPeriodPair,
    ← classGroup_mk_eq_iff σ hK, map_inv, map_inv, inv_inj]

theorem ellOf_eq_ellOfIdeal {L : PeriodPair} (hL : periodLatticeEnd L = cmRingOfEmbedding σ)
    {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {c : ℂ} (hc : c ≠ 0)
    (h : (L.lattice : Set ℂ) = (c * ·) '' idealLattice σ I) :
    ellOf σ L hL = ellOfIdeal σ hK I⁻¹ := by
  rw [ellOfIdeal, ellOf_eq_ellOf_iff, inv_inv, lattice_idealPeriodPair]
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [h, Set.image_image]
  simp [inv_mul_cancel_left₀ hc]

theorem ellOfIdeal_surjective (x : ELL K) : ∃ I, ellOfIdeal σ hK I = x := by
  obtain ⟨E, rfl⟩ := ELL.exists_eq x
  obtain ⟨L, C, hL, -, hE⟩ := E.exists_lattice σ hK
  obtain ⟨I, c, hc, h⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  exact ⟨I⁻¹, by rw [← hE, ← ellOf, ellOf_eq_ellOfIdeal σ hK hL hc h]⟩

theorem classGroup_mk_surjective (a : ClassGroup (𝓞 K)) :
    ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = a :=
  ClassGroup.induction (K := K) (P := fun a ↦ ∃ I, ClassGroup.mk K I = a) (fun I ↦ ⟨I, rfl⟩) a

def classToEll (a : ClassGroup (𝓞 K)) : ELL K :=
  ellOfIdeal σ hK (classGroup_mk_surjective hK a).choose

theorem classToEll_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    classToEll σ hK (ClassGroup.mk K I) = ellOfIdeal σ hK I :=
  (ellOfIdeal_eq_iff σ hK _ _).2 (classGroup_mk_surjective hK _).choose_spec

def ellEquiv : ClassGroup (𝓞 K) ≃ ELL K :=
  Equiv.ofBijective (classToEll σ hK)
    ⟨fun a b hab ↦ by
      obtain ⟨I, rfl⟩ := classGroup_mk_surjective hK a
      obtain ⟨J, rfl⟩ := classGroup_mk_surjective hK b
      rwa [classToEll_mk, classToEll_mk, ellOfIdeal_eq_iff] at hab,
    fun x ↦ by
      obtain ⟨I, rfl⟩ := ellOfIdeal_surjective σ hK x
      exact ⟨ClassGroup.mk K I, classToEll_mk σ hK I⟩⟩

theorem ellEquiv_mk (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ellEquiv σ hK (ClassGroup.mk K I) = ellOfIdeal σ hK I :=
  classToEll_mk σ hK I

def ellMulAction : MulAction (ClassGroup (𝓞 K)) (ELL K) :=
  (ellEquiv σ hK).symm.mulAction (ClassGroup (𝓞 K))

theorem ellMulAction_smul (a : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ hK).smul a x = ellEquiv σ hK (a * (ellEquiv σ hK).symm x) :=
  rfl

theorem exists_lattice_mul (L : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ L' : PeriodPair, L'.lattice = idealLattice σ ↑𝔞⁻¹ * L.lattice ∧ periodLatticeEnd L' = cmRingOfEmbedding σ := by
  obtain ⟨I, c, hc, h⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K) (↑𝔞⁻¹) h
  let P := idealPeriodPair σ hK (𝔞⁻¹ * I)
  let L' : PeriodPair :=
    { ω₁ := c * P.ω₁
      ω₂ := c * P.ω₂
      indep := by
        have := P.indep
        rw [LinearIndependent.pair_iff] at this ⊢
        intro s t hst
        apply this s t
        have hst' : c * (s • P.ω₁ + t • P.ω₂) = 0 := by
          rw [← hst]; simp only [Complex.real_smul]; ring
        exact (mul_eq_zero.1 hst').resolve_left hc }
  have hlat : (L'.lattice : Set ℂ) = (c * ·) '' P.lattice := by
    ext z
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, L']
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * P.ω₁ + n * P.ω₂, ⟨m, n, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨m, n, rfl⟩, rfl⟩
      exact ⟨m, n, by ring⟩
  refine ⟨L', ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [hlat, h', lattice_idealPeriodPair, Units.val_mul]
  · rw [latticeEnd_eq_of_homothetic hc hlat]
    exact latticeEnd_ideal σ hK _

theorem classGroup_smul_ellOf (L L' : PeriodPair) (hL : periodLatticeEnd L = cmRingOfEmbedding σ)
    (hL' : periodLatticeEnd L' = cmRingOfEmbedding σ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : L'.lattice = idealLattice σ ↑𝔞⁻¹ * L.lattice) :
    (ellMulAction σ hK).smul (ClassGroup.mk K 𝔞) (ellOf σ L hL) = ellOf σ L' hL' := by
  obtain ⟨I, c, hc, hI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have h' := idealLattice_mul_homothetic σ (I : FractionalIdeal (𝓞 K)⁰ K) (↑𝔞⁻¹) hI
  rw [← h, ← Units.val_mul] at h'
  have e1 : ellOf σ L hL = ellEquiv σ hK (ClassGroup.mk K I⁻¹) := by
    rw [ellEquiv_mk]; exact ellOf_eq_ellOfIdeal σ hK hL hc hI
  have e2 : ellOf σ L' hL' = ellEquiv σ hK (ClassGroup.mk K (𝔞⁻¹ * I)⁻¹) := by
    rw [ellEquiv_mk]; exact ellOf_eq_ellOfIdeal σ hK hL' hc h'
  rw [ellMulAction_smul, e1, e2, Equiv.symm_apply_apply]
  congr 1
  rw [mul_inv_rev, inv_inv, map_mul, mul_comm]

theorem existsUnique_smul_eq (x y : ELL K) :
    ∃! a : ClassGroup (𝓞 K), (ellMulAction σ hK).smul a x = y := by
  refine ⟨(ellEquiv σ hK).symm y * ((ellEquiv σ hK).symm x)⁻¹, ?_, ?_⟩
  · simp only [ellMulAction_smul, inv_mul_cancel_right, Equiv.apply_symm_apply]
  · intro a ha
    rw [ellMulAction_smul] at ha
    rw [← ha, Equiv.symm_apply_apply, mul_inv_cancel_right]

theorem ell_smul_eq_self_iff (a : ClassGroup (𝓞 K)) (x : ELL K) :
    (ellMulAction σ hK).smul a x = x ↔ a = 1 := by
  constructor
  · intro h
    exact (existsUnique_smul_eq σ hK x x).unique h
      (by rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply])
  · rintro rfl
    rw [ellMulAction_smul, one_mul, Equiv.apply_symm_apply]

theorem finite_ell : Finite (ELL K) :=
  Finite.of_equiv _ (ellEquiv (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom hK)

end Quadratic

end Elliptic
end GroundTheory.Global
