module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SdUniq

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq
noncomputable section

namespace PI.VolStabSW

namespace SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW

def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

section Lattice

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)


include hχ in
theorem transform_indicator (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ L
  · rw [Set.indicator_of_mem hy]
    have e : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (L : Set V)
      · simp [Set.indicator, hx, hy x hx]
      · simp [Set.indicator, hx]
    rw [e, integral_indicator_const _ hLo.measurableSet]
    simp
  · rw [Set.indicator_apply, if_neg hy]
    simp only [ann, Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨t, ht, hty⟩ := hy
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have key : ∫ x, f x ∂μ = χ t y * ∫ x, f x ∂μ := by
      calc ∫ x, f x ∂μ = ∫ x, f (t + x) ∂μ := (integral_add_left_eq_self f t).symm
        _ = ∫ x, χ t y * f x ∂μ := by
          congr 1
          funext x
          by_cases hx : x ∈ (L : Set V)
          · have htx : t + x ∈ L := L.add_mem ht hx
            have hx' : x ∈ L := hx
            simp [hf, Set.indicator, hx', htx, hχ]
          · have htx : t + x ∉ L := fun h => hx (by simpa using L.sub_mem h ht)
            have hx' : x ∉ L := hx
            simp [hf, Set.indicator, hx', htx]
        _ = χ t y * ∫ x, f x ∂μ := integral_const_mul _ _
    have h2 : (1 - χ t y) * ∫ x, f x ∂μ = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hty
    · exact h1


end Lattice

section Triv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)

end Triv

section Nontriv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K

theorem mem_of_psi (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  by_contra hn
  have ht0 : t ≠ 0 := fun h => hn ⟨0, zero_mem _, by simp [h]⟩
  have hs : r0 * t⁻¹ ∉ v.adicCompletionIntegers F := fun hs => h0 (by
    have := ht _ hs
    rwa [inv_mul_cancel_right₀ ht0] at this)
  have hs0 : r0 * t⁻¹ ≠ 0 := fun h => hs (by rw [h]; exact zero_mem _)
  have hr0 : r0 ≠ 0 := fun h => hs0 (by rw [h, zero_mul])
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hs
  have hlt := ((Valued.v : Valuation (Fv F v) _).one_lt_val_iff hs0).mp hs
  refine hn ⟨(r0 * t⁻¹)⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_lt hlt), ?_⟩
  field_simp

end Nontriv

section Add

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in
theorem singleV_add (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  apply Subtype.ext
  exact Pi.single_add v r s

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have e : pairA F 0 (singleV F v (r + s)) =
      pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [singleV_add]
    show ((0 : Ainf F), singleV F v r + singleV F v s) =
      ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  unfold psiV
  rw [e, AddChar.map_add_eq_mul]

theorem continuous_singleV (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := _root_.PI.VolStabS.SdUniqW.continuous_singleV v

theorem continuous_psiV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV F ψ v) := by
  unfold psiV
  exact hψ.comp (continuous_const.prodMk (continuous_singleV v))

variable (R : Type) [CommRing R] [Algebra F R]

theorem BR_add (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X T Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (T + X) Y = BR R σ J T Y + BR R σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem pairHerm_add (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n (T + S) U = pairHerm R σ n T U + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
    map_add, mul_add]

end Add

section ContY

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_trace_tens : Continuous (Algebra.trace R (R ⊗[F] E)) :=
  IsModuleTopology.continuous_of_linearMap _

end ContY

end SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
noncomputable section

namespace PI.VolStabSW

namespace TensAllW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice Matrix

def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1

theorem lip_field (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hker : LinearMap.ker (Matrix.toLin' W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c (by simpa [Matrix.toLin'_apply] using hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' W) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h

theorem lip_pi {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type) [∀ i, CommRing (K i)]
    (h : ∀ i, LIP (K i)) : LIP (∀ i, K i) := by
  intro m n _ _ _ _ W hW
  have hP : ∀ i, ∃ P : Matrix n m (K i), P * W.map (fun x => x i) = 1 := by
    intro i
    refine h i m n (W.map (fun x => x i)) (fun c hc => ?_)
    have h0 := hW (fun b => Pi.single i (c b)) ?_
    · funext b
      have hb := congr_fun (congr_fun h0 b) i
      simpa using hb
    · funext a j
      by_cases hj : j = i
      · subst hj
        have ha := congr_fun hc a
        simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using ha
      · simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, hj]
  choose P hP using hP
  refine ⟨Matrix.of fun b a j => P j b a, ?_⟩
  ext a a' j
  have hj := congr_fun (congr_fun (hP j) a) a'
  rw [Matrix.mul_apply] at hj ⊢
  rw [Finset.sum_apply]
  simp only [Matrix.map_apply, Pi.mul_apply, Matrix.of_apply] at hj ⊢
  rw [hj]
  by_cases haa : a = a' <;> simp [Matrix.one_apply, haa]

theorem inj_of_isUnit {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n R) (P : Matrix n m R) (hP : IsUnit (P * W).det)
    (c : n → R) (hc : W *ᵥ c = 0) : c = 0 := by
  have h1 : (P * W) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  calc c = 1 *ᵥ c := (Matrix.one_mulVec c).symm
    _ = ((P * W)⁻¹ * (P * W)) *ᵥ c := by rw [Matrix.nonsing_inv_mul _ hP]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2

theorem wMat_mulVec (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) (j : Fin M) (l : Fin d) :
    (wMat b R X *ᵥ c) (j, l) =
      crd b R (∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j) l := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, wMat, crd, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem wMat_mulVec_eq_zero (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) :
    wMat b R X *ᵥ c = 0 ↔ ∀ j, ∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j = 0 := by
  constructor
  · intro h j
    apply (Algebra.TensorProduct.basis R b).repr.injective
    ext l
    have hl := congr_fun h (j, l)
    rw [wMat_mulVec] at hl
    simpa [crd] using hl
  · intro h
    funext q
    obtain ⟨j, l⟩ := q
    rw [wMat_mulVec, h j]
    simp [crd]

theorem linIndep_iff (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  have hexp : ∀ y : R ⊗[F] E, ∑ k, crd b R y k • ((1 : R) ⊗ₜ[F] b k) = y := by
    intro y
    have hs := (Algebra.TensorProduct.basis R b).sum_repr y
    simpa only [crd, Algebra.TensorProduct.basis_apply] using hs
  have hcrd : ∀ (g : Fin d → R) (l : Fin d), crd b R (∑ k, g k • ((1 : R) ⊗ₜ[F] b k)) l = g l := by
    intro g l
    have hb : ∀ k, ((1 : R) ⊗ₜ[F] b k) = Algebra.TensorProduct.basis R b k := fun k =>
      (Algebra.TensorProduct.basis_apply b k).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [crd, hb, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h c hc
    rw [wMat_mulVec_eq_zero] at hc
    have hg := h (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hc j)
    funext q
    obtain ⟨i, k⟩ := q
    have hk := congrArg (fun y => crd b R y k) (hg i)
    rw [hcrd] at hk
    simpa [crd] using hk
  · intro h g hg i
    have hc := h (fun q => crd b R (g q.1) q.2) (by
      rw [wMat_mulVec_eq_zero]
      intro j
      have hj := congr_fun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
      rw [← hj]
      refine Finset.sum_congr rfl fun i _ => ?_
      show (∑ k, crd b R (g i) k • ((1 : R) ⊗ₜ[F] b k)) * X i j = g i * X i j
      rw [hexp])
    rw [← hexp (g i)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk := congr_fun hc (i, k)
    simp only [Pi.zero_apply] at hk
    rw [hk, zero_smul]

section Top

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]

theorem continuous_wMat {a M : ℕ} :
    Continuous (fun X : Fin a → Fin M → R ⊗[F] E => wMat b R X) := by
  refine continuous_matrix fun p q => ?_
  exact (continuous_crd b R p.2).comp (continuous_const.mul
    ((continuous_apply p.1).comp (continuous_apply q.1)))

include b in
theorem isOpen_linIndep (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have hset : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R, {X | IsUnit (P * wMat b R X).det} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [linIndep_iff b R X]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ (wMat b R X) h
      refine ⟨P, ?_⟩
      rw [hP, Matrix.det_one]
      exact isUnit_one
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit (wMat b R X) P hP c hc
  rw [hset]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)

end Top

end TensAllW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW TensAllW

theorem lip_ainf (F : Type) [Field F] [NumberField F] : LIP (InfiniteAdeleRing F) := by
  classical
  exact lip_pi (fun v : InfinitePlace F => v.Completion) (fun v => lip_field _)

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
noncomputable section

namespace PI.VolStabSW.DeterminantAdmissible

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Topology Filter Set
  PI.VolStabSW.PositiveNearLattice MeasurableSpace
open scoped TensorProduct ENNReal RestrictedProduct

section Borel

variable {F : Type} [Field F] [NumberField F]

instance borel_Af : BorelSpace (Af F) := ⟨rfl⟩
instance borel_Fv (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (Fv F v) := ⟨rfl⟩
instance borel_tens {E : Type} [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

end Borel

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isCompact_intV : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v

theorem isClopen_intV : IsClopen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  ⟨(isCompact_intV v).isClosed, ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v⟩

instance lc_Fv : LocallyCompactSpace (Fv F v) :=
  (isCompact_intV v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isClopen_intV v).isOpen.mem_nhds (zero_mem (v.adicCompletionIntegers F)))

end Local

section Box1

variable {F : Type} [Field F] [NumberField F]

end Box1

end PI.VolStabSW.DeterminantAdmissible
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAFTop
namespace PI.VolStabSW.TopoAF

theorem afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := fun F _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩

end PI.VolStabSW.TopoAF
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSS
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

theorem isReduced_tens_field (F E C : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Field C] [Algebra F C] : IsReduced (C ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[F] E)

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSecSt
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

def SecGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (_hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (_hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (R : Type) [CommRing R] [Algebra F R], IsSemisimpleRing (R ⊗[F] E) →
    ∀ (a : ℕ) (x : Fin a → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) x →
      ∃ q : Fin M → Fin a → R ⊗[F] E, ∀ S : Matrix (Fin a) (Fin a) (R ⊗[F] E),
        S ∈ HermR R σ a →
        gramB R σ J x (fun j k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') = S

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHSt
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def FibLatGen : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
    ∀ (P : Set V), P ⊆ L → (∀ y ∈ P, ∀ Z ∈ Λ 0, y + Z ∈ P) → IsOpen P → IsClosed P →
    ∀ Nb ∈ 𝓝 T, (∀ x ∈ P, G x ∈ Nb → x ∈ U) →
      (∀ y ∈ P, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, P.indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ (P ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

end PI.VolStabSW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.EventuallyStruct
noncomputable section

namespace PI.VolStabSW

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

end Loc

end CompGAux

end PI.VolStabSW
end
end
