module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Formalism.PeriodIntegrals.UnimodLocStd
public import Formalism.PeriodIntegrals.QuotInv

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.EfRankSum
section -- merged from Formalism.PeriodIntegrals.EfRankSum
namespace PI

open Formalism.MainNotions.Gaps.EtaleWeightGaps

def EfRankSum : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [IsReduced A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    (ϖ : O), Irreducible ϖ → Module.Finite O ↥(As O A) → ∀ [∀ ζ : Pts O A, IsDVRAt ζ],
    Finite (Pts O A) ∧ (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank K A

end PI
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.EfRankSumMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Points
namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

theorem mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ζ.asIdeal ∈ (maximalIdeal O).primesOver ↥(As O A) := by
  haveI := ζ.isMaximal
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) ζ.asIdeal)).symm

theorem isMaximal_of_mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] {q : Ideal ↥(As O A)}
    (hq : q ∈ (maximalIdeal O).primesOver ↥(As O A)) : q.IsMaximal := by
  obtain ⟨hp, hl⟩ := hq
  have h : q.under O = maximalIdeal O := hl.over.symm
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) q
    (h ▸ IsLocalRing.maximalIdeal.isMaximal O)

noncomputable def ptsEquiv (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] :
    Pts O A ≃ (maximalIdeal O).primesOver ↥(As O A) where
  toFun ζ := ⟨ζ.asIdeal, mem_primesOver O A ζ⟩
  invFun q := ⟨q.1, isMaximal_of_mem_primesOver O A q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ptsEquiv_apply (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ((ptsEquiv O A ζ : (maximalIdeal O).primesOver ↥(As O A)) : Ideal ↥(As O A)) = ζ.asIdeal := rfl

theorem finite_pts (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] : Finite (Pts O A) := by
  classical
  haveI : Finite ((maximalIdeal O).primesOver ↥(As O A)) := by
    have hfin : ((maximalIdeal O).primesOver ↥(As O A)).Finite :=
      Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)
    exact hfin.to_subtype
  exact Finite.of_equiv _ (ptsEquiv O A).symm

end PI.UnitaryGroupMassFormula.EfRankSum
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Lattice
namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem isTorsionFree_alg (O : Type) [CommRing O] [IsDomain O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O A := by
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • a = r • b := hab
  have hr0 : r ≠ 0 := hr.ne_zero
  have hK : algebraMap O K r ≠ 0 := by
    simpa using (IsFractionRing.injective O K).ne hr0
  have h1 : (algebraMap O K r) • a = (algebraMap O K r) • b := by
    rw [algebraMap_smul, algebraMap_smul]
    exact hab'
  calc a = ((algebraMap O K r)⁻¹ * algebraMap O K r) • a := by rw [inv_mul_cancel₀ hK, one_smul]
    _ = ((algebraMap O K r)⁻¹ * algebraMap O K r) • b := by rw [mul_smul, h1, ← mul_smul]
    _ = b := by rw [inv_mul_cancel₀ hK, one_smul]

theorem isTorsionFree_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] :
    Module.IsTorsionFree O ↥(As O A) := by
  obtain ⟨h⟩ := isTorsionFree_alg O K A
  refine ⟨fun r hr a b hab => ?_⟩
  have hab' : r • (a : A) = r • (b : A) := by
    have h2 := congrArg (fun x : ↥(As O A) => (x : A)) hab
    simpa using h2
  exact Subtype.ext (h hr hab')

theorem free_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A]
    [Module.Finite O ↥(As O A)] : Module.Free O ↥(As O A) := by
  haveI := isTorsionFree_as O K A
  exact Module.free_of_finite_type_torsion_free'

theorem isLocalizedModule_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A] :
    IsLocalizedModule (nonZeroDivisors O) ((As O A).val.toLinearMap) := by
  obtain ⟨htf⟩ := isTorsionFree_alg O K A
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro s
    have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp only [Module.algebraMap_end_apply] at hxy
      exact htf (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero s.2)) hxy
    · intro y
      refine ⟨(algebraMap O K s)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro y
    have hy : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
    have hyO : IsAlgebraic O y := (IsFractionRing.isAlgebraic_iff O K A).mpr hy
    obtain ⟨c, hc0, hc⟩ := hyO.exists_integral_multiple
    refine ⟨(⟨c • y, hc⟩, ⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩), ?_⟩
    rfl
  · intro x₁ x₂ h
    exact ⟨1, by rw [Subtype.ext h]⟩

theorem finrank_as (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (A : Type) [CommRing A] [Algebra O A] [Algebra K A] [IsScalarTower O K A] [FiniteDimensional K A]
    [Module.Finite O ↥(As O A)] : Module.finrank O ↥(As O A) = Module.finrank K A := by
  haveI : Module.Free O ↥(As O A) := free_as O K A
  haveI := isLocalizedModule_as O K A
  let b := Module.Free.chooseBasis O ↥(As O A)
  let b' := b.ofIsLocalizedModule K (nonZeroDivisors O) ((As O A).val.toLinearMap)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end PI.UnitaryGroupMassFormula.EfRankSum
end

namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

theorem sum_ef (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] [Module.Flat O ↥(As O A)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank O ↥(As O A) := by
  classical
  have : Finite (Pts O A) := finite_pts O A
  let : Fintype (Pts O A) := Fintype.ofFinite _
  let : Fintype ((maximalIdeal O).primesOver ↥(As O A)) := Fintype.ofEquiv _ (ptsEquiv O A)
  rw [finsum_eq_sum_of_fintype, ← Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal O),
    ← (ptsEquiv O A).sum_comp]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [ptsEquiv_apply, ep_eq_ramificationIdx hϖ, fdeg_eq_inertiaDeg]

theorem efRankSum_main : PI.EfRankSum := by
  intro O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _
  haveI : Module.Free O ↥(As O A) := free_as O K A
  exact ⟨finite_pts O A, by rw [sum_ef O A hϖ, finrank_as O K A]⟩

end PI.UnitaryGroupMassFormula.EfRankSum
end

theorem ramificationDegreeSum : PI.EfRankSum := PI.UnitaryGroupMassFormula.EfRankSum.efRankSum_main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ScGapBig
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SpectralGapLarge.ScGapBigMain
namespace PI.UnitaryGroupMassFormula.ScGapBig

open PI.ScGapBig

theorem nat_bound (n m t : ℕ) (hn : 1801 ≤ n) (hm : m ≤ n + 1) (ht : t ≤ n + 6) :
    2 * (n + m * t) ^ 3 + t + 3 < 16 * n ^ 19 := by
  have hmt : m * t ≤ (n + 1) * (n + 6) := Nat.mul_le_mul hm ht
  have hsq : 1801 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have h1 : n + m * t ≤ 2 * n ^ 2 := by nlinarith
  have h2 : (n + m * t) ^ 3 ≤ (2 * n ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (2 * n ^ 2) ^ 3 = 8 * n ^ 6 := by ring
  have h4 : 2 ≤ n ^ 13 :=
    le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ n by omega) 13)
  have h5 : n ^ 19 = n ^ 6 * n ^ 13 := by ring
  have h6 : n ^ 6 * 2 ≤ n ^ 6 * n ^ 13 := Nat.mul_le_mul_left _ h4
  have h7 : n ≤ n ^ 6 := Nat.le_self_pow (by norm_num) n
  omega

theorem scGapBig_main : ScGapBig := by
  intro k r b hn hgap
  have hrk : rk48 k r = 2 * r + k + 1 := rfl
  obtain ⟨t, hodd, ht1, ht2⟩ : ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ t ≤ rk48 k r + 6 := by
    rcases Nat.even_or_odd (rk48 k r) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨rk48 k r + 5, ⟨a + 2, by omega⟩, le_refl _, by omega⟩
    · exact ⟨rk48 k r + 6, ⟨a + 3, by omega⟩, by omega, le_refl _⟩
  refine ⟨t, hodd, ht1, by omega, ?_⟩
  intro j hj
  have hm : 2 * r + 2 ≤ rk48 k r + 1 := by omega
  have hb := nat_bound (rk48 k r) (2 * r + 2) t hn hm ht2
  have hcast : 2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 <
      16 * (rk48 k r : ℝ) ^ 19 := by
    exact_mod_cast hb
  linarith [hgap j hj]

end PI.UnitaryGroupMassFormula.ScGapBig
end

theorem scGapBig : PI.ScGapBig.ScGapBig := PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylProduct.WeylProd
namespace PI.WeylProdWork

open Finset

noncomputable def wg (x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < j then (x i - x j) / ((j : ℝ) - (i : ℝ)) else 1

theorem denom_eq (n : ℕ) :
    ∏ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) =
      ∏ i ∈ range n, ((i.factorial : ℕ) : ℝ) := by
  have h1 : ∀ i ∈ range n, ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) = (((n - 1 - i).factorial : ℕ) : ℝ) := by
    intro i hi
    rw [mem_range] at hi
    rw [Finset.prod_Ico_eq_prod_range]
    have e : n - (i + 1) = n - 1 - i := by omega
    rw [e, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    exact Finset.prod_congr rfl (fun t _ => by ring)
  rw [Finset.prod_congr rfl h1]
  exact Finset.prod_range_reflect (fun i => ((i.factorial : ℕ) : ℝ)) n

theorem row_eq (x : ℕ → ℝ) (n i : ℕ) :
    ∏ j ∈ range n, wg x i j =
      (∏ j ∈ Ico (i + 1) n, (x i - x j)) / ∏ j ∈ Ico (i + 1) n, ((j : ℝ) - (i : ℝ)) := by
  rw [← Finset.prod_div_distrib]
  by_cases hin : i + 1 ≤ n
  · rw [← Finset.prod_range_mul_prod_Ico _ hin]
    have h1 : ∏ j ∈ range (i + 1), wg x i j = 1 := Finset.prod_eq_one (fun j hj => by
      rw [mem_range] at hj
      simp [wg, show ¬ i < j by omega])
    rw [h1, one_mul]
    exact Finset.prod_congr rfl (fun j hj => by
      rw [mem_Ico] at hj
      simp [wg, show i < j by omega])
  · push_neg at hin
    rw [Finset.Ico_eq_empty_of_le (by omega), Finset.prod_empty]
    exact Finset.prod_eq_one (fun j hj => by
      rw [mem_range] at hj
      simp [wg, show ¬ i < j by omega])

theorem weylProd : PI.WeylProd := by
  intro n μ w c hμ
  have hterm : ∀ i j : Fin n,
      (((if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = wg (shiftSeq w) i j := by
    intro i j
    unfold wg
    by_cases h : i < j
    · have h' : (i : ℕ) < (j : ℕ) := h
      rw [if_pos h, if_pos h']
      have hi : shiftSeq w (i : ℕ) = ((w i : ℤ) : ℝ) - ((i : ℕ) : ℝ) := by
        simp [shiftSeq]
      have hj : shiftSeq w (j : ℕ) = ((w j : ℤ) : ℝ) - ((j : ℕ) : ℝ) := by
        simp [shiftSeq]
      rw [hi, hj, hμ i, hμ j]
      push_cast
      ring
    · have h' : ¬ (i : ℕ) < (j : ℕ) := h
      rw [if_neg h, if_neg h', Rat.cast_one]
  rw [Rat.cast_prod]
  simp only [Rat.cast_prod]
  rw [Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => hterm i j))]
  have e1 : ∀ i : ℕ, ∏ j : Fin n, wg (shiftSeq w) i (j : ℕ) = ∏ j ∈ range n, wg (shiftSeq w) i j :=
    fun i => Fin.prod_univ_eq_prod_range (wg (shiftSeq w) i) n
  simp only [e1]
  rw [Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range n, wg (shiftSeq w) i j) n]
  simp only [row_eq]
  rw [Finset.prod_div_distrib, denom_eq]
  rfl

end PI.WeylProdWork
end

theorem weyl_product_formula : PI.WeylProd := PI.WeylProdWork.weylProd
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetOrd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DeterminantKernelOrder.ValNatCastEqOne
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerIso.DetOrdW

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

theorem val_natCast_eq_one (𝔭 : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) :
    𝔭.valuation K (s : K) = 1 := by
  have hcast : ((s : ℕ) : K) = algebraMap (𝓞 K) K (s : 𝓞 K) := by simp
  rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hs𝔭
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hs
  have h1 : (1 : 𝓞 K) ∈ 𝔭.asIdeal := by
    have e := congrArg (Int.cast : ℤ → 𝓞 K) hab
    push_cast at e
    rw [← e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hs𝔭) (Ideal.mul_mem_left _ _ hp)
  exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem val_le_one_of_den (𝔭 : HeightOneSpectrum (𝓞 K)) {p s : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) (hs : Nat.Coprime s p) {x : K}
    (hx : (s : K) * x ∈ (algebraMap (𝓞 K) K).range) : 𝔭.valuation K x ≤ 1 := by
  obtain ⟨r, hr⟩ := hx
  have h : 𝔭.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := 𝔭.valuation_le_one (K := K) r
  rw [hr, map_mul, val_natCast_eq_one 𝔭 hp hs, one_mul] at h
  exact h

theorem val_det_le_one (𝔭 : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal) {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : (ι → K) →ₗ[K] (ι → K))
    (hu : ∀ v : ι → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
      ∃ s : ℕ, Nat.Coprime s p ∧ ∀ w, (s : K) * u v w ∈ (algebraMap (𝓞 K) K).range) :
    𝔭.valuation K (LinearMap.det u) ≤ 1 := by
  set M := LinearMap.toMatrix' u with hM
  have hsingle : ∀ j : ι, ∀ w, (Pi.single j (1 : K) : ι → K) w ∈ (algebraMap (𝓞 K) K).range := by
    intro j w
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  choose s hs hsi using fun j => hu (Pi.single j 1) (hsingle j)
  have hent : ∀ i j, M i j * (s j : K) ∈ (algebraMap (𝓞 K) K).range := by
    intro i j
    rw [hM, LinearMap.toMatrix'_apply, mul_comm]
    exact hsi j i
  choose N hN using fun i j => hent i j
  have hdet : LinearMap.det u * ((∏ j, s j : ℕ) : K) = algebraMap (𝓞 K) K (Matrix.of N).det := by
    rw [RingHom.map_det, ← LinearMap.det_toMatrix', ← hM, Nat.cast_prod, ← Matrix.det_diagonal, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [Matrix.mul_diagonal, hN]
  apply val_le_one_of_den 𝔭 hp (Nat.Coprime.prod_left fun j _ => hs j)
  rw [mul_comm, hdet]
  exact RingHom.mem_range_self _ _

variable {E : Type} [Field E] [Algebra K E] {n : Type} [Fintype n]

theorem comp_integral {M : Set E} {p : ℕ} {g g' : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)}
    (hg : AtP M g p) (hg' : AtP M g' p) (v : Fin 4 × n → K)
    (hv : ∀ w, v w ∈ (algebraMap (𝓞 K) K).range) :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ w, (s : K) * g' (g.symm v) w ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨-, hgB⟩ := hg
  obtain ⟨hgA', -⟩ := hg'
  obtain ⟨s₁, hs₁, h₁⟩ := hgB v hv
  obtain ⟨s₂, hs₂, h₂⟩ := hgA' ((s₁ : K) • g.symm v) (fun a => by
    simpa [Pi.smul_apply, Algebra.smul_def] using h₁ a)
  refine ⟨s₂ * s₁, Nat.Coprime.mul_left hs₂ hs₁, fun w => ?_⟩
  have h := h₂ w
  rw [map_smul, Pi.smul_apply, smul_eq_mul] at h
  rw [Nat.cast_mul, mul_assoc]
  exact h

theorem detOrdIndep : DetOrdIndep := by
  intro K E _ _ _ _ n _ M p 𝔭 g g' g₀ hp hp𝔭 hg hg'
  classical
  let u : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K) :=
    ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
  let u' : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K) :=
    ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
  have h1 : 𝔭.valuation K (LinearMap.det u) ≤ 1 :=
    val_det_le_one 𝔭 hp𝔭 u (fun v hv => comp_integral hg hg' v hv)
  have h2 : 𝔭.valuation K (LinearMap.det u') ≤ 1 :=
    val_det_le_one 𝔭 hp𝔭 u' (fun v hv => comp_integral hg' hg v hv)
  have hprod : LinearMap.det u' * LinearMap.det u = 1 := by
    rw [← LinearMap.det_comp]
    have hid : u' ∘ₗ u = LinearMap.id := LinearMap.ext fun x => by simp [u, u']
    rw [hid, LinearMap.det_id]
  have hv1 : 𝔭.valuation K (LinearMap.det u) = 1 := by
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have h3 : 𝔭.valuation K (LinearMap.det u) * 𝔭.valuation K (LinearMap.det u') ≤ 𝔭.valuation K (LinearMap.det u) :=
      mul_le_of_le_one_right' h2
    rw [mul_comm, ← map_mul, hprod, map_one] at h3
    exact absurd h3 (not_le.2 hlt)
  have hrel : detRel g' g₀ = LinearMap.det u * detRel g g₀ := by
    unfold detRel
    rw [← LinearMap.det_comp]
    congr 1
    exact LinearMap.ext fun x => by simp [u]
  unfold ordK
  rw [hrel, map_mul, hv1, one_mul]

end PI.KerIso.DetOrdW
end
end

theorem ordRelativeDet_independence : PI.KerIso.DetOrdIndep :=
  PI.KerIso.DetOrdW.detOrdIndep
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerPerPair
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PeriodPairIndependence.IndepOfImNe
noncomputable section
open NumberField ComplexConjugate
open scoped nonZeroDivisors

namespace PI.KerLat.PerPairProof

theorem indep_of_im_ne {a b : ℂ} (h : (conj a * b).im ≠ 0) : LinearIndependent ℝ ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
  simp only [Complex.real_smul] at hst
  have h2 := congrArg Complex.im (congrArg (fun z => conj a * z) hst)
  simp only [mul_zero, Complex.zero_im] at h2
  have e1 : (conj a * ((s : ℂ) * a)).im = 0 := by
    rw [mul_left_comm, mul_comm (conj a) a, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_im]
  have e2 : (conj a * ((t : ℂ) * b)).im = t * (conj a * b).im := by
    rw [mul_left_comm, Complex.im_ofReal_mul]
  rw [mul_add, Complex.add_im, e1, e2, zero_add] at h2
  have ht : t = 0 := (mul_eq_zero.1 h2).resolve_right h
  refine ⟨?_, ht⟩
  rw [ht, Complex.ofReal_zero, zero_mul, add_zero] at hst
  exact (mul_eq_zero.1 hst).resolve_right ha |> Complex.ofReal_eq_zero.1

theorem im_ne {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (hφ : ∃ k : K, (φ k).im ≠ 0)
    (B : Module.Basis (Fin 2) ℚ K) : (conj (φ (B 0)) * φ (B 1)).im ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := hφ
  have hB0 : φ (B 0) ≠ 0 := (map_ne_zero φ).2 (B.ne_zero 0)
  have hs : ∀ (q : ℚ) (v : K),
      (conj (φ (B 0)) * φ (q • v)).im = (q : ℝ) * (conj (φ (B 0)) * φ v).im := by
    intro q v
    rw [Rat.smul_def, map_mul, map_ratCast, mul_left_comm, ← Complex.ofReal_ratCast,
      Complex.im_ofReal_mul]
  have e0 : (conj (φ (B 0)) * φ (B 0)).im = 0 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_im]
  have key : ∀ x : K, (conj (φ (B 0)) * φ x).im = 0 := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← B.sum_repr x, map_sum, Finset.mul_sum, Complex.im_sum, Fin.sum_univ_two, hs, hs, e0, h0]
    simp
  have h1 := key 1
  rw [map_one, mul_one, Complex.conj_im, neg_eq_zero] at h1
  have h2 := key k
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, neg_zero, zero_mul, add_zero] at h2
  have hre : (φ (B 0)).re ≠ 0 := fun hr => hB0 (Complex.ext hr h1)
  exact hk ((mul_eq_zero.1 h2).resolve_left hre)

theorem perPair : PI.KerLat.PerPair := by
  intro K _ _ φ cc δ hK hφ hcc hδ
  classical
  let b0 := NumberField.RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, hK]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  let bI : Module.Basis (Fin 2) ℤ cc := (Ideal.selfBasis b0 cc hcc).reindex e
  let f : cc →+ ℂ :=
    { toFun := fun c => δ * φ ((c : 𝓞 K) : K)
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add] }
  let ω : Fin 2 → ℂ := fun i => f (bI i)
  let g : cc →ₗ[ℤ] K :=
    ((algebraMap (𝓞 K) K).toAddMonoidHom.comp cc.subtype.toAddMonoidHom).toIntLinearMap
  have hg : LinearMap.ker g = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    exact Subtype.ext (IsFractionRing.injective (𝓞 K) K hxy)
  have hliZ : LinearIndependent ℤ (fun i => ((bI i : 𝓞 K) : K)) :=
    bI.linearIndependent.map' g hg
  have hli : LinearIndependent ℚ (fun i => ((bI i : 𝓞 K) : K)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 hliZ
  let B : Module.Basis (Fin 2) ℚ K :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hK])
  have hBi : ∀ i, B i = ((bI i : 𝓞 K) : K) := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hω : (conj (ω 0) * ω 1).im ≠ 0 := by
    have hB := im_ne φ hφ B
    rw [hBi, hBi] at hB
    have eq : conj (ω 0) * ω 1 =
        (Complex.normSq δ : ℂ) * (conj (φ ((bI 0 : 𝓞 K) : K)) * φ ((bI 1 : 𝓞 K) : K)) := by
      simp only [ω, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [Complex.normSq_eq_conj_mul_self, map_mul]
      ring
    rw [eq, Complex.im_ofReal_mul]
    exact mul_ne_zero (Complex.normSq_pos.2 hδ).ne' hB
  refine ⟨⟨ω 0, ω 1, indep_of_im_ne hω⟩, ?_⟩
  show (Submodule.span ℤ {ω 0, ω 1}).toAddSubgroup = _
  rw [← AddSubgroup.toIntSubmodule_closure]
  first
  | rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
  | change AddSubgroup.closure {ω 0, ω 1} = _
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro w (rfl | rfl)
    · exact ⟨bI 0, (bI 0).2, rfl⟩
    · exact ⟨bI 1, (bI 1).2, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    have hfc : δ * φ (c : K) = f ⟨c, hc⟩ := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfc, ← bI.sum_repr ⟨c, hc⟩, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) _
    fin_cases i
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ rfl

end PI.KerLat.PerPairProof
end
end

theorem exists_periodPairOfIdeal : PI.KerLat.PerPair := PI.KerLat.PerPairProof.perPair
end
