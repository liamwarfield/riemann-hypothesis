module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfA
public import Lemmata.PowerMembership.PowMem

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.AevalEndApply
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.LevConstOfEv
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries

section PS

variable {LL : Type*} [Field LL]

theorem eq_X_mul_shift (f : PowerSeries LL) (h0 : constantCoeff f = 0) :
    f = X * mk (fun k => coeff (k + 1) f) := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

end PS

section Ev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)

def Vs : PowerSeries LL := mk fun k => coeff (k + 1) (W.lev c ζ Eπ)

def Ui : PowerSeries LL := (Vs W c ζ Eπ)⁻¹ ^ h'

def ev (a : LetA O n) (i : ℤ) : LL :=
  if 0 ≤ i + h' then coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') else 0

variable {W c ζ Eπ h'}

theorem levE_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) : W.lev c ζ Eπ = X * Vs W c ζ Eπ :=
  eq_X_mul_shift _ h0

theorem Vs_cc (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : constantCoeff (Vs W c ζ Eπ) ≠ 0 := by
  rw [Vs, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  exact h1

theorem Vs_Ui (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) : Vs W c ζ Eπ ^ h' * Ui W c ζ Eπ h' = 1 := by
  rw [Ui, ← mul_pow, PowerSeries.mul_inv_cancel _ (Vs_cc h1), one_pow]

theorem levΛ_eq (h0 : constantCoeff (W.lev c ζ Eπ) = 0) :
    W.lev c ζ (Eπ ^ h') = X ^ h' * Vs W c ζ Eπ ^ h' := by
  rw [map_pow, levE_eq h0, mul_pow]

theorem levΛ_Ui (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) :
    W.lev c ζ (Eπ ^ h') * Ui W c ζ Eπ h' = X ^ h' := by
  rw [levΛ_eq h0, mul_assoc, Vs_Ui h1, mul_one]

theorem ev_of_lt (a : LetA O n) {i : ℤ} (hi : i + h' < 0) : ev W c ζ Eπ h' a i = 0 := by
  unfold ev
  rw [if_neg (by omega)]

theorem ev_eq (a : LetA O n) {i : ℤ} (hi : 0 ≤ i + h') :
    ev W c ζ Eπ h' a i = coeff (i + h').toNat (W.lev c ζ a * Ui W c ζ Eπ h') := by
  unfold ev
  rw [if_pos hi]

theorem ev_add (a b : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (a + b) i = ev W c ζ Eπ h' a i + ev W c ζ Eπ h' b i := by
  unfold ev
  split_ifs
  · rw [map_add (W.lev c ζ) a b, add_mul, map_add (f := _)]
  · rw [add_zero]

theorem ev_zero (i : ℤ) : ev W c ζ Eπ h' (0 : LetA O n) i = 0 := by
  unfold ev
  split_ifs <;> simp

theorem ev_sum {ι : Type*} (s : Finset ι) (a : ι → LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (∑ k ∈ s, a k) i = ∑ k ∈ s, ev W c ζ Eπ h' (a k) i := by
  classical
  refine Finset.induction_on s (by rw [Finset.sum_empty, Finset.sum_empty, ev_zero]) ?_
  intro x s hx ih
  rw [Finset.sum_insert hx, Finset.sum_insert hx, ev_add, ih]

theorem ev_alg (x : O) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (algebraMap O (LetA O n) x * a) i = algebraMap O LL x * ev W c ζ Eπ h' a i := by
  unfold ev
  split_ifs
  · rw [map_mul (W.lev c ζ), AlgHom.commutes, mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul,
      Algebra.smul_def]
  · rw [mul_zero]

theorem ev_letE (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((letE c : LetA O n) * a) i = ev W c ζ Eπ h' a i := by
  unfold ev
  rw [map_mul (W.lev c ζ), Formalism.MainNotions.N.Ln34.ModelFPf.lev_letE (W := W) c ζ, one_mul]

private theorem coeff_lev_pow_eq_zero_of_lt (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (j : ℕ) (hj : j < h') :
    coeff j (W.lev c ζ (Eπ ^ h')) = 0 := by
  rw [levΛ_eq h0, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

private theorem coeff_lev_eq_sum_coeff_lev_pow_mul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (i : ℕ) :
    coeff i (W.lev c ζ a) = ∑ j ∈ Finset.range (i + h' + 1),
      coeff j (W.lev c ζ (Eπ ^ h')) * ev W c ζ Eπ h' a ((i : ℤ) - j) := by
  have e1 : coeff i (W.lev c ζ a) =
      coeff (i + h') (W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h')) := by
    have e : W.lev c ζ (Eπ ^ h') * (W.lev c ζ a * Ui W c ζ Eπ h') = W.lev c ζ a * X ^ h' := by
      rw [← levΛ_Ui h0 h1]
      ring
    rw [e, PowerSeries.coeff_mul_X_pow]
  rw [e1, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [ev_eq a (by omega), show ((i : ℤ) - j + h').toNat = i + h' - j by omega]

theorem serMul_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    {V : Type} [AddCommGroup V] [Module LL V] (a : LetA O n) (d : V) (i : ℤ) :
    serMul (W.lev c ζ (Eπ ^ h')) (fun k => ev W c ζ Eπ h' a k • d) i = serC (W.lev c ζ a) d i := by
  unfold serMul serC
  split_ifs with hi
  · obtain ⟨i', rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (i' + h' + 1)) ?_]
    · simp only [smul_smul, ← Finset.sum_smul]
      rw [Int.toNat_natCast, coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i']
    · intro j hj
      rw [Function.mem_support] at hj
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      apply hj
      simp only
      rw [ev_of_lt a (by omega), zero_smul, smul_zero]
  · have hz : (fun j : ℕ => coeff j (W.lev c ζ (Eπ ^ h')) •
        (fun k => ev W c ζ Eπ h' a k • d) (i - j)) = fun _ => 0 := by
      funext j
      by_cases hj : j < h'
      · rw [coeff_lev_pow_eq_zero_of_lt h0 j hj, zero_smul]
      · simp only
        rw [ev_of_lt a (by omega), zero_smul, smul_zero]
    rw [hz, finsum_zero]

theorem lev_zero_of_ev (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0) (a : LetA O n) (t₀ : ℤ)
    (h : ∀ t < t₀, ev W c ζ Eπ h' a t = 0) (i : ℕ) (hi : (i : ℤ) < t₀ + h') :
    coeff i (W.lev c ζ a) = 0 := by
  have e : W.lev c ζ a = (W.lev c ζ a * Ui W c ζ Eπ h') * Vs W c ζ Eπ ^ h' := by
    rw [mul_assoc, mul_comm (Ui W c ζ Eπ h'), Vs_Ui h1, mul_one]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hev := h ((p.1 : ℤ) - h') (by omega)
  rw [ev_eq a (by omega), show ((p.1 : ℤ) - h' + h').toNat = p.1 by omega] at hev
  rw [hev, zero_mul]

theorem lev_const_of_ev (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (a : LetA O n) (t₁ : ℤ) (h : ∀ t < t₁, t ≠ 0 → ev W c ζ Eπ h' a t = 0) (i : ℕ)
    (hi : (i : ℤ) < t₁ + h') :
    coeff i (W.lev c ζ a) = ev W c ζ Eπ h' a 0 * coeff i (W.lev c ζ (Eπ ^ h')) := by
  rw [coeff_lev_eq_sum_coeff_lev_pow_mul_ev h0 h1 a i, Finset.sum_eq_single i]
  · rw [sub_self, mul_comm]
  · intro j _ hji
    by_cases hjh : j < h'
    · rw [coeff_lev_pow_eq_zero_of_lt h0 j hjh, zero_mul]
    · rw [h ((i : ℤ) - j) (by omega) (by omega), mul_zero]
  · intro hi'
    exact absurd (Finset.mem_range.mpr (by omega)) hi'

end Ev

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def twA (uE' : LetA O n) (h' : ℕ) : LetA O n →ₗ[O] LetA O n :=
  (LinearMap.mulRight O (uE' ^ h')).comp (W.γA W.gam).toLinearMap

variable {W}

theorem twA_apply (uE' : LetA O n) (h' : ℕ) (a : LetA O n) :
    twA W uE' h' a = W.γA W.gam a * uE' ^ h' := rfl

theorem aeval_end_apply {M : Type*} [AddCommGroup M] [Module O M] (f : Module.End O M) (P : Polynomial O)
    (x : M) : Polynomial.aeval f P x = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • (f ^ i) x := by
  first
  | (rw [Polynomial.aeval_eq_sum_range, LinearMap.coeFn_sum, Finset.sum_apply]
     simp only [LinearMap.smul_apply])
  | (simp [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]; done)

private theorem gammaA_mem_AΔ (g : W.Gam) {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA g a ∈ W.AΔ := by
  have hc : ∀ (g h : W.Gam) (a : LetA O n), W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
    intro g h a
    funext i
    show W.γ₀ g (W.γ₀ h (a i)) = W.γ₀ h (W.γ₀ g (a i))
    rw [← AlgHom.mul_apply, ← map_mul, mul_comm, map_mul, AlgHom.mul_apply]
  intro δ hδ
  rw [hc, ha δ hδ]

theorem twA_pow_mem (uE' : LetA O n) (h' : ℕ) (huΔ : uE' ∈ W.AΔ) (k : ℕ) {a : LetA O n}
    (ha : a ∈ W.AΔ) : (twA W uE' h' ^ k) a ∈ W.AΔ := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, twA_apply]
    exact Subalgebra.mul_mem _ (gammaA_mem_AΔ _ ih) (Subalgebra.pow_mem _ huΔ _)

private theorem gammaA_letE_eq_letE (g : W.Gam) (c : ZMod n) : W.γA g (letE c : LetA O n) = letE c := by
  funext i
  show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
  unfold letE
  by_cases h : i = c
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem twA_pow_letE (uE' : LetA O n) (h' : ℕ) (c : ZMod n) (k : ℕ) (a : LetA O n) :
    (twA W uE' h' ^ k) ((letE c : LetA O n) * a) = (letE c : LetA O n) * (twA W uE' h' ^ k) a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, twA_apply, twA_apply, map_mul,
      gammaA_letE_eq_letE, mul_assoc]

theorem aeval_twA_mem (uE' : LetA O n) (h' : ℕ) (huΔ : uE' ∈ W.AΔ) (P : Polynomial O) {a : LetA O n}
    (ha : a ∈ W.AΔ) : Polynomial.aeval (twA W uE' h') P a ∈ W.AΔ := by
  rw [aeval_end_apply]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (twA_pow_mem uE' h' huΔ i ha) _

theorem aeval_twA_letE (uE' : LetA O n) (h' : ℕ) (c : ZMod n) (P : Polynomial O) (a : LetA O n) :
    Polynomial.aeval (twA W uE' h') P ((letE c : LetA O n) * a) =
      (letE c : LetA O n) * Polynomial.aeval (twA W uE' h') P a := by
  rw [aeval_end_apply, aeval_end_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [twA_pow_letE, mul_smul_comm]

theorem ev_twA (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (twA W uE' h' a) i = u ^ i * ev W c ζ Eπ h' a i := by
  obtain ⟨V, hVdef⟩ : ∃ V, V = Vs W c ζ Eπ := ⟨_, rfl⟩
  have hEV : W.lev c ζ Eπ = PowerSeries.X * V := by
    ext k
    rcases k with _ | k
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hVdef]
      unfold Vs
      rw [PowerSeries.coeff_mk]
  have hV0 : PowerSeries.constantCoeff V ≠ 0 := by
    rw [hVdef, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Vs
    simpa [PowerSeries.coeff_mk] using h1
  have hVinv : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hV0
  have hlevu : W.lev c ζ uE * V = PowerSeries.C u * PowerSeries.rescale u V := by
    have h2 : W.lev c ζ (W.γA W.gam Eπ) = W.lev c ζ uE * W.lev c ζ Eπ := by rw [hγE, map_mul]
    rw [hlevγ, hEV, map_mul, PowerSeries.rescale_X] at h2
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := LL))
    calc PowerSeries.X * (W.lev c ζ uE * V) = W.lev c ζ uE * (PowerSeries.X * V) := by ring
      _ = PowerSeries.C u * PowerSeries.X * PowerSeries.rescale u V := h2.symm
      _ = PowerSeries.X * (PowerSeries.C u * PowerSeries.rescale u V) := by ring
  have hW' : W.lev c ζ uE' * W.lev c ζ uE = 1 := by rw [← map_mul, huu, map_one]
  have hR : PowerSeries.rescale u V * PowerSeries.rescale u V⁻¹ = 1 := by
    rw [← map_mul, hVinv, map_one]
  have hC : PowerSeries.C u * PowerSeries.C u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu, map_one]
  have hkey : W.lev c ζ uE' * V⁻¹ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ := by
    calc W.lev c ζ uE' * V⁻¹
        = W.lev c ζ uE' * V⁻¹ * (PowerSeries.C u * PowerSeries.C u⁻¹) *
            (PowerSeries.rescale u V * PowerSeries.rescale u V⁻¹) := by rw [hC, hR]; ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ *
            (W.lev c ζ uE' * (PowerSeries.C u * PowerSeries.rescale u V) * V⁻¹) := by ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ *
            ((W.lev c ζ uE' * W.lev c ζ uE) * (V * V⁻¹)) := by rw [← hlevu]; ring
      _ = PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹ := by rw [hW', hVinv]; ring
  have hmain : W.lev c ζ (twA W uE' h' a) * Ui W c ζ Eπ h' =
      PowerSeries.C (u⁻¹ ^ h') * PowerSeries.rescale u (W.lev c ζ a * Ui W c ζ Eπ h') := by
    rw [twA_apply, map_mul, map_pow, hlevγ]
    unfold Ui
    rw [← hVdef]
    simp only [map_mul, map_pow]
    calc PowerSeries.rescale u (W.lev c ζ a) * W.lev c ζ uE' ^ h' * V⁻¹ ^ h'
        = PowerSeries.rescale u (W.lev c ζ a) * (W.lev c ζ uE' * V⁻¹) ^ h' := by ring
      _ = PowerSeries.rescale u (W.lev c ζ a) *
            (PowerSeries.C u⁻¹ * PowerSeries.rescale u V⁻¹) ^ h' := by rw [hkey]
      _ = PowerSeries.C u⁻¹ ^ h' * (PowerSeries.rescale u (W.lev c ζ a) *
            PowerSeries.rescale u V⁻¹ ^ h') := by ring
  unfold ev
  split_ifs with hih
  · rw [hmain, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
    have hm : (((i + h').toNat : ℕ) : ℤ) = i + h' := Int.toNat_of_nonneg hih
    have hu' : u⁻¹ ^ h' * u ^ (i + h').toNat = u ^ i := by
      rw [← zpow_natCast u, hm, zpow_add₀ hu, zpow_natCast, inv_pow, mul_comm, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    rw [← mul_assoc, hu']
  · simp

theorem ev_twA_pow (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (k : ℕ) (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' ((twA W uE' h' ^ k) a) i = (u ^ i) ^ k * ev W c ζ Eπ h' a i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ev_twA c ζ Eπ h' h0 h1 uE uE' huu hγE u hu hlevγ, ih]
    ring

theorem ev_aeval_twA (c : ZMod n) (ζ : LL) (Eπ : LetA O n) (h' : ℕ)
    (h0 : constantCoeff (W.lev c ζ Eπ) = 0) (h1 : coeff 1 (W.lev c ζ Eπ) ≠ 0)
    (uE uE' : LetA O n) (huu : uE' * uE = 1) (hγE : W.γA W.gam Eπ = uE * Eπ) (u : LL) (hu : u ≠ 0)
    (hlevγ : ∀ a, W.lev c ζ (W.γA W.gam a) = rescale u (W.lev c ζ a)) (P : Polynomial O)
    (a : LetA O n) (i : ℤ) :
    ev W c ζ Eπ h' (Polynomial.aeval (twA W uE' h') P a) i =
      Polynomial.aeval (u ^ i) P * ev W c ζ Eπ h' a i := by
  have hzero : ev W c ζ Eπ h' 0 i = 0 := by
    unfold ev; split_ifs <;> simp
  have hadd : ∀ x y : LetA O n, ev W c ζ Eπ h' (x + y) i = ev W c ζ Eπ h' x i + ev W c ζ Eπ h' y i := by
    intro x y; unfold ev; split_ifs <;> simp [map_add (f := _), add_mul]
  have hsmul : ∀ (r : O) (x : LetA O n),
      ev W c ζ Eπ h' (r • x) i = algebraMap O LL r * ev W c ζ Eπ h' x i := by
    intro r x
    unfold ev
    split_ifs
    · first
      | (simp only [map_smul, smul_mul_assoc, PowerSeries.coeff_smul, Algebra.smul_def]; done)
      | (rw [map_smul, smul_mul_assoc, PowerSeries.coeff_smul, Algebra.smul_def])
      | (simp [Algebra.smul_def, mul_assoc]; done)
    · simp
  have hsum : ∀ (s : Finset ℕ) (g : ℕ → LetA O n),
      ev W c ζ Eπ h' (∑ k ∈ s, g k) i = ∑ k ∈ s, ev W c ζ Eπ h' (g k) i := by
    intro s g
    classical
    refine Finset.induction_on s ?_ ?_
    · simpa using hzero
    · intro k s hk ih
      rw [Finset.sum_insert hk, Finset.sum_insert hk, hadd, ih]
  rw [aeval_end_apply, Polynomial.aeval_eq_sum_range, Finset.sum_mul, hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsmul, ev_twA_pow c ζ Eπ h' h0 h1 uE uE' huu hγE u hu hlevγ, Algebra.smul_def]
  ring

theorem EE_aeval (Eπ : LetA O n) (h' : ℕ) (uE uE' : LetA O n) (huu : uE' * uE = 1)
    (hγE : W.γA W.gam Eπ = uE * Eπ) (P : Polynomial O) (f : W.EE) (a : LetA O n)
    (h : algebraMap (LetA O n) W.EE (Eπ ^ h') * f = algebraMap (LetA O n) W.EE a) :
    algebraMap (LetA O n) W.EE (Eπ ^ h') * Polynomial.aeval (W.γE W.gam).toLinearMap P f =
      algebraMap (LetA O n) W.EE (Polynomial.aeval (twA W uE' h') P a) := by
  have hγ : W.γE W.gam (algebraMap (LetA O n) W.EE (Eπ ^ h')) =
      algebraMap (LetA O n) W.EE (uE ^ h') * algebraMap (LetA O n) W.EE (Eπ ^ h') := by
    rw [W.γE_ext, ← map_mul, ← mul_pow, ← hγE]
    congr 1
    exact map_pow (W.γA W.gam) Eπ h'
  have hk : ∀ k : ℕ, algebraMap (LetA O n) W.EE (Eπ ^ h') * (((W.γE W.gam).toLinearMap ^ k) f) =
      algebraMap (LetA O n) W.EE ((twA W uE' h' ^ k) a) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h2 := congrArg (W.γE W.gam) ih
      rw [map_mul, hγ, W.γE_ext] at h2
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, twA_apply,
        AlgHom.toLinearMap_apply]
      calc algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (((W.γE W.gam).toLinearMap ^ k) f)
          = algebraMap (LetA O n) W.EE (uE' ^ h') * (algebraMap (LetA O n) W.EE (uE ^ h') *
              algebraMap (LetA O n) W.EE (Eπ ^ h') * W.γE W.gam (((W.γE W.gam).toLinearMap ^ k) f)) := by
            rw [← mul_assoc, ← mul_assoc, ← map_mul, ← mul_pow, huu, one_pow, map_one, one_mul]
        _ = algebraMap (LetA O n) W.EE (uE' ^ h') *
              algebraMap (LetA O n) W.EE (W.γA W.gam ((twA W uE' h' ^ k) a)) := by
            rw [h2]; rfl
        _ = algebraMap (LetA O n) W.EE (W.γA W.gam ((twA W uE' h' ^ k) a) * uE' ^ h') := by
            rw [map_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_end_apply, aeval_end_apply, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, hk i, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]

theorem aeval_γLA_tmul (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n) (P : Polynomial O)
    (e : W.EE) (z : LcQ W T π' c) :
    Polynomial.aeval (γLA W T π' c) P (e ⊗ₜ z) = Polynomial.aeval (W.γE W.gamK).toLinearMap P e ⊗ₜ z := by
  have hp : ∀ i : ℕ, (γLA W T π' c ^ i) (e ⊗ₜ z) = (((W.γE W.gamK).toLinearMap ^ i) e) ⊗ₜ z := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [γLA]
  rw [aeval_end_apply, aeval_end_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hp, TensorProduct.smul_tmul']

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

section Gen

theorem aeval_mem_of_stable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (f : Module.End R M) (hf : ∀ v ∈ S, f v ∈ S) (P : Polynomial R) {v : M}
    (hv : v ∈ S) : Polynomial.aeval f P v ∈ S := by
  first | exact Bl.PowerMembership.goal1 .. | (apply Bl.PowerMembership.goal1 <;> assumption) | (intros; apply Bl.PowerMembership.goal1 <;> assumption) | (apply @Bl.PowerMembership.goal1 <;> assumption) | (intros; apply @Bl.PowerMembership.goal1 <;> assumption) | (apply @Bl.PowerMembership.goal1 <;> first | assumption | infer_instance) | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P v hv | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P v | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf P | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f hf | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S f | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› S | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› ‹_› | exact @Bl.PowerMembership.goal1 R M ‹_› ‹_› | exact @Bl.PowerMembership.goal1 R M ‹_› | exact @Bl.PowerMembership.goal1 R M | exact @Bl.PowerMembership.goal1 R

theorem aeval_comm {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : Module.End R M)
    (P : Polynomial R) (v : M) : Polynomial.aeval f P (f v) = f (Polynomial.aeval f P v) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hq, map_add (f := _)]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul, ← Module.End.mul_apply, ← pow_succ, pow_succ',
      Module.End.mul_apply]

theorem ps_coeff_cancel {LL : Type*} [Field LL] (p g : PowerSeries LL)
    (hp : PowerSeries.constantCoeff p ≠ 0) (N : ℕ) (h : ∀ i < N, PowerSeries.coeff i (p * g) = 0) :
    ∀ i < N, PowerSeries.coeff i g = 0 := by
  intro i hi
  have e : g = p⁻¹ * (p * g) := by
    rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
  rw [e, PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
  rw [h q.2 (by omega), mul_zero]

end Gen

section Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)

theorem tensor_eq_sum {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z : LA W T π' c) :
    z = ∑ i, (TensorProduct.equivFinsuppOfBasisRight bL z i) ⊗ₜ bL i := by
  calc z = (TensorProduct.equivFinsuppOfBasisRight bL).symm (TensorProduct.equivFinsuppOfBasisRight bL z) := by
        simp
    _ = ∑ i, (TensorProduct.equivFinsuppOfBasisRight bL z i) ⊗ₜ bL i := by
        rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]

theorem coord_γLA {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z : LA W T π' c) (i : Fin r) :
    TensorProduct.equivFinsuppOfBasisRight bL (γLA W T π' c z) i =
      W.γE W.gamK (TensorProduct.equivFinsuppOfBasisRight bL z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hx, hy, map_add (f := _), Finsupp.add_apply, map_add (f := _)]
  | tmul e l =>
    rw [ModelFPf.γLA_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply, Finsupp.mapRange_apply]
    exact ((W.γE W.gamK).toLinearMap.map_smul _ _).symm

theorem coord_sub {r : ℕ} (bL : Basis (Fin r) O (LcQ W T π' c)) (z z' : LA W T π' c) (i : Fin r) :
    TensorProduct.equivFinsuppOfBasisRight bL (z - z') i =
      TensorProduct.equivFinsuppOfBasisRight bL z i - TensorProduct.equivFinsuppOfBasisRight bL z' i := by
  rw [map_sub, Finsupp.sub_apply]

variable {W T π' c}

theorem valAt_zero (ζ : LL) (hvsmul : ∀ (a : O) x, x ∈ NcS W T (c - 1) →
      valAt W T c ζ (a • x) = algebraMap O LL a • valAt W T c ζ x) : valAt W T c ζ 0 = 0 := by
  have h := hvsmul 0 0 (Submodule.zero_mem _)
  rw [zero_smul, map_zero, zero_smul] at h
  exact h

theorem valAt_sum (ζ : LL)
    (hvadd : ∀ x y, x ∈ NcS W T (c - 1) → y ∈ NcS W T (c - 1) →
      valAt W T c ζ (x + y) = valAt W T c ζ x + valAt W T c ζ y)
    (hvsmul : ∀ (a : O) x, x ∈ NcS W T (c - 1) →
      valAt W T c ζ (a • x) = algebraMap O LL a • valAt W T c ζ x)
    {ι : Type*} (s : Finset ι) (co : ι → O) (y : ι → W.DD T) (hy : ∀ i, y i ∈ NcS W T (c - 1)) :
    valAt W T c ζ (∑ i ∈ s, co i • y i) = ∑ i ∈ s, algebraMap O LL (co i) • valAt W T c ζ (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, valAt_zero ζ hvsmul]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hvadd _ _ (Submodule.smul_mem _ _ (hy a)) (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hy i)),
      hvsmul _ _ (hy a), ih]

theorem mkL_sum {ι : Type*} (s : Finset ι) (co : ι → O) (y : ι → W.DD T)
    (hy : ∀ i, y i ∈ NcS W T (c - 1)) (h : ∑ i ∈ s, co i • y i ∈ NcS W T (c - 1)) :
    mkL W T π' c (∑ i ∈ s, co i • y i) h = ∑ i ∈ s, co i • mkL W T π' c (y i) (hy i) := by
  have e : (⟨∑ i ∈ s, co i • y i, h⟩ : ↥(NcS W T (c - 1))) = ∑ i ∈ s, co i • ⟨y i, hy i⟩ := by
    ext
    simp
  unfold mkL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, show Submodule.Quotient.mk (∑ i ∈ s, co i • (⟨y i, hy i⟩ : ↥(NcS W T (c - 1)))) =
      ∑ i ∈ s, Submodule.Quotient.mk (p := (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype)
        (co i • (⟨y i, hy i⟩ : ↥(NcS W T (c - 1)))) from map_sum (Submodule.mkQ _) _ _]
  simp only [Submodule.Quotient.mk_smul]

end Loc

section NL

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

variable {W} {T : LocLat G Qp LL O} {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' : ℕ}
  {c : ZMod n}

theorem piNL_le (hπΔ : π' ∈ W.AΔ)
    (hA : ∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c) :
    piNL W T Pt π' Eπ h' c 1 ≤ NL W T Pt π' Eπ h' c := by
  rintro _ ⟨y, hy, rfl⟩
  rw [pow_one]
  exact hA π' hπΔ y hy

theorem piNL_γ (hγ : ∀ x ∈ NL W T Pt π' Eπ h' c, γLA W T π' c x ∈ NL W T Pt π' Eπ h' c)
    (hA : ∀ a ∈ W.AΔ, ∀ x ∈ NL W T Pt π' Eπ h' c, smulLA W T π' c a x ∈ NL W T Pt π' Eπ h' c)
    {uπ : LetA O n} (huπ : uπ ∈ W.AΔ) (hγπ : W.γA W.gamK π' = π' * uπ) {x : LA W T π' c}
    (hx : x ∈ piNL W T Pt π' Eπ h' c 1) : γLA W T π' c x ∈ piNL W T Pt π' Eπ h' c 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨smulLA W T π' c uπ (γLA W T π' c y), hA uπ huπ _ (hγ y hy), ?_⟩
  rw [pow_one, ModelFPf.γLA_smulLA, ModelFPf.smulLA_smulLA, hγπ]

end NL

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
