module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FractionFieldTranscendenceBasisExt

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTrace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTrace
set_option backward.isDefEq.respectTransparency false
open MvPolynomial

namespace GlobalTheory.CompanionTheory.TraceDerivation

theorem trace_map_derivation : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L]
    [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L]
    (D : Derivation K L L) (D0 : Derivation K F F),
    (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) →
    ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) =
      algebraMap F L (Algebra.trace F L (D y)) := by
  intro K F L _ _ _ _ _ _ _ _ _ D D0 h y
  classical
  let b := Module.finBasis F L
  let M := Algebra.leftMulMatrix b y
  let N := Algebra.leftMulMatrix b (D y)
  let C : Matrix (Fin (Module.finrank F L)) (Fin (Module.finrank F L)) F :=
    Matrix.of fun i j => b.repr (D (b j)) i
  have hmul : ∀ (z : L) (j), z * b j = ∑ i, Algebra.leftMulMatrix b z i j • b i := by
    intro z j
    simp only [Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr _).symm
  have hD : ∀ j, D (b j) = ∑ k, C k j • b k := fun j => (b.sum_repr _).symm
  have hsmul : ∀ (a : F) (x : L), D (a • x) = D0 a • x + a • D x := by
    intro a x
    rw [Algebra.smul_def, D.leibniz, h, smul_eq_mul, smul_eq_mul, Algebra.smul_def,
      Algebra.smul_def]
    ring
  have h1 : ∀ j, ∑ i, (M * C) i j • b i = y * D (b j) := by
    intro j
    rw [hD j, Finset.mul_sum]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, hmul y k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have h2 : ∀ j, ∑ i, (C * M) i j • b i = ∑ k, M k j • D (b k) := by
    intro j
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, mul_smul]
  have key : ∀ j, ∑ i, (N + M * C) i j • b i = ∑ i, (M.map D0 + C * M) i j • b i := by
    intro j
    have e := congrArg D (hmul y j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [D.leibniz, map_sum] at e
    simp only [hsmul, Finset.sum_add_distrib, smul_eq_mul] at e
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib, h1, h2, Matrix.map_apply]
    rw [← hmul (D y) j]
    rw [add_comm (D y * b j), mul_comm (D y), e]
  have hmat : N + M * C = M.map D0 + C * M := by
    ext i j
    have : b.repr (∑ i, (N + M * C) i j • b i) i = b.repr (∑ i, (M.map D0 + C * M) i j • b i) i := by
      rw [key j]
    rw [b.repr_sum_self, b.repr_sum_self] at this
    exact this
  have htr : Matrix.trace N = D0 (Matrix.trace M) := by
    have := congrArg Matrix.trace hmat
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_mul_comm M C] at this
    have h3 := add_right_cancel this
    rw [h3]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  congr 1
  rw [Algebra.trace_eq_matrix_trace b y, Algebra.trace_eq_matrix_trace b (D y)]
  exact htr.symm

end GlobalTheory.CompanionTheory.TraceDerivation
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivationCommutesWithTraceStatement
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_commutes_with_trace : ∀ (K F L : Type) [Field K] [CharZero K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L] [FiniteDimensional F L] (D : Derivation K L L) (D0 : Derivation K F F), (∀ x : F, D (algebraMap F L x) = algebraMap F L (D0 x)) → ∀ y : L, algebraMap F L (D0 (Algebra.trace F L y)) = algebraMap F L (Algebra.trace F L (D y)) := by
  first | exact @GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | exact GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation | (intros; apply GlobalTheory.CompanionTheory.TraceDerivation.trace_map_derivation <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RaTpowSinglePow
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

def fldF (K : Type) [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ) :
    IntermediateField K (FractionRing R) :=
  IntermediateField.adjoin K (Set.range fun k => algebraMap R (FractionRing R) (t k : R))

theorem ra_tpow_add {d : ℕ} (t : Fin d → Rˣ) (m m' : Fin d → ℤ) : tpow t (m + m') = tpow t m * tpow t m' := by
  simp only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]

theorem ra_tpow_zero {d : ℕ} (t : Fin d → Rˣ) : tpow t 0 = 1 := by
  simp [tpow]

theorem ra_tpow_single {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (z : ℤ) : tpow t (Pi.single k z) = ((t k ^ z : Rˣ) : R) := by
  unfold tpow
  rw [Finset.prod_eq_single k (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

theorem ra_expS_add {d : ℕ} (S : Finset (Fin (d + 1))) (m m' : Fin d → ℤ) (hm : m ∈ expS S) (hm' : m' ∈ expS S) :
    m + m' ∈ expS S := by
  refine ⟨fun k hk => ?_, fun h0 => ?_⟩
  · simpa using add_nonneg (hm.1 k hk) (hm'.1 k hk)
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    linarith [hm.2 h0, hm'.2 h0]

theorem ra_zero_mem_expS {d : ℕ} (S : Finset (Fin (d + 1))) : (0 : Fin d → ℤ) ∈ expS S :=
  ⟨fun _ _ => le_rfl, fun _ => by simp⟩

theorem ra_tpow_single_pow {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (z : ℤ) (N : ℕ) :
    tpow t (Pi.single k z) ^ N = tpow t (Pi.single k (z * N)) := by
  rw [ra_tpow_single, ra_tpow_single, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]

theorem ra_prod_pow {d : ℕ} (t : Fin d → Rˣ) (e : Fin d → ℕ) :
    ∏ j, (t j : R) ^ (e j) = tpow t (fun j => (e j : ℤ)) := by
  unfold tpow
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_natCast, Units.val_pow_eq_pow_val]

theorem ra_torusS_le_span (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) :
    ∀ x ∈ torusS K t S, x ∈ Submodule.span K (tpow t '' expS S) := by
  intro x hx
  have hx' : x ∈ Subalgebra.toSubmodule (torusS K t S) := hx
  rw [torusS, Algebra.adjoin_eq_span] at hx'
  refine Submodule.span_mono (fun y hy => ?_) hx'
  induction hy using Submonoid.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨0, ra_zero_mem_expS S, ra_tpow_zero t⟩
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm, rfl⟩ := hy
    obtain ⟨m', hm', rfl⟩ := hz
    exact ⟨m + m', ra_expS_add S m m' hm hm', ra_tpow_add t m m'⟩

theorem tpow_mem_torusS (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (m : Fin (n + 1) → ℤ) (hm : m ∈ expS S) :
    tpow t m ∈ torusS K t S :=
  Algebra.subset_adjoin ⟨m, hm, rfl⟩

theorem t_mem_torusS (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (hS : (0 : Fin (n + 2)) ∈ S) (k : Fin (n + 1)) :
    (t k : R) ∈ torusS K t S := by
  have h := tpow_mem_torusS (K := K) t S (Pi.single k 1) ⟨fun j _ => by
    rw [Pi.single_apply]; split_ifs <;> norm_num, fun h => absurd hS h⟩
  rwa [ra_tpow_single, zpow_one] at h

theorem torusS_loc (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) (S : Finset (Fin (n + 2)))
    (hS : (0 : Fin (n + 2)) ∈ S) :
    Function.Injective (MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) :
      MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t S) ∧
    ∀ a : torusS K t S, ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) g) ∧
      a * MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) g =
        MvPolynomial.aeval (fun k => (⟨t k, t_mem_torusS t S hS k⟩ : torusS K t S)) f := by
  classical
  set u : Fin (n + 1) → torusS K t S := fun k => ⟨t k, t_mem_torusS t S hS k⟩ with hu
  have hval : ∀ p : MvPolynomial (Fin (n + 1)) K,
      ((MvPolynomial.aeval u p : torusS K t S) : R) = MvPolynomial.aeval (fun k => (t k : R)) p := fun p => by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add (f := _), Subalgebra.coe_add, hp, hq]
    | mul_X p k hp => simp only [map_mul, Subalgebra.coe_mul, hp, MvPolynomial.aeval_X]; rfl
  have hinj := algebraicIndependent_iff_injective_aeval.mp ht
  refine ⟨fun p q h => hinj (by rw [← hval, ← hval, h]), fun a => ?_⟩
  have key : ∀ x (hx : x ∈ torusS K t S), ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval u g) ∧
        x * MvPolynomial.aeval (fun k => (t k : R)) g = MvPolynomial.aeval (fun k => (t k : R)) f := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      refine ⟨∏ j, MvPolynomial.X j ^ (m j).toNat, ∏ j, MvPolynomial.X j ^ (-m j).toNat, ?_, ?_⟩
      · have hmem : (fun j => -((-m j).toNat : ℤ)) ∈ expS S := by
          refine ⟨fun i hi => ?_, fun h0 => ?_⟩
          · have := hm.1 i hi
            simp only [neg_nonneg, Nat.cast_nonpos]
            omega
          · exact Finset.sum_nonpos fun i _ => by simp
        refine IsUnit.of_mul_eq_one ⟨_, tpow_mem_torusS t S _ hmem⟩ (Subtype.ext ?_)
        rw [Subalgebra.coe_mul, hval]
        simp only [map_prod, map_pow, MvPolynomial.aeval_X, Subalgebra.coe_one]
        rw [ra_prod_pow, ← ra_tpow_add]
        convert ra_tpow_zero t using 2
        ext j
        simp
      · simp only [map_prod, map_pow, MvPolynomial.aeval_X]
        rw [ra_prod_pow, ra_prod_pow, ← ra_tpow_add]
        congr 1
        ext j
        simp only [Pi.add_apply]
        omega
    | algebraMap c =>
      exact ⟨MvPolynomial.C c, 1, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨f1, g1, hg1, h1⟩ := hx
      obtain ⟨f2, g2, hg2, h2⟩ := hy
      refine ⟨f1 * g2 + f2 * g1, g1 * g2, by rw [map_mul]; exact hg1.mul hg2, ?_⟩
      simp only [map_add (f := _), map_mul]
      linear_combination (MvPolynomial.aeval (fun k => (t k : R)) g2) * h1 +
        (MvPolynomial.aeval (fun k => (t k : R)) g1) * h2
    | mul x y _ _ hx hy =>
      obtain ⟨f1, g1, hg1, h1⟩ := hx
      obtain ⟨f2, g2, hg2, h2⟩ := hy
      refine ⟨f1 * f2, g1 * g2, by rw [map_mul]; exact hg1.mul hg2, ?_⟩
      simp only [map_mul]
      linear_combination (y * MvPolynomial.aeval (fun k => (t k : R)) g2) * h1 +
        (MvPolynomial.aeval (fun k => (t k : R)) f1) * h2
  obtain ⟨f, g, hg, hfg⟩ := key a a.2
  exact ⟨f, g, hg, Subtype.ext (by rw [Subalgebra.coe_mul, hval, hval]; exact hfg)⟩

theorem torusS_frac [IsDomain R] (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (hS : S.Nonempty) (k : Fin (n + 1)) :
    ∃ a' ∈ torusS K t S, a' ≠ 0 ∧ (t k : R) * a' ∈ torusS K t S := by
  classical
  by_cases h0 : (0 : Fin (n + 2)) ∈ S
  · exact ⟨1, one_mem _, one_ne_zero, by rw [mul_one]; exact t_mem_torusS t S h0 k⟩
  · obtain ⟨s, hs⟩ := hS
    obtain ⟨j, rfl⟩ : ∃ j : Fin (n + 1), j.succ = s := Fin.exists_succ_eq.mpr fun h => h0 (h ▸ hs)
    refine ⟨tpow t (Pi.single j (-1)), tpow_mem_torusS t S _ ⟨fun i hi => ?_, fun _ => ?_⟩,
      by unfold tpow; exact Units.ne_zero _, ?_⟩
    · rw [Pi.single_apply]
      split_ifs with h
      · subst h; exact absurd hs hi
      · exact le_rfl
    · simp
    · have : (t k : R) * tpow t (Pi.single j (-1)) = tpow t (Pi.single k 1 + Pi.single j (-1)) := by
        rw [ra_tpow_add, ra_tpow_single t k 1, zpow_one]
      rw [this]
      refine tpow_mem_torusS t S _ ⟨fun i hi => ?_, fun _ => ?_⟩
      · have hij : i ≠ j := fun h => hi (h ▸ hs)
        simp only [Pi.add_apply, Pi.single_apply, hij, if_false, add_zero]
        split_ifs <;> norm_num
      · simp [Finset.sum_add_distrib]

theorem torusS_succ_span (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    ∀ x ∈ torusS K t (Finset.univ.erase k.succ), x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) := by
  intro x hx
  have hsub : expS (Finset.univ.erase k.succ) ⊆ {m | m ≠ fun _ => -1} := by
    intro m hm h
    have := hm.1 k (by simp)
    rw [h] at this
    norm_num at this
  exact Submodule.span_mono (Set.image_mono hsub) (ra_torusS_le_span t _ x hx)

theorem torus_scale [IsDomain R] (t : Fin (n + 1) → Rˣ) (i : Fin (n + 2)) :
    ∃ w ∈ torusS K t (Finset.univ.erase i), w ≠ 0 ∧
      ∀ x ∈ torusS K t Finset.univ, ∃ N : ℕ, w ^ N * x ∈ torusS K t (Finset.univ.erase i) := by
  classical
  have hscale : ∀ (A : Subalgebra K R) (w : R), w ∈ A → (∀ m, ∃ N : ℕ, w ^ N * tpow t m ∈ A) →
      ∀ x ∈ torusS K t Finset.univ, ∃ N : ℕ, w ^ N * x ∈ A := by
    intro A w hw hgen x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, _, rfl⟩ := hx
      exact hgen m
    | algebraMap c => exact ⟨0, by simpa using A.algebraMap_mem c⟩
    | add x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨N1 + N2, ?_⟩
      have : w ^ (N1 + N2) * (x + y) = w ^ N2 * (w ^ N1 * x) + w ^ N1 * (w ^ N2 * y) := by ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hw _) h1) (mul_mem (pow_mem hw _) h2)
    | mul x y _ _ hx hy =>
      obtain ⟨N1, h1⟩ := hx
      obtain ⟨N2, h2⟩ := hy
      refine ⟨N1 + N2, ?_⟩
      have : w ^ (N1 + N2) * (x * y) = (w ^ N1 * x) * (w ^ N2 * y) := by ring
      rw [this]
      exact mul_mem h1 h2
  have hne : ∀ z : ℤ, ∀ k, tpow t (Pi.single k z) ≠ 0 := fun z k => by unfold tpow; exact Units.ne_zero _
  induction i using Fin.cases with
  | zero =>
    have hS : ∀ i : Fin (n + 1), i.succ ∈ Finset.univ.erase (0 : Fin (n + 2)) := fun i =>
      Finset.mem_erase.mpr ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩
    refine ⟨tpow t (Pi.single 0 (-1)), tpow_mem_torusS t _ _ ⟨fun i hi => absurd (hS i) hi, fun _ => by simp⟩,
      hne _ _, hscale _ _ (tpow_mem_torusS t _ _ ⟨fun i hi => absurd (hS i) hi, fun _ => by simp⟩) fun m => ?_⟩
    refine ⟨(∑ k, m k).toNat, ?_⟩
    rw [ra_tpow_single_pow, ← ra_tpow_add]
    refine tpow_mem_torusS t _ _ ⟨fun i hi => absurd (hS i) hi, fun _ => ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
    omega
  | succ k =>
    have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ :=
      Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩
    have hk : ∀ i : Fin (n + 1), i.succ ∉ Finset.univ.erase k.succ → i = k := fun i hi => by
      by_contra h
      exact hi (Finset.mem_erase.mpr ⟨fun h' => h (Fin.succ_inj.mp h'), Finset.mem_univ _⟩)
    have hw : tpow t (Pi.single k 1) ∈ torusS K t (Finset.univ.erase k.succ) := by
      rw [ra_tpow_single, zpow_one]
      exact t_mem_torusS t _ h0 k
    refine ⟨tpow t (Pi.single k 1), hw, hne _ _, hscale _ _ hw fun m => ⟨(-m k).toNat, ?_⟩⟩
    rw [ra_tpow_single_pow, ← ra_tpow_add]
    refine tpow_mem_torusS t _ _ ⟨fun i hi => ?_, fun h => absurd h0 h⟩
    obtain rfl := hk i hi
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega

theorem prod_inv_mem (t : Fin (n + 1) → Rˣ) :
    (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := by
  have h := tpow_mem_torusS (K := K) t Finset.univ (fun _ => -1) ⟨fun k hk => absurd (Finset.mem_univ _) hk,
    fun h => absurd (Finset.mem_univ _) h⟩
  rwa [tpow, Finset.prod_congr rfl (fun k _ => zpow_neg_one (t k)), Finset.prod_inv_distrib] at h

theorem torusS_le_univ (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) :
    torusS K t S ≤ torusS K t Finset.univ :=
  Algebra.adjoin_mono (Set.image_mono fun m _ => ⟨fun k hk => absurd (Finset.mem_univ _) hk,
    fun h => absurd (Finset.mem_univ _) h⟩)

theorem inv_mem_univ (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    (((t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := by
  have h := tpow_mem_torusS (K := K) t Finset.univ (Pi.single k (-1)) ⟨fun k hk => absurd (Finset.mem_univ _) hk,
    fun h => absurd (Finset.mem_univ _) h⟩
  rwa [ra_tpow_single, zpow_neg_one] at h

theorem jacS_mono {d m : ℕ} (B B' : Subalgebra K R) (hB : B ≤ B') (D : Fin d → Derivation K R R) (κ : Fin m → Fin d) :
    jacS B D κ ≤ jacS B' D κ :=
  AddSubgroup.closure_mono fun _ ⟨b, bs, hy⟩ =>
    ⟨Subalgebra.inclusion hB b, fun l => Subalgebra.inclusion hB (bs l), hy⟩

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TorusMemFldF
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidFinPf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

theorem fldF_findim_pf_tpow (t : Fin (n + 1) → Rˣ) (m : Fin (n + 1) → ℤ) :
    algebraMap R (FractionRing R) (tpow t m) = ∏ k, (algebraMap R (FractionRing R) (t k : R)) ^ (m k) := by
  have h : algebraMap R (FractionRing R) (tpow t m) =
      (((Units.map (algebraMap R (FractionRing R)).toMonoidHom) (∏ k, t k ^ m k) : (FractionRing R)ˣ) :
        FractionRing R) := rfl
  rw [h, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem fldF_findim_pf_mem (t : Fin (n + 1) → Rˣ) :
    ∀ r ∈ torusS K t Finset.univ, algebraMap R (FractionRing R) r ∈ fldF K t := by
  intro r hr
  have hle : torusS K t Finset.univ ≤
      (fldF K t).toSubalgebra.comap (IsScalarTower.toAlgHom K R (FractionRing R)) := by
    unfold torusS
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨m, -, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra,
      fldF_findim_pf_tpow]
    exact prod_mem fun k _ => zpow_mem
      (IntermediateField.subset_adjoin K (Set.range fun k => algebraMap R (FractionRing R) (t k : R)) ⟨k, rfl⟩ :
        algebraMap R (FractionRing R) (t k : R) ∈ fldF K t) _
  have := hle hr
  rwa [Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra] at this

theorem fldF_findim_pf (t : Fin (n + 1) → Rˣ) (Bu : Subalgebra K R) (hTB : torusS K t Finset.univ ≤ Bu) (hFG : Bu.FG)
    (hInt : ∀ b ∈ Bu, IsIntegral (torusS K t Finset.univ) b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b) :
    FiniteDimensional (fldF K t) (FractionRing R) := by
  classical
  obtain ⟨s, hs⟩ := hFG

  let ψ : torusS K t Finset.univ →+* fldF K t :=
    ((algebraMap R (FractionRing R)).comp (torusS K t Finset.univ).val.toRingHom).codRestrict (fldF K t)
      (fun x => fldF_findim_pf_mem t x x.2)
  have hcomp : (algebraMap (fldF K t) (FractionRing R)).comp ψ =
      (algebraMap R (FractionRing R)).comp (algebraMap (torusS K t Finset.univ) R) := by
    ext x
    rfl

  have hint : ∀ x ∈ (s : Set R), IsIntegral (fldF K t) (algebraMap R (FractionRing R) x) := fun x hx =>
    IsIntegral.map_of_comp_eq ψ (algebraMap R (FractionRing R)) hcomp
      (hInt x (hs ▸ Algebra.subset_adjoin hx))
  let E := IntermediateField.adjoin (fldF K t) (algebraMap R (FractionRing R) '' (s : Set R))
  have : Finite (algebraMap R (FractionRing R) '' (s : Set R)) := (s.finite_toSet.image _).to_subtype
  have hE : FiniteDimensional (fldF K t) E := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, hx, rfl⟩
    exact hint x hx)

  have hBu : Bu ≤ ((E.restrictScalars K).toSubalgebra).comap (IsScalarTower.toAlgHom K R (FractionRing R)) := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra,
      IntermediateField.mem_restrictScalars]
    exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
  have hmemB : ∀ b ∈ Bu, algebraMap R (FractionRing R) b ∈ E := fun b hb => by
    have := hBu hb
    rwa [Subalgebra.mem_comap, IsScalarTower.coe_toAlgHom', IntermediateField.mem_toSubalgebra,
      IntermediateField.mem_restrictScalars] at this

  have hmemR : ∀ r : R, algebraMap R (FractionRing R) r ∈ E := fun r => by
    obtain ⟨b, hb, b', hb', hb0, hrb⟩ := hFrac r
    have hne : algebraMap R (FractionRing R) b' ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb0
    have heq : algebraMap R (FractionRing R) r = algebraMap R (FractionRing R) b / algebraMap R (FractionRing R) b' :=
      eq_div_of_mul_eq hne (by rw [← map_mul, hrb])
    rw [heq]
    exact div_mem (hmemB b hb) (hmemB b' hb')
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨r, r', -, rfl⟩ := IsFractionRing.div_surjective (A := R) y
    exact div_mem (hmemR r) (hmemR r')
  have e : E ≃ₗ[fldF K t] FractionRing R :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv
  exact e.finiteDimensional

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

theorem frac_deriv (D : Derivation K R R) :
    ∃ D' : Derivation K (FractionRing R) (FractionRing R),
      ∀ r, D' (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (D r) := by
  let φ : R →+* TrivSqZeroExt (FractionRing R) (FractionRing R) :=
    { toFun := fun r => TrivSqZeroExt.inl (algebraMap R (FractionRing R) r) +
        TrivSqZeroExt.inr (algebraMap R (FractionRing R) (D r))
      map_one' := by ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp [-DualNumber.inr_eq_smul_eps] }
  have hu : ∀ s : nonZeroDivisors R, IsUnit (φ s) := fun s =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
      simpa [φ] using IsLocalization.map_units (FractionRing R) s)
  let Λ : FractionRing R →+* TrivSqZeroExt (FractionRing R) (FractionRing R) := IsLocalization.lift hu
  have hΛ : ∀ r, Λ (algebraMap R (FractionRing R) r) = φ r := fun r => IsLocalization.lift_eq hu r
  have hfst : ∀ x, (Λ x).fst = x := fun x => by
    have : (TrivSqZeroExt.fstHom (FractionRing R) (FractionRing R) (FractionRing R)).toRingHom.comp Λ =
        RingHom.id _ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
      simp [hΛ, φ]
    exact congr($this x)
  have hsnd : ∀ r, (Λ (algebraMap R (FractionRing R) r)).snd = algebraMap R (FractionRing R) (D r) := fun r => by
    rw [hΛ]
    simp [φ, -DualNumber.inr_eq_smul_eps]
  have hmul : ∀ x y, (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd := fun x y => by
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  have hK : ∀ c : K, (Λ (algebraMap K (FractionRing R) c)).snd = 0 := fun c => by
    rw [IsScalarTower.algebraMap_apply K R (FractionRing R), hsnd, D.map_algebraMap, map_zero]
  let e : FractionRing R →ₗ[K] FractionRing R :=
    { toFun := fun x => (Λ x).snd
      map_add' := fun x y => by rw [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, Algebra.smul_def, hmul, hK, smul_zero, add_zero, algebraMap_smul] }
  exact ⟨Derivation.mk' e fun x y => hmul x y, fun r => hsnd r⟩

theorem fldF_findim (t : Fin (n + 1) → Rˣ) (Bu : Subalgebra K R) (hTB : torusS K t Finset.univ ≤ Bu) (hFG : Bu.FG)
    (hInt : ∀ b ∈ Bu, IsIntegral (torusS K t Finset.univ) b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b) :
    FiniteDimensional (fldF K t) (FractionRing R) :=
  fldF_findim_pf t Bu hTB hFG hInt hFrac

theorem torus_mem_fldF (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) :
    ∀ r ∈ torusS K t S, algebraMap R (FractionRing R) r ∈ fldF K t := fun r hr =>
  fldF_findim_pf_mem t r (torusS_le_univ t S hr)

theorem trace_deriv [CharZero K] (t : Fin (n + 1) → Rˣ) [FiniteDimensional (fldF K t) (FractionRing R)] (D : Derivation K R R)
    (hD : ∀ j, D (t j : R) ∈ Set.range (algebraMap K R)) (y b : R) (hb : b ∈ torusS K t Finset.univ)
    (hy : algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) y)) = algebraMap R (FractionRing R) b) :
    algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) (D y))) =
        algebraMap R (FractionRing R) (D b) := by
  obtain ⟨Dl, hDl⟩ := frac_deriv D

  have hF : ∀ x ∈ fldF K t, Dl x ∈ fldF K t := fun x hx => by
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hD j
      rw [hDl, ← hc, ← IsScalarTower.algebraMap_apply]
      exact IntermediateField.algebraMap_mem _ c
    | algebraMap c =>
      rw [Derivation.map_algebraMap]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | inv x hx0 hx =>
      rw [Derivation.leibniz_inv, smul_eq_mul]
      exact mul_mem (neg_mem (pow_mem (inv_mem hx0) 2)) hx
    | mul x y hx0 hy0 hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (mul_mem hx0 hy) (mul_mem hy0 hx)
  let e : fldF K t →ₗ[K] fldF K t :=
    { toFun := fun x => ⟨Dl (x : FractionRing R), hF _ x.2⟩
      map_add' := fun x y => Subtype.ext (map_add Dl (x : FractionRing R) y)
      map_smul' := fun c x => Subtype.ext (Dl.map_smul c (x : FractionRing R)) }
  let D0 : Derivation K (fldF K t) (fldF K t) :=
    Derivation.mk' e fun x y => Subtype.ext (by
      change Dl ((x : FractionRing R) * y) = (x : FractionRing R) * Dl (y : FractionRing R) +
        (y : FractionRing R) * Dl (x : FractionRing R)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul])
  have hD0 : ∀ x : fldF K t, Dl (algebraMap (fldF K t) (FractionRing R) x) =
      algebraMap (fldF K t) (FractionRing R) (D0 x) := fun _ => rfl
  have key := GlobalTheory.T.derivation_commutes_with_trace K (fldF K t) (FractionRing R) Dl D0 hD0 (algebraMap R (FractionRing R) y)
  rw [← hDl, ← key, ← hD0, hy, hDl]

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] [CharZero K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}

theorem trace_chart (t : Fin (n + 1) → Rˣ) (S : Finset (Fin (n + 2))) (u : Fin (n + 1) → torusS K t S)
    (hinj : Function.Injective (MvPolynomial.aeval u : MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t S))
    (hloc : ∀ a : torusS K t S, ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval u g) ∧ a * MvPolynomial.aeval u g = MvPolynomial.aeval u f)
    (hfr : ∀ k, ∃ a' ∈ torusS K t S, a' ≠ 0 ∧ (t k : R) * a' ∈ torusS K t S)
    (B' : Subalgebra K R) (hTB : torusS K t S ≤ B') (hFG : B'.FG) (hInt : ∀ b ∈ B', IsIntegral (torusS K t S) b)
    (hFrac : ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b)
    (E : Fin (n + 1) → Derivation K R R) (hE : ∀ k j, E k (u j : R) = if k = j then 1 else 0)
    {m : ℕ} (κ : Fin m → Fin (n + 1)) (hκ : Function.Injective κ) :
    ∀ y ∈ jacS B' E κ, ∃ a ∈ torusS K t S,
      algebraMap (fldF K t) (FractionRing R)
        (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) y)) =
          algebraMap R (FractionRing R) a := by
  classical

  have hι : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)
  have hιne : ∀ r : R, r ≠ 0 → algebraMap R (FractionRing R) r ≠ 0 := fun r hr h =>
    hr (hι (h.trans (map_zero _).symm))

  letI : Algebra (torusS K t S) B' := (Subalgebra.inclusion hTB).toRingHom.toAlgebra
  haveI : IsScalarTower K (torusS K t S) B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hAB : Function.Injective (algebraMap (torusS K t S) B') := Subalgebra.inclusion_injective hTB
  let f : B' →ₐ[torusS K t S] R := { B'.val with commutes' := fun _ => rfl }
  haveI : Algebra.IsIntegral (torusS K t S) B' :=
    ⟨fun b => (isIntegral_algHom_iff f Subtype.val_injective).mp (hInt b b.2)⟩
  haveI : Algebra.FiniteType K B' := Subalgebra.fg_iff_finiteType B' |>.mp hFG
  haveI : Algebra.FiniteType (torusS K t S) B' := Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  haveI : Module.Finite (torusS K t S) B' := Algebra.IsIntegral.finite

  let ψ : torusS K t S →+* fldF K t :=
    { toFun := fun a => ⟨algebraMap R (FractionRing R) a, torus_mem_fldF t S a a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ (a : R) b)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ (a : R) b) }
  letI : Algebra (torusS K t S) (fldF K t) := ψ.toAlgebra
  have hψ : ∀ a : torusS K t S, ((algebraMap (torusS K t S) (fldF K t) a : fldF K t) : FractionRing R) =
      algebraMap R (FractionRing R) a := fun _ => rfl
  have hψinj : Function.Injective (algebraMap (torusS K t S) (fldF K t)) := fun a b h =>
    Subtype.ext (hι (by rw [← hψ, ← hψ, h]))

  have hQ : ∀ z ∈ fldF K t, ∃ x y : torusS K t S, algebraMap R (FractionRing R) (y : R) ≠ 0 ∧
      z = algebraMap R (FractionRing R) x / algebraMap R (FractionRing R) y := fun z hz => by
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      obtain ⟨a', ha', ha'0, hta⟩ := hfr k
      refine ⟨⟨_, hta⟩, ⟨a', ha'⟩, hιne _ ha'0, ?_⟩
      simp only [map_mul]
      rw [mul_div_assoc, div_self (hιne _ ha'0), mul_one]
    | algebraMap c =>
      refine ⟨algebraMap K _ c, 1, by simpa using one_ne_zero, ?_⟩
      simp [IsScalarTower.algebraMap_apply K R (FractionRing R)]
    | add x y _ _ hx hy =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      obtain ⟨y1, y2, hy2, rfl⟩ := hy
      refine ⟨x1 * y2 + y1 * x2, x2 * y2, by simpa using mul_ne_zero hx2 hy2, ?_⟩
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul, map_add (f := _), map_mul]
      rw [div_add_div _ _ hx2 hy2]
      ring
    | inv x _ hx =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      by_cases h1 : algebraMap R (FractionRing R) (x1 : R) = 0
      · exact ⟨0, 1, by simpa using one_ne_zero, by simp [h1]⟩
      · exact ⟨x2, x1, h1, by rw [inv_div]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨x1, x2, hx2, rfl⟩ := hx
      obtain ⟨y1, y2, hy2, rfl⟩ := hy
      refine ⟨x1 * y1, x2 * y2, by simpa using mul_ne_zero hx2 hy2, ?_⟩
      simp only [Subalgebra.coe_mul, map_mul]
      rw [div_mul_div_comm]
  haveI : FaithfulSMul (torusS K t S) (fldF K t) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hψinj
  haveI : IsFractionRing (torusS K t S) (fldF K t) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, y, hy, hz⟩ := hQ z z.2
    refine ⟨x, y, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div, hψ, hψ, ← hz]

  have hBL : Function.Injective (algebraMap B' (FractionRing R)) := fun a b h => Subtype.ext (hι h)
  haveI : FaithfulSMul B' (FractionRing R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  haveI : IsFractionRing B' (FractionRing R) := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    obtain ⟨b1, hb1, b1', hb1', hb1'0, hr⟩ := hFrac r
    obtain ⟨b2, hb2, b2', hb2', hb2'0, hs'⟩ := hFrac s
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hb20 : b2 ≠ 0 := by rw [← hs']; exact mul_ne_zero hs0 hb2'0
    refine ⟨⟨b1 * b2', mul_mem hb1 hb2'⟩, ⟨b1' * b2, mul_mem hb1' hb2⟩, ?_⟩
    change _ = algebraMap R (FractionRing R) (b1 * b2') / algebraMap R (FractionRing R) (b1' * b2)
    have hden : algebraMap R (FractionRing R) (b1' * b2) ≠ 0 := hιne _ (mul_ne_zero hb1'0 hb20)
    rw [div_eq_div_iff (hιne _ hs0) hden, ← map_mul, ← map_mul, ← hr, ← hs']
    congr 1
    ring
  haveI : IsScalarTower (torusS K t S) (fldF K t) (FractionRing R) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (torusS K t S) B' (FractionRing R) := IsScalarTower.of_algebraMap_eq fun _ => rfl

  choose Dl hDl using fun k => frac_deriv (E k)
  have hDu : ∀ k j, Dl k (algebraMap (torusS K t S) (FractionRing R) (u j)) = if k = j then 1 else 0 := by
    intro k j
    change Dl k (algebraMap R (FractionRing R) (u j : R)) = _
    rw [hDl, hE]
    split_ifs <;> simp
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, bs, rfl⟩ := hy
    obtain ⟨a, ha⟩ := GlobalTheory.T.fraction_field_transcendence_basis_ext K (n + 1) (torusS K t S) u hinj hloc B' hAB (fldF K t) (FractionRing R)
      Dl hDu m ⟨κ, hκ⟩ b bs
    refine ⟨a, a.2, ?_⟩
    have hX : algebraMap R (FractionRing R) ((b : R) * (Matrix.of fun k l => E (κ k) (bs l : R)).det) =
        algebraMap B' (FractionRing R) b *
          (Matrix.of fun k l => Dl ((⟨κ, hκ⟩ : Fin m ↪ Fin (n + 1)) k) (algebraMap B' (FractionRing R) (bs l))).det := by
      rw [map_mul, RingHom.map_det]
      refine congrArg₂ (· * ·) rfl (congrArg Matrix.det ?_)
      ext k l
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      rw [← hDl]
      rfl
    rw [← hψ, ha, hX]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hyb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by simp only [map_add (f := _)] at hxa hyb ⊢; rw [hxa, hyb]⟩
  | neg x _ hx =>
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨-a, neg_mem ha, by simp only [map_neg] at hxa ⊢; rw [hxa]⟩

end CrystallineSemistableComparison.Pb
