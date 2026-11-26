module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerReductionCongruence
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCoker
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCoker
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_smul_eq_zero_of_isFiniteLength {R : Type} [CommRing R] (r : R)
    (hr : ∀ b : R, IsUnit (1 - b * r)) (M : Type) [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ n : ℕ, ∀ m : M, r ^ n • m = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun m => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    have hS : ∀ q : M ⧸ N, r • q = 0 := by
      intro q
      by_contra hq
      have htop : (R ∙ (r • q)) = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by rwa [Submodule.span_singleton_eq_bot])
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : q ∈ R ∙ (r • q))
      have h1 : (1 - b * r) • q = 0 := by rw [sub_smul, one_smul, mul_smul, hb, sub_self]
      have h2 : q = 0 := (hr b).smul_eq_zero.1 h1
      exact hq (by rw [h2, smul_zero])
    refine ⟨n + 1, fun m => ?_⟩
    have hm : r • m ∈ N := by
      have := hS (N.mkQ m)
      rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have := hn ⟨_, hm⟩
    rw [pow_succ, mul_smul]
    simpa using congrArg Subtype.val this

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem isUnit_one_sub_mul_l (b : A O K) : IsUnit (1 - b * (l : A O K)) := by
  set f : A O K := 1 - b * (l : A O K)
  set g := (equivA O K).symm f
  have hg : equivA O K g = f := AlgEquiv.apply_symm_apply _ _
  suffices IsUnit g by simpa [hg] using this.map (equivA O K)
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h0 : algebraMap O K (constantCoeff g) = 1 - constantCoeff (b : K⟦X⟧) * l := by
    calc algebraMap O K (constantCoeff g) = constantCoeff ((equivA O K g : A O K) : K⟦X⟧) := by
          rw [coe_equivA, ← coeff_zero_eq_constantCoeff_apply (map _ g), coeff_map,
            coeff_zero_eq_constantCoeff_apply]
      _ = 1 - constantCoeff (b : K⟦X⟧) * l := by
          rw [hg]
          simp only [f, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul,
            map_sub, map_one, map_mul]
          congr 2
  have hlt : ‖constantCoeff (b : K⟦X⟧) * (l : K)‖ < 1 := by
    rw [norm_mul]
    have hb : ‖constantCoeff (b : K⟦X⟧)‖ ≤ 1 := by
      simpa using (mem_A.1 b.2) 0
    calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_l_lt_one (K := K) l
  have hn : ‖algebraMap O K (constantCoeff g)‖ = 1 := by
    rw [h0, sub_eq_add_neg, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlt.ne), norm_neg, norm_one, max_eq_right hlt.le]
  have hne : algebraMap O K (constantCoeff g) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (algebraMap O K (constantCoeff g))⁻¹).2
    (by rw [norm_inv, hn, inv_one])
  refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (K := K) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ hne, map_one]

theorem exists_l_pow_smul_eq_app_of_isFiniteLength_coker (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ]
    [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ)
    (G : GlobalTheory.BK.Hom Q T) :
    IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCokerStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_smul_mem_range_of_finiteLength_coker : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (G : GlobalTheory.BK.Hom Q T), IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  first | exact @GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker | exact GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker | (intros; apply GlobalTheory.BK.exists_l_pow_smul_eq_app_of_isFiniteLength_coker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnity
open ReciprocityTheory.Gal

open Polynomial IntermediateField

namespace GlobalTheory.ShapeNeg

theorem natDegree_minpoly_le_mul {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) (x : PadicAlgCl p) (hx : IsIntegral K x) :
    (minpoly ℚ_[p] x).natDegree ≤ (minpoly K x).natDegree * Module.finrank ℚ_[p] K := by
  set E := K⟮x⟯
  haveI : FiniteDimensional K E := adjoin.finiteDimensional hx
  haveI : FiniteDimensional ℚ_[p] E := Module.Finite.trans K E
  have h1 : Module.finrank ℚ_[p] K * Module.finrank K E = Module.finrank ℚ_[p] E :=
    Module.finrank_mul_finrank ℚ_[p] K E
  rw [adjoin.finrank hx] at h1
  have hxE : x ∈ E := mem_adjoin_simple_self K x
  haveI : IsScalarTower ℚ_[p] E (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have h2 : minpoly ℚ_[p] (⟨x, hxE⟩ : E) = minpoly ℚ_[p] x :=
    (minpoly.algebraMap_eq (algebraMap E (PadicAlgCl p)).injective (⟨x, hxE⟩ : E)).symm
  have h3 := minpoly.natDegree_le (A := ℚ_[p]) (⟨x, hxE⟩ : E)
  rw [h2] at h3
  rw [mul_comm]
  omega

theorem natDegree_minpoly_le_card_pow_eq_one {p : ℕ} [Fact p.Prime]
    {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {N : ℕ} [NeZero N] {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ) :
    (minpoly K ζ).natDegree ≤ Nat.card {x : ZMod N // x ^ k = 1} := by
  classical
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos N)).tower_top
  have hirr : Irreducible (minpoly K ζ) := minpoly.irreducible hint
  have hsep : (minpoly K ζ).Separable := hirr.separable
  have hspl : Splits ((minpoly K ζ).map (algebraMap K (PadicAlgCl p))) := IsAlgClosed.splits _
  rw [← card_rootSet_eq_natDegree hsep hspl, ← Nat.card_eq_fintype_card]
  have hχ : ∀ σ : Formalism.GaloisCohomology.GK p K, ((hζ.autToPow K σ : ZMod N)) ^ k = 1 := by
    intro σ
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    have h1 := hζ.autToPow_spec K (σ ^ k)
    rw [hfix σ] at h1
    have h0 : ζ ^ (1 % N) = ζ := by rw [hζ.eq_orderOf, pow_mod_orderOf, pow_one]
    have h2 : ζ ^ (hζ.autToPow K (σ ^ k) : ZMod N).val = ζ ^ (1 % N) := h1.trans h0.symm
    have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos N)) h2
    rw [← ZMod.val_one_eq_one_mod] at h3
    exact ZMod.val_injective N h3
  have horb : ∀ y : (minpoly K ζ).rootSet (PadicAlgCl p), ∃ σ : Formalism.GaloisCohomology.GK p K, σ ζ = y := by
    intro y
    have hy : aeval (y : PadicAlgCl p) (minpoly K ζ) = 0 :=
      (mem_rootSet.1 y.2).2
    have he : minpoly K ζ = minpoly K (y : PadicAlgCl p) :=
      minpoly.eq_of_irreducible_of_monic hirr hy (minpoly.monic hint)
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (PadicAlgCl p)).1 he.symm
    exact ⟨σ, hσ⟩
  choose σ hσ using horb
  refine Nat.card_le_card_of_injective (fun y => ⟨(hζ.autToPow K (σ y) : ZMod N), hχ (σ y)⟩) ?_
  intro y y' hyy
  have h : (hζ.autToPow K (σ y) : ZMod N) = (hζ.autToPow K (σ y') : ZMod N) :=
    congrArg Subtype.val hyy
  have h' : (σ y) ζ = (σ y') ζ := by
    rw [← hζ.autToPow_spec K (σ y), ← hζ.autToPow_spec K (σ y'), h]
  exact Subtype.ext (by rw [← hσ y, ← hσ y']; exact h')

theorem exists_pow_ne_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  intro p _ K hK k hk
  by_contra hcon
  push_neg at hcon
  have hp : p.Prime := Fact.out
  set d := Module.finrank ℚ_[p] K with hd
  obtain ⟨n, hn⟩ : ∃ n, 2 * k * d < p ^ n := ⟨2 * k * d, Nat.lt_pow_self hp.one_lt⟩
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero ((p ^ (n + 1) : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ (n + 1))
  have hfix : ∀ σ : Formalism.GaloisCohomology.GK p K, (σ ^ k) ζ = ζ := fun σ => hcon σ (n + 1) ζ hζ.pow_eq_one
  have hB := natDegree_minpoly_le_card_pow_eq_one hζ k hfix
  have hC : Nat.card {x : ZMod (p ^ (n + 1)) // x ^ k = 1} ≤ 2 * k := by
    by_cases h2 : p = 2
    · subst h2
      exact GlobalTheory.card_pow_eq_one_two_pow_le (n + 1) (by omega) hk
    · haveI : IsCyclic (ZMod (p ^ (n + 1)))ˣ := ZMod.isCyclic_units_of_prime_pow p hp h2 (n + 1)
      have := GlobalTheory.card_pow_eq_one_le_of_isCyclic_units (p ^ (n + 1)) hk
      omega
  have hint : IsIntegral K ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  have hA := natDegree_minpoly_le_mul hK ζ hint
  have hcyc : cyclotomic (p ^ (n + 1)) ℚ_[p] = minpoly ℚ_[p] ζ := by
    refine minpoly.eq_of_irreducible_of_monic (GlobalTheory.Cyc.Model.cyc_irred n) ?_ (cyclotomic.monic _ _)
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic (NeZero.pos _)
  rw [← hcyc, natDegree_cyclotomic, Nat.totient_prime_pow_succ hp] at hA
  rw [← hd] at hA
  have hp1 : 1 ≤ p - 1 := by have := hp.two_le; omega
  have h1 : p ^ n ≤ p ^ n * (p - 1) := Nat.le_mul_of_pos_right _ hp1
  have h2 : (minpoly K ζ).natDegree * d ≤ 2 * k * d := Nat.mul_le_mul_right _ (hB.trans hC)
  omega

end GlobalTheory.ShapeNeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPowMovesPadicRootOfUnityStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_pow_moves_padic_rootOfUnity : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ k : ℕ, 0 < k → ∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ := by
  first | exact @GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | exact GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity | (intros; apply GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMemCyclotomicLayerPrimeRpow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMemCyclotomicLayerPrimeRpow
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem norm_aeval_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : ∃ n : ℤ, ‖aeval π p‖ = (l : ℝ) ^ ((n : ℝ) / (N : ℝ)) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.UnramValue.norm_of_mem_unramified_subfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = aeval π p := by
    rw [aeval_eq_sum_range' (Nat.lt_succ_self _)]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs] at h6
  obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_eq_sup p.support (support_nonempty.2 hp)
    (fun i => ‖p.coeff i • π ^ i‖₊)
  obtain ⟨n, hn⟩ := key i hi
  refine ⟨n * N - i, ?_⟩
  have h7 : ‖aeval π p‖ = ‖p.coeff i • π ^ i‖ := congrArg NNReal.toReal (h6.trans hi')
  rw [h7, hn]
  congr 1
  push_cast
  field_simp

theorem norm_of_mem_Ks : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j →
    ∀ x : Om l, x ∈ Ks K j → x ≠ 0 →
      ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  intro l _ K j hj x hx hx0
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ, IntermediateField.mem_restrictScalars] at hx
  have hx' : x ∈ Algebra.adjoin ↥(K0 K) {ζ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx'
  obtain ⟨q, hq⟩ := hx'
  have hcast : ((Nat.totient (l ^ j) : ℕ) : ℝ) = (l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) := by
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rfl
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := norm_primitiveRoot_sub_one l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [hcast, ← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  set r := q %ₘ minpoly ↥(K0 K) ζ with hr
  have hrx : aeval ζ r = x := by
    rw [hr, aeval_modByMonic_eq_self_of_root (minpoly.aeval _ _)]
    exact hq
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, map_zero] at hrx
    exact hx0 hrx.symm
  have hdeg : r.natDegree < Nat.totient (l ^ j) := by
    have := natDegree_lt_natDegree hr0 (degree_modByMonic_lt q (minpoly.monic hint))
    rwa [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, natDegree_cyclotomic] at this
  obtain ⟨n, hn⟩ := norm_aeval_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 r)
    (fun h => hr0 (taylor_injective 1 (by rw [h, map_zero]))) (by rwa [natDegree_taylor])
  refine ⟨n, ?_⟩
  rw [← hcast, ← hn, ← hrx, taylor_apply, aeval_comp]
  simp

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMemCyclotomicLayerPrimeRpowStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_mem_cyclotomic_layer_prime_rpow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j → ∀ x : Om l, x ∈ Ks K j → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_of_mem_Ks | exact GlobalTheory.Cyc.norm_of_mem_Ks | (intros; apply GlobalTheory.Cyc.norm_of_mem_Ks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLeftInverseOfPhiModuleExactTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLeftInverseOfPhiModuleExactTriple
open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.BK.IntegralLeftInverseExactTriple

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem mem_M_single (P : PhiMod O K l e a ι) (τ : ZMod a) (u : ι → K⟦X⟧)
    (hu : ∀ i, u i ∈ A O K) : (Pi.single τ u : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun σ => mem_vecs.2 fun i => ?_
  by_cases h : σ = τ
  · subst h; simpa using hu i
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem app_single {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} (F : Hom P Q) (τ : ZMod a)
    (u : ι → K⟦X⟧) : F.app (Pi.single τ u) = Pi.single τ (F.mat τ *ᵥ u) := by
  funext σ
  rw [Hom.app_apply]
  by_cases h : σ = τ
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem smul_one_mem (ν : Type) [Fintype ν] [DecidableEq ν] (n : ℕ) (i j : ν) :
    (((l : K) ^ n) • (1 : Matrix ν ν K⟦X⟧)) i j ∈ A O K := by
  rw [Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · rw [show ((l : K) ^ n) • (1 : K⟦X⟧) = ((l ^ n : ℕ) : K⟦X⟧) by simp [Algebra.smul_def]]
    exact natCast_mem _ _
  · rw [smul_zero]; exact zero_mem _

end GlobalTheory.BK.IntegralLeftInverseExactTriple

namespace GlobalTheory.BK


open IntegralLeftInverseExactTriple in
theorem exists_integral_leftInverse_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : GlobalTheory.BK.Hom P Q) (G : GlobalTheory.BK.Hom Q T), IsExactTriple F G → ∀ n : ℕ, (∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) → ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧) := by
  intro O K _ _ _ _ _ _ l e a _ _ _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG n hG τ
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  have hGF : G.mat τ * F.mat τ = 0 := by
    refine Matrix.ext fun i j => ?_
    have hs := mem_M_single P τ (Pi.single j 1) fun i' => by
      by_cases h : i' = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 := (hFG.exact _ (F.app_mem_M hs)).2 ⟨_, hs, rfl⟩
    have := congrFun (congrFun h0 τ) i
    rw [app_single, app_single, Pi.single_eq_same, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
      at this
    simpa using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, hWA, ?_⟩
  have hFWF : F.mat τ * (W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hFW]
    simp only [Z, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, hGF,
      Matrix.mul_zero, sub_zero, Matrix.mul_smul, Matrix.mul_one, sub_self]
  rw [← sub_eq_zero]
  refine Matrix.ext fun i j => ?_
  set D := W * F.mat τ - ((l : K) ^ n) • (1 : Matrix ι ι K⟦X⟧) with hD
  have hDm : Pi.single τ (fun i' => D i' j) ∈ P.M := mem_M_single P τ _ fun i' =>
    sub_mem (Subalgebra.sum_mem _ fun k _ => mul_mem (hWA i' k) (F.mem _ _ _)) (smul_one_mem ι n i' j)
  have hFD : F.mat τ *ᵥ (fun i' => D i' j) = 0 := by
    funext k
    have := congrFun (congrFun hFWF k) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have h0 := hFG.inj _ hDm (by rw [app_single, hFD, Pi.single_zero])
  have := congrFun (congrFun h0 τ) i
  simpa using this

end GlobalTheory.BK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLeftInverseOfPhiModuleExactTripleStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_leftInverse_of_phiModule_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : GlobalTheory.BK.Hom P Q) (G : GlobalTheory.BK.Hom Q T), IsExactTriple F G → ∀ n : ℕ, (∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) → ∀ τ : ZMod a, ∃ Λ : Matrix ι κ K⟦X⟧, (∀ i k, Λ i k ∈ A O K) ∧ Λ * F.mat τ = (l : K) ^ n • (1 : Matrix ι ι K⟦X⟧) := by
  first | exact @GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple | exact GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple | (intros; apply GlobalTheory.BK.exists_integral_leftInverse_of_exactTriple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwist
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.CyclotomicH2Bound

open GlobalTheory.ShapeNeg

theorem cycK_eq_of_prim {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (n : ℕ)
    (g : Formalism.GaloisCohomology.GK p K) {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) (a : ℕ)
    (ha : g ζ = ζ ^ a) : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = (a : ZMod (p ^ n)) := by
  have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
    (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ hζ.pow_eq_one
  have h1 : (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) ζ = g ζ := rfl
  rw [h1, ha] at hsp
  have h3 : ((Formalism.GaloisCohomology.cycK p K n g : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) =
      (PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]) := rfl
  rw [h3]
  set b := ((PadicInt.toZModPow n) ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g)) : ℤ_[p]))
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
  have hz : ζ ^ ((a : ℤ) - (b.val : ℤ)) = 1 := by
    rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
  have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
  have h0 : (((a : ℤ) - (b.val : ℤ) : ℤ) : ZMod (p ^ n)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hd
  push_cast at h0
  rw [ZMod.natCast_zmod_val] at h0
  exact (sub_eq_zero.1 h0).symm

theorem exists_prim (p : ℕ) [Fact p.Prime] (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
  HasEnoughRootsOfUnity.exists_primitiveRoot _ _

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem finite_quot [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ) (k : ℕ) :
    Finite (O ⧸ Ideal.span {ϖ ^ k}) := by
  have hI : Ideal.span {ϖ} = IsLocalRing.maximalIdeal O :=
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ).symm
  haveI : Finite (O ⧸ Ideal.span {ϖ}) := by
    rw [hI]; exact (inferInstance : Finite (IsLocalRing.ResidueField O))
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) k

theorem lev_cyclic {M : Type} [AddCommGroup M] [Module O M] (eM : M ≃ₗ[O] Formalism.NG.KO O)
    {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    ∃ x₀ : Lev M (ϖ ^ n), ∀ y : Lev M (ϖ ^ n), ∃ t : O, y = t • x₀ := by
  have hϖ0 : (algebraMap O (FractionRing O) ϖ) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hϖ.ne_zero
  let z₀ : FractionRing O := (algebraMap O (FractionRing O) ϖ ^ n)⁻¹
  have hk : (ϖ ^ n) • eM.symm (Submodule.Quotient.mk z₀) = 0 := by
    rw [← map_smul, ← Submodule.Quotient.mk_smul, Algebra.smul_def, map_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hϖ0)]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.one_le.1 le_rfl), map_zero]
  refine ⟨Lev.mk _ hk, fun y => ?_⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (eM y.val)
  have hy := y.smul_val
  have hm : (ϖ ^ n) • (Submodule.Quotient.mk z : Formalism.NG.KO O) = 0 := by
    rw [hz, ← map_smul, hy, map_zero]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at hm
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, Lev.ext ?_⟩
  rw [Lev.val_smul, Lev.val_mk, ← eM.symm_apply_apply y.val, ← hz, ← map_smul,
    ← Submodule.Quotient.mk_smul]
  congr 2
  rw [Algebra.smul_def, ht, Algebra.smul_def, map_pow, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hϖ0), one_mul]

theorem td_nsmul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M) (k : ℕ)
    (y : M) : φ (k • y) = k • φ y := map_nsmul (show M →ₗ[R] R from φ) k y
theorem td_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x - y) = φ x - φ y := (show M →ₗ[R] R from φ).map_sub x y
theorem td_add {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (φ : TDual R M)
    (x y : M) : φ (x + y) = φ x + φ y := (show M →ₗ[R] R from φ).map_add x y

theorem out_smul {N : Type} [AddCommGroup N] [Module O N] {ϖ : O} (k : ℕ) {z : N}
    (hz : (ϖ ^ k) • z = 0) (t : O) : (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out • z = t • z := by
  have h1 : Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t).out =
      Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) t := Ideal.Quotient.mk_out _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h1)
  rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hz, smul_zero]

theorem h2_bounded_cyclotomic : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hLTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ ε hε e M _ _ eM ρ hρ σ₀ hσ hcont
  have hw : ((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1 ≠ 0 := by
    intro h0; apply hσ; ext; rw [Units.val_one]; exact sub_eq_zero.1 h0
  obtain ⟨c, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hpϖ
  haveI hQ := finite_quot hϖ c
  refine ⟨(p ^ c) ^ ((p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hkn : ∀ y : Lev M (ϖ ^ n), (ϖ ^ n) • y = 0 := fun y => Lev.ext (by
    rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  haveI : Finite (Lev M (ϖ ^ n)) := by
    haveI := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) (fun y => ?_)
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n (hkn x₀) t⟩
  obtain ⟨⟨eB⟩, -, -, -, hcup, -⟩ := hLTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)
  have hpn : ∀ y : Lev M (ϖ ^ n), ((p : O) ^ n) • y = 0 := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hr, mul_smul, hkn, smul_zero]
  obtain ⟨ζ, hζ⟩ := exists_prim p n
  obtain ⟨a₀, ha₀, hdiff⟩ := hε σ₀ n ζ hζ.pow_eq_one
  have hcyc := cycK_eq_of_prim n σ₀ hζ a₀ ha₀
  have hεy : ∀ y : Lev M (ϖ ^ n), ((ε σ₀ : Oˣ) : O) • y = (a₀ : O) • y := by
    intro y; obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hdiff
    rw [← sub_eq_zero, ← sub_smul, ← hr, mul_smul, hpn, smul_zero]
  have hεk : ∀ (k : ℕ) (y : Lev M (ϖ ^ n)), ((ε σ₀ : Oˣ) : O) ^ k • y = (a₀ ^ k : ℕ) • y := by
    intro k; induction k with
    | zero => intro y; simp
    | succ k ih => intro y; rw [pow_succ, mul_smul, hεy, ih, ← Nat.cast_smul_eq_nsmul O (a₀ ^ k),
        ← Nat.cast_smul_eq_nsmul O (a₀ ^ (k + 1)), smul_smul, Nat.cast_pow, Nat.cast_pow, ← pow_succ]
  have hinv : ∀ y : Lev M (ϖ ^ n), levRepZ p n h ρ σ₀⁻¹ y = ((ε σ₀ : Oˣ) : O) ^ e • y := by
    intro y; apply Lev.ext
    rw [levRepZ_apply, levRep_val, hρ, Lev.val_smul, map_inv, inv_pow, inv_inv, Units.val_pow_eq_pow_val]
  let A := H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id _))
  have hfix : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n))) * (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y := by
    intro a y
    have h1 := DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 a.2 σ₀) y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply] at h1
    rw [hinv, hεk, td_nsmul, nsmul_eq_mul, hcyc, ← mul_assoc] at h1
    have h2 : ((a₀ ^ (e + 1) : ℕ) : ZMod (p ^ n)) = (a₀ : ZMod (p ^ n)) * ((a₀ ^ e : ℕ) : ZMod (p ^ n)) := by
      push_cast; ring
    rw [h2]; exact h1
  have hkill : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((ϖ ^ c) • y) = 0 := by
    intro a y
    have hy : (ϖ ^ c) • y = (((ε σ₀ ^ (e + 1) : Oˣ) : O) - 1) • (((u⁻¹ : Oˣ) : O) • y) := by
      rw [hu, smul_smul, mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]
    rw [hy, sub_smul, one_smul, Units.val_pow_eq_pow_val, hεk, td_sub, td_nsmul, nsmul_eq_mul, hfix,
      sub_self]
  have hkillp : ∀ (a : A) (y : Lev M (ϖ ^ n)),
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) ((p ^ c : ℕ) • y) = 0 := by
    intro a y
    have hy : (p ^ c : ℕ) • y = (ϖ ^ c) • ((s ^ c) • y) := by
      rw [← Nat.cast_smul_eq_nsmul O, smul_smul, ← mul_pow, mul_comm ϖ s, hs, Nat.cast_pow]
    rw [hy, hkill]
  have hA : ∀ a : A, (p ^ c : ℕ) • a = 0 := by
    intro a; apply Subtype.ext; apply LinearMap.ext; intro y
    rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), Submodule.coe_smul]
    change ((p ^ c : ℕ) : ZMod (p ^ n)) •
      (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) y = 0
    rw [Nat.cast_smul_eq_nsmul, ← td_nsmul, hkillp]
  let T := {x : ZMod (p ^ n) // (p ^ c) • x = 0}
  have hT : Nat.card T ≤ p ^ c := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsAddCyclic.card_nsmul_eq_zero_le (pow_pos (Fact.out : p.Prime).pos c)
  have hq : ∀ (a : A) (t : O), (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n)))
      ((Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀) =
        (a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (t • x₀) := by
    intro a t
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1
      (Ideal.Quotient.eq.1 (Ideal.Quotient.mk_out (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t)))
    have h1 : (Ideal.Quotient.mk (Ideal.span {ϖ ^ c}) t).out • x₀ = t • x₀ + (ϖ ^ c) • (r • x₀) := by
      rw [smul_smul, mul_comm (ϖ ^ c) r, hr, sub_smul, add_sub_cancel]
    rw [h1, td_add, hkill, add_zero]
  let G : A → (O ⧸ Ideal.span {ϖ ^ c} → T) := fun a q =>
    ⟨(a : TDual (ZMod (p ^ n)) (Lev M (ϖ ^ n))) (q.out • x₀), by rw [← td_nsmul, hkillp]⟩
  have hGinj : Function.Injective G := by
    intro a a' hG; apply Subtype.ext; apply LinearMap.ext; intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    have h1 := congrArg Subtype.val (congrFun hG (Ideal.Quotient.mk _ t))
    simp only [G] at h1
    rwa [hq a t, hq a' t] at h1
  haveI : Finite A := Finite.of_injective G hGinj
  have hAcard : Nat.card A ≤ (p ^ c) ^ Nat.card (O ⧸ Ideal.span {ϖ ^ c}) :=
    (Nat.card_le_card_of_injective G hGinj).trans (by rw [Nat.card_fun]; exact Nat.pow_le_pow_left hT _)
  let F : H2 ((levRepZ p n h ρ).comp (MonoidHom.id _)) → (A → T) := fun f a =>
    ⟨eB (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) f a), by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), ← LinearEquiv.map_smul, ← LinearMap.map_smul,
        Nat.cast_smul_eq_nsmul (ZMod (p ^ n)), hA a, LinearMap.map_zero, LinearEquiv.map_zero]⟩
  have hFinj : Function.Injective F := by
    intro f f' hF; apply hcup; apply LinearMap.ext; intro a; apply eB.injective
    exact congrArg Subtype.val (congrFun hF a)
  show Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id _))) ≤ _
  calc _ ≤ Nat.card (A → T) := Nat.card_le_card_of_injective F hFinj
    _ = Nat.card T ^ Nat.card A := Nat.card_fun
    _ ≤ (p ^ c) ^ Nat.card A := Nat.pow_le_pow_left hT _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos (Fact.out : p.Prime).pos c) hAcard

end GlobalTheory.CyclotomicH2Bound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2BoundedTwistStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h2_bounded_twist : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ (e : ℕ) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M),
    (∀ g m, ρ g m = ((((ε g) ^ e)⁻¹ : Oˣ) : O) • m) → ∀ σ₀ : Formalism.GaloisCohomology.GK p K, ε σ₀ ^ (e + 1) ≠ 1 →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  first | exact @GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | exact GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic | (intros; apply GlobalTheory.CyclotomicH2Bound.h2_bounded_cyclotomic <;> assumption)
end
end
