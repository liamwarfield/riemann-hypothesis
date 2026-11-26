module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.AdeleApproximation.AdeleIntA
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

def IsInt (b : FiniteAdeleRing R K) : Prop := ∀ v, b v ∈ v.adicCompletionIntegers K

private theorem val_R_lemma (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  exact (valuedAdicCompletion_eq_valuation (K := K) v r).trans (by rw [valuation_of_algebraMap])

theorem int_R (v : HeightOneSpectrum R) (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ 1;
      rw [val_R_lemma]; exact v.intValuation_le_one r

theorem val_R (v : HeightOneSpectrum R) (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := val_R_lemma v r

theorem exists_near (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ k : K, y - algebraMap K (v.adicCompletion K) k ∈ v.adicCompletionIntegers K := by
  have hU : IsOpen ((fun z => z - y) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    (Valued.isOpen_valuationSubring _).preimage (continuous_sub_right y)
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (R := R) (K := K) v).exists_mem_open hU
    ⟨y, by simp⟩
  refine ⟨k, ?_⟩
  have hk' : algebraMap K (v.adicCompletion K) k - y ∈ v.adicCompletionIntegers K := hk
  have := neg_mem hk'
  simpa [neg_sub] using this

theorem exists_den_local (v : HeightOneSpectrum R) (y : v.adicCompletion K) :
    ∃ s : R, s ≠ 0 ∧
      algebraMap K (v.adicCompletion K) (algebraMap R K s) * y ∈ v.adicCompletionIntegers K := by
  obtain ⟨b, hb, hyb⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v y;
      exact ⟨b, nonZeroDivisors.ne_zero hb, by rw [mul_comm]; exact hyb⟩

private theorem algK_apply_lemma_2 (v : HeightOneSpectrum R) (k : K) :
    (algebraMap K (FiniteAdeleRing R K) k) v = algebraMap K (v.adicCompletion K) k := by
  rfl

private theorem algR_apply_lemma_3 (v : HeightOneSpectrum R) (r : R) :
    (algebraMap R (FiniteAdeleRing R K) r) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) := by
  rfl

theorem exists_den (b : FiniteAdeleRing R K) :
    ∃ r : R, r ≠ 0 ∧ IsInt (algebraMap R (FiniteAdeleRing R K) r * b) := by
  classical
  have hfin : {v : HeightOneSpectrum R | b v ∉ v.adicCompletionIntegers K}.Finite := by
    exact Filter.eventually_cofinite.mp b.2
  choose s hs0 hs using fun v => exists_den_local (R := R) (K := K) v (b v)
  refine ⟨∏ w ∈ hfin.toFinset, s w, Finset.prod_ne_zero_iff.mpr fun w _ => hs0 w, ?_⟩
  intro v
  rw [show (algebraMap R (FiniteAdeleRing R K) (∏ w ∈ hfin.toFinset, s w) * b) v =
      (algebraMap R (FiniteAdeleRing R K) (∏ w ∈ hfin.toFinset, s w)) v * b v from rfl,
    algR_apply_lemma_3]
  by_cases hvS : v ∈ hfin.toFinset
  · rw [← Finset.prod_erase_mul _ _ hvS, map_mul, map_mul, mul_assoc]
    exact mul_mem (int_R v _) (hs v)
  · have hb : b v ∈ v.adicCompletionIntegers K := by
      by_contra hc
      exact hvS (hfin.mem_toFinset.mpr hc)
    exact mul_mem (int_R v _) hb

theorem exists_approx_local (v : HeightOneSpectrum R) (c : v.adicCompletion K)
    (hc : c ∈ v.adicCompletionIntegers K) (r : R) (hr : r ≠ 0) :
    ∃ a : R, Valued.v (c - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := _root_.Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_local v c hc r hr

theorem exists_approx (c : FiniteAdeleRing R K) (hc : IsInt c) (r : R) (hr : r ≠ 0) :
    ∃ a : R, ∀ v, Valued.v (c v - algebraMap K _ (algebraMap R K a)) ≤ v.intValuation r := by
  classical
  have hT : {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {r}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr)
  choose a0 ha0 using fun v => exists_approx_local v (c v) (hc v) r hr
  obtain ⟨a, ha⟩ := exists_forall_sub_mem_ideal (s := hT.toFinset) (fun v => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {r})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a0 v.1)
  refine ⟨a, fun v => ?_⟩
  by_cases hv : v ∈ hT.toFinset
  · have h1 := ha v hv
    rw [← intValuation_le_pow_iff_mem, ← intValuation_eq_exp_neg_multiplicity v hr] at h1
    have e : c v - algebraMap K (v.adicCompletion K) (algebraMap R K a) =
        (c v - algebraMap K _ (algebraMap R K (a0 v))) - algebraMap K _ (algebraMap R K (a - a0 v)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    refine (Valuation.map_sub _ _ _).trans (max_le (ha0 v) ?_)
    rw [val_R]; exact h1
  · have h1 : v.intValuation r = 1 := by
      rw [intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hv ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    rw [h1]; exact sub_mem (hc v) (int_R v a)

theorem exists_approx_adele (b : FiniteAdeleRing R K) :
    ∃ u : K, IsInt (b - algebraMap K (FiniteAdeleRing R K) u) := by
  obtain ⟨r, hr, hrb⟩ := exists_den b
  obtain ⟨a, ha⟩ := exists_approx _ hrb r hr
  refine ⟨algebraMap R K a / algebraMap R K r, fun v => ?_⟩
  have hrK : algebraMap R K r ≠ 0 := by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)
  have hrv : algebraMap K (v.adicCompletion K) (algebraMap R K r) ≠ 0 := (map_ne_zero _).mpr hrK
  have h0 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hrv
  have hk' : algebraMap R K r * (algebraMap R K a / algebraMap R K r) = algebraMap R K a := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hrK, mul_one]
  have hc : (algebraMap R (FiniteAdeleRing R K) r * b) v =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) * b v := by
    rw [show (algebraMap R (FiniteAdeleRing R K) r * b) v =
        (algebraMap R (FiniteAdeleRing R K) r) v * b v from rfl, algR_apply_lemma_3]
  have hsub : (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v =
      b v - algebraMap K (v.adicCompletion K) (algebraMap R K a / algebraMap R K r) := by
    rw [show (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v =
        b v - (algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v from rfl,
      algK_apply_lemma_2]
  have key : (algebraMap R (FiniteAdeleRing R K) r * b) v -
        algebraMap K (v.adicCompletion K) (algebraMap R K a) =
      algebraMap K (v.adicCompletion K) (algebraMap R K r) *
        (b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v := by
    rw [hc, hsub, mul_sub, ← map_mul (algebraMap K (v.adicCompletion K)), hk']
  have hv := ha v
  rw [key, map_mul, ← val_R_lemma (K := K) v r] at hv
  show Valued.v ((b - algebraMap K (FiniteAdeleRing R K) (algebraMap R K a / algebraMap R K r)) v) ≤ 1
  exact le_of_mul_le_mul_left (by rwa [mul_one]) (zero_lt_iff.mpr h0)

end ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA
end
end

namespace ReciprocityTheory.ChartRestriction.G.SA

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology WithZero Filter

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem small_mem_nhds (v : HeightOneSpectrum R) {s : Set (v.adicCompletion K)}
    (hs : s ∈ 𝓝 (0 : v.adicCompletion K)) :
    ∃ n : ℕ, ∀ x, Valued.v x ≤ exp (-(n : ℤ)) → x ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hg := MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine ⟨(log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1, fun x hx => hγ ?_⟩
  show Valued.v.restrict x < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  refine lt_of_le_of_lt hx ?_
  calc exp (-(((log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).natAbs + 1 : ℕ) : ℤ))
      < exp (log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)) := exp_lt_exp.2 (by omega)
    _ = _ := exp_log hg

theorem nhds_zero_int {N : Set (FiniteAdeleRing R K)} (hN : N ∈ 𝓝 (0 : FiniteAdeleRing R K)) :
    ∃ r : R, r ≠ 0 ∧ ∀ y : FiniteAdeleRing R K,
      (∀ v, Valued.v (y v) ≤ v.intValuation r) → y ∈ N := by
  have hBopen : ∀ v : HeightOneSpectrum R,
      IsOpen ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)) :=
    fun v => Valued.isOpen_valuationSubring _
  let mk : (∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) → FiniteAdeleRing R K :=
    fun y => ⟨fun v => (y v : v.adicCompletion K), Eventually.of_forall fun v => (y v).2⟩
  have hmk : Continuous mk := by
    exact (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
      (A := fun v => ((v.adicCompletionIntegers K : ValuationSubring _) : Set (v.adicCompletion K)))
      (𝓕 := cofinite)).continuous
  have hmk0 : mk 0 = 0 := rfl
  have hpre : mk ⁻¹' N ∈ 𝓝 (0 : ∀ v : HeightOneSpectrum R, v.adicCompletionIntegers K) :=
    hmk.continuousAt.preimage_mem_nhds (by rw [hmk0]; exact hN)
  rw [nhds_pi, mem_pi] at hpre
  obtain ⟨T, hT, t, ht, hsub⟩ := hpre
  have hloc : ∀ v, ∃ n : ℕ, ∀ x : v.adicCompletionIntegers K,
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    have hu0 : u ∈ 𝓝 (0 : v.adicCompletion K) := by simpa using hu
    obtain ⟨n, hn⟩ := small_mem_nhds v hu0
    exact ⟨n, fun x hx => hut (hn _ hx)⟩
  choose n hn using hloc
  let I : Ideal R := ∏ v ∈ hT.toFinset, v.asIdeal ^ (n v)
  have hI : I ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  refine ⟨r, hr0, fun y hy => ?_⟩
  have hyint : ∀ v, y v ∈ v.adicCompletionIntegers K := fun v => by
    rw [mem_adicCompletionIntegers]
    exact (hy v).trans (v.intValuation_le_one r)
  have hy' : y = mk (fun v => ⟨y v, hyint v⟩) := by ext v; rfl
  rw [hy']
  apply hsub
  intro v hv
  apply hn v
  refine (hy v).trans ?_
  rw [intValuation_le_pow_iff_mem]
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 hv)) hrI

theorem denseRange_finiteAdele : DenseRange (algebraMap K (FiniteAdeleRing R K)) := by
  intro b
  rw [mem_closure_iff_nhds]
  intro N hN
  have h0 : (fun y => b + y) ⁻¹' N ∈ 𝓝 (0 : FiniteAdeleRing R K) := by
    have ht := (continuous_const_add b).tendsto (0 : FiniteAdeleRing R K)
    rw [add_zero] at ht
    exact ht hN
  obtain ⟨r, hr, hrN⟩ := nhds_zero_int h0
  obtain ⟨u, hu⟩ := ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx_adele b
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Lib.AdeleIntA.exists_approx (b - algebraMap K _ u) hu r hr
  refine ⟨algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a), ?_, ⟨_, rfl⟩⟩
  have hx : algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a) - b =
      -((b - algebraMap K (FiniteAdeleRing R K) u) -
        algebraMap K (FiniteAdeleRing R K) (algebraMap R K a)) := by
    rw [map_add (f := _)]; ring
  have hmem := hrN (algebraMap K (FiniteAdeleRing R K) (u + algebraMap R K a) - b) (by
    rw [hx]
    intro v
    have hv : (-((b - algebraMap K (FiniteAdeleRing R K) u) -
        algebraMap K (FiniteAdeleRing R K) (algebraMap R K a))) v =
        -((b - algebraMap K (FiniteAdeleRing R K) u) v - algebraMap K _ (algebraMap R K a)) := by
      rfl
    rw [hv, Valuation.map_neg]
    exact ha v)
  simpa using hmem

end ReciprocityTheory.ChartRestriction.G.SA
