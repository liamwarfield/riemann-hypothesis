module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsGoodSplitPrimeCmField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUnique
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConst

theorem gauge_exists_pos_unique :
    ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c :=
  GlobalTheory.GaugeConst.exists_unique_isGauge

end GlobalTheory.GaugeConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_exists_pos_unique : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ c : ℝ, 0 < c ∧ IsGauge ε c ∧ ∀ c', IsGauge ε c' → c' = c := by
  first | exact @GlobalTheory.GaugeConst.gauge_exists_pos_unique | exact GlobalTheory.GaugeConst.gauge_exists_pos_unique | (intros; apply GlobalTheory.GaugeConst.gauge_exists_pos_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDegreeOneAvoiding
open NumberField Polynomial

namespace GlobalTheory.LargeSplitPrime

theorem exists_degree_one_avoiding (N : Type) [Field N] [NumberField N] (m : ℤ) (hm : m ≠ 0) :
    ∃ P : Ideal (𝓞 N), P.IsMaximal ∧ (m : 𝓞 N) ∉ P ∧ Function.Surjective (Int.castRingHom (𝓞 N ⧸ P)) := by
  obtain ⟨θ, d, hd, -, hden⟩ := GlobalTheory.SW.SplitPrime.exists_prim_den N
  by_cases hθ : θ = 0
  · refine GlobalTheory.SW.SplitPrime.exists_degree_one (1 : 𝓞 N) one_ne_zero d hd (fun a => ?_) m hm
    obtain ⟨g, hg⟩ := hden a
    refine ⟨C (g.coeff 0), ?_⟩
    rw [hg, hθ, aeval_C, aeval_def, eval₂_at_zero]
  · exact GlobalTheory.SW.SplitPrime.exists_degree_one θ hθ d hd hden m hm

theorem surjective_of_conj {N : Type} [Field N] [NumberField N] [IsGalois ℚ N] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 N)) [hP : P.IsMaximal] [hQ : Q.IsMaximal] (h1 : (p : 𝓞 N) ∈ P) (h2 : (p : 𝓞 N) ∈ Q)
    (hs : Function.Surjective (Int.castRingHom (𝓞 N ⧸ P))) :
    Function.Surjective (Int.castRingHom (𝓞 N ⧸ Q)) := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hp').mpr (by simpa using h1)
  have : Q.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hQ.ne_top hp').mpr (by simpa using h2)
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (N ≃ₐ[ℚ] N)
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨t, ht⟩ := hs (Ideal.Quotient.mk P (σ⁻¹ • a))
  have h3 : (t : 𝓞 N) - σ⁻¹ • a ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht]; simp
  have h4 : σ • ((t : 𝓞 N) - σ⁻¹ • a) ∈ Q := hσ ▸ Ideal.smul_mem_pointwise_smul σ _ _ h3
  have h5 : σ • (t : 𝓞 N) = t := map_intCast (MulSemiringAction.toRingHom _ _ σ) t
  rw [smul_sub, smul_inv_smul, h5] at h4
  exact ⟨t, by simpa using Ideal.Quotient.eq.2 h4⟩

theorem exists_splitsCompl (E : Type) [Field E] [NumberField E] (m : ℕ) :
    ∃ p : ℕ, p.Prime ∧ m < p ∧ Formalism.MainNotions.S.SplitsCompl E p := by
  let N : Type := IntermediateField.normalClosure ℚ E (AlgebraicClosure E)
  haveI : NumberField N := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  haveI : IsAlgClosure ℚ (AlgebraicClosure E) := IsAlgClosure.ofAlgebraic ℚ E (AlgebraicClosure E)
  haveI : Normal ℚ N := normalClosure.normal ℚ E (AlgebraicClosure E)
  haveI : IsGalois ℚ N := IsGalois.mk
  obtain ⟨P, hP, hm, hs⟩ := exists_degree_one_avoiding N ((m.factorial : ℤ) * discr E)
    (mul_ne_zero (by exact_mod_cast m.factorial_ne_zero) (discr_ne_zero E))
  have hp := GlobalTheory.SW.SplitPrime.absNorm_prime P hP hs
  have hnd : ¬ ((Ideal.absNorm P : ℕ) : ℤ) ∣ (m.factorial : ℤ) * discr E := by
    rintro ⟨c, hc⟩
    apply hm
    rw [hc]
    push_cast
    exact P.mul_mem_right _ (Ideal.absNorm_mem P)
  refine ⟨_, hp, ?_, fun P' hP' hmem => ⟨?_, ?_⟩⟩
  · by_contra h
    exact hnd (Dvd.dvd.mul_right (by exact_mod_cast Nat.dvd_factorial hp.pos (not_lt.1 h)) _)
  · obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P'
    have hQm : ((Ideal.absNorm P : ℕ) : 𝓞 N) ∈ Q := by
      have := (Ideal.mem_of_liesOver Q P' _).1 hmem
      simpa using this
    have hsQ := surjective_of_conj hp P Q (Ideal.absNorm_mem P) hQm hs
    have hs' : Function.Surjective (Int.castRingHom (𝓞 E ⧸ P')) := by
      intro x
      obtain ⟨t, ht⟩ := hsQ (algebraMap (𝓞 E ⧸ P') (𝓞 N ⧸ Q) x)
      refine ⟨t, FaithfulSMul.algebraMap_injective (𝓞 E ⧸ P') (𝓞 N ⧸ Q) ?_⟩
      rw [← ht]; simp
    have hq := GlobalTheory.SW.SplitPrime.absNorm_prime P' hP' hs'
    by_contra hne
    have hco : IsCoprime ((Ideal.absNorm P' : ℕ) : 𝓞 E) ((Ideal.absNorm P : ℕ) : 𝓞 E) :=
      ((Nat.coprime_primes hq hp).2 hne).cast
    obtain ⟨a, b, hab⟩ := hco
    exact hP'.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ P'.add_mem (P'.mul_mem_left _ (Ideal.absNorm_mem P')) (P'.mul_mem_left _ hmem)))
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hp hmem
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx E hp).1 (fun h => hnd (h.mul_left _)) P'
        hP'.isPrime hmem)

end GlobalTheory.LargeSplitPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroup
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeWhole

private theorem pos_of_isGauge' {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) : 0 < c := by
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  by_contra hc
  push_neg at hc
  have hle : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2) ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
      (pow_nonneg (le_of_lt hr) _)
  have := le_of_tendsto h' hle
  linarith

theorem isGaugeSub_univ {n : ℕ} {ε : Fin n → Bool} {c : ℝ} (h : IsGauge ε c) :
    0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε) := by
  have hc := pos_of_isGauge' h
  have h' : Filter.Tendsto
      (fun r : ℝ => c * (Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}).toReal / r ^ (n ^ 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal) := h
  have hpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hfin : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨hc, ?_⟩
  unfold IsGaugeSub
  refine ⟨by simp, fun s _ => ?_, ?_⟩
  · rw [Measure.map_smul, map_mul_left_eq_self]
    exact (measurable_const_smul s).aemeasurable
  · rw [← ENNReal.ofReal_toReal hfin]
    refine (ENNReal.tendsto_ofReal h').congr' ?_
    filter_upwards [h'.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hr hr0
    have hr0' : (0 : ℝ) < r := hr0
    have hμ : Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
      intro htop
      rw [htop] at hr
      simp at hr
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos (pow_pos hr0' _),
      ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hμ]

theorem gauge_whole : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  intro n ε
  refine ⟨fun c hc => isGaugeSub_univ hc, ?_⟩
  obtain ⟨E, hE, horth, hexp⟩ := GlobalTheory.LieONB.exists_orthonormal_basis n ε
  refine ⟨⊤, E, fun _ _ _ _ => Submodule.mem_top, horth, fun X => ?_, ?_⟩
  · constructor
    · rintro ⟨-, hX⟩
      rw [hexp X hX]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hs : ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i = (((X * (E i)ᴴ).trace).re : ℝ) • E i := by
        ext a b
        simp [Complex.real_smul]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro hX
      refine ⟨Submodule.mem_top, ?_⟩
      have hle : Submodule.span ℝ (Set.range E) ≤ GlobalTheory.GaugeConst.lieJ ε := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact GlobalTheory.GaugeConst.mem_lieJ.mpr (hE i).1
      exact GlobalTheory.GaugeConst.mem_lieJ.mp (hle hX)
  · ext g
    simp

end GlobalTheory.GaugeWhole
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeWholeGroupStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaarGauge_whole_group : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ c : ℝ, IsGauge ε c → 0 < c ∧ IsGaugeSub (Set.univ : Set (Formalism.REAL.UJ ε)) (n ^ 2) (ENNReal.ofReal c • Formalism.REAL.muG ε)) ∧ ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ (Set.univ : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := by
  first | exact @GlobalTheory.GaugeWhole.gauge_whole | exact GlobalTheory.GaugeWhole.gauge_whole | (intros; apply GlobalTheory.GaugeWhole.gauge_whole <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvSubOneMem
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.GaugeSubLoc

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem inv_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (g : Formalism.REAL.UJ ε) (hg : uMat g - 1 ∈ A) : uMat g⁻¹ - 1 ∈ A := by

  have hmap : ∀ W : A, uMat g * (W : Matrix (Fin n) (Fin n) ℂ) ∈ A := by
    intro W
    have : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = (uMat g - 1) * W + W := by noncomm_ring
    rw [this]
    exact A.add_mem (hA _ hg _ W.2) W.2
  let T : A →ₗ[ℝ] A :=
    LinearMap.codRestrict A ((LinearMap.mulLeft ℝ (uMat g)).comp A.subtype) hmap
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro W hW
    have h0 : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = 0 := congrArg Subtype.val hW
    apply Subtype.ext
    calc (W : Matrix (Fin n) (Fin n) ℂ) = uMat g⁻¹ * (uMat g * W) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  obtain ⟨W, hW⟩ := (LinearMap.injective_iff_surjective (f := T)).mp hinj ⟨-(uMat g - 1), A.neg_mem hg⟩
  have hW' : uMat g * (W : Matrix (Fin n) (Fin n) ℂ) = -(uMat g - 1) := congrArg Subtype.val hW
  have hinv : uMat g⁻¹ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (1 + (W : Matrix (Fin n) (Fin n) ℂ))) := by
          rw [Matrix.mul_add, Matrix.mul_one, hW', show uMat g + -(uMat g - 1) = 1 by abel,
            Matrix.mul_one]
      _ = 1 + (W : Matrix (Fin n) (Fin n) ℂ) := by
          rw [← Matrix.mul_assoc, uMat_inv_mul, Matrix.one_mul]
  rw [hinv, add_sub_cancel_left]
  exact W.2

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      rw [uMat_mul]; noncomm_ring
    change uMat (g * h) - 1 ∈ A
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := fun {g} hg => inv_sub_one_mem A hA g hg

theorem isClosed_algSub (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (Formalism.REAL.UJ ε)) := by
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => uMat g - 1) :=
    (Units.continuous_val.comp continuous_subtype_val).sub continuous_const
  exact A.closed_of_finiteDimensional.preimage hc

end GlobalTheory.GaugeSubLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebra
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric Formalism.REAL

noncomputable section

namespace GlobalTheory.GaugeSubExists

open GlobalTheory.GaugeConst

variable {n : ℕ}

theorem exp_sub_one_mem (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ A) :
    NormedSpace.exp X - 1 ∈ A := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X
  have h1 := (hasSum_nat_add_iff' 1).2 h
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at h1
  have hp : ∀ k : ℕ, X ^ (k + 1) ∈ A := by
    intro k
    induction k with
    | zero => simpa using hX
    | succ k ih => rw [pow_succ]; exact hA _ ih _ hX
  exact A.closed_of_finiteDimensional.mem_of_tendsto h1.tendsto_sum_nat
    (Eventually.of_forall fun m => A.sum_mem fun k _ => A.smul_mem _ (hp k))

def algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Subgroup (UJ ε) where
  carrier := {g | uMat g - 1 ∈ A}
  one_mem' := by
    change (1 : Matrix (Fin n) (Fin n) ℂ) - 1 ∈ A
    simp
  mul_mem' := by
    intro g h hg hh
    change uMat g * uMat h - 1 ∈ A
    have : uMat g * uMat h - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
      noncomm_ring
    rw [this]
    exact A.add_mem (A.add_mem (hA _ hg _ hh) hg) hh
  inv_mem' := by
    intro g hg
    have hgi : uMat g⁻¹ * uMat g = 1 := g.1.inv_mul
    have hst : ∀ x ∈ A, LinearMap.mulLeft ℝ (uMat g) x ∈ A := by
      intro x hx
      have : LinearMap.mulLeft ℝ (uMat g) x = (uMat g - 1) * x + x := by
        rw [LinearMap.mulLeft_apply]; noncomm_ring
      rw [this]
      exact A.add_mem (hA _ hg _ hx) hx
    have hinj : Function.Injective ((LinearMap.mulLeft ℝ (uMat g)).restrict hst) := by
      intro x y hxy
      have h1 : uMat g * x.1 = uMat g * y.1 := congrArg Subtype.val hxy
      have h2 := congrArg (uMat g⁻¹ * ·) h1
      simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul] at h2
      exact Subtype.ext h2
    obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨_, hg⟩
    have h1 : uMat g * x.1 = uMat g - 1 := congrArg Subtype.val hx
    have h2 := congrArg (uMat g⁻¹ * ·) h1
    simp only [← Matrix.mul_assoc, hgi, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one] at h2
    change uMat g⁻¹ - 1 ∈ A
    rw [← neg_sub, ← h2]
    exact A.neg_mem x.2

theorem isClosed_algSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : IsClosed (algSub ε A hA : Set (UJ ε)) :=
  A.closed_of_finiteDimensional.preimage ((continuous_uMat ε).sub continuous_const)

theorem exists_preimage {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (A : Submodule ℝ M) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) (hA : ∀ X ∈ A, f X ∈ A) {W : Set M} (hW : W ∈ 𝓝 (0 : M)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ f Y = a.1 := by
  obtain ⟨p, hp⟩ := A.subtype.exists_leftInverse_of_injective A.ker_subtype
  have hp' : ∀ x : A, p x.1 = x := fun x => LinearMap.congr_fun hp x
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ _
  have h1 : HasStrictFDerivAt (fun x : A => f x.1) A.subtypeL 0 :=
    HasStrictFDerivAt.comp (0 : A) (g := f) (f := Subtype.val) hf A.subtypeL.hasStrictFDerivAt
  have h2 := (LinearMap.toContinuousLinearMap p).hasStrictFDerivAt.comp (0 : A) h1
  have h3 : (LinearMap.toContinuousLinearMap p).comp A.subtypeL =
      (ContinuousLinearEquiv.refl ℝ A : A →L[ℝ] A) := by
    ext1 x; exact hp' x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [Submodule.coe_zero, h0, map_zero] at h4
  rw [← h4]
  have h6 : Subtype.val ⁻¹' W ∈ 𝓝 (0 : A) := continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  refine mem_of_superset (image_mem_map h6) ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact ⟨Y.1, Y.2, hY, (congrArg Subtype.val (hp' ⟨_, hA _ Y.2⟩)).symm⟩


open scoped Matrix.Norms.Frobenius in
theorem exists_log (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {W : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hW : W ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ)) :
    ∀ᶠ a : A in 𝓝 0, ∃ Y ∈ A, Y ∈ W ∧ NormedSpace.exp Y - 1 = a.1 := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℝ) (α := ℂ)
  exact exists_preimage (M := Matrix (Fin n) (Fin n) ℂ) A (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ)))
    (fun _ hX => exp_sub_one_mem A hA hX) hW

def expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (X : ↥(A ⊓ lieJ ε)) : algSub ε A hA :=
  ⟨expJ ε ⟨X.1, X.2.2⟩, exp_sub_one_mem A hA X.2.1⟩

theorem continuous_expSub (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) : Continuous (expSub ε A hA) :=
  ((continuous_expJ ε).comp (continuous_subtype_val.subtype_mk _)).subtype_mk _

theorem expSub_image_mem_nhds (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) {U : Set ↥(A ⊓ lieJ ε)} (hU : U ∈ 𝓝 (0 : ↥(A ⊓ lieJ ε))) :
    expSub ε A hA '' U ∈ 𝓝 (1 : algSub ε A hA) := by
  obtain ⟨e, he, h0⟩ := UpqExpChart.exists_chart (n := Fin n)
  have hinj : Set.InjOn NormedSpace.exp e.source := he ▸ e.injOn
  have hs := e.open_source.mem_nhds h0
  obtain ⟨T, hT, hTU⟩ := (mem_nhds_subtype _ _ _).1 hU
  have h1 : expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source)) ∈ 𝓝 (1 : UJ ε) :=
    expJ_image_mem_nhds ε (continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem hT hs))
  have h2 : Subtype.val ⁻¹' (expJ ε '' (Subtype.val ⁻¹' (T ∩ e.source))) ∈ 𝓝 (1 : algSub ε A hA) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds h1
  have hc : Continuous fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A) :=
    (((continuous_uMat ε).comp continuous_subtype_val).sub continuous_const).subtype_mk _
  have h3 : Tendsto (fun g : algSub ε A hA => (⟨uMat g.1 - 1, g.2⟩ : A)) (𝓝 1) (𝓝 0) :=
    hc.tendsto' 1 0 (Subtype.ext (sub_self (1 : Matrix (Fin n) (Fin n) ℂ)))
  filter_upwards [h2, h3.eventually (exists_log A hA hs)] with g hg1 hg2
  obtain ⟨X, hX, hXg⟩ := hg1
  obtain ⟨Y, hYA, hY, hYg⟩ := hg2
  have h4 : NormedSpace.exp X.1 = uMat g.1 := congrArg uMat hXg
  have h5 : NormedSpace.exp Y = uMat g.1 := sub_left_injective hYg
  have h6 : X.1 = Y := hinj hX.2 hY (h4.trans h5.symm)
  exact ⟨⟨X.1, h6 ▸ hYA, X.2⟩, hTU hX.1, Subtype.ext hXg⟩

theorem finrank_eq (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) {d : ℕ}
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hs : ∀ X, (X ∈ A ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) :
    Module.finrank ℝ ↥(A ⊓ lieJ ε) = d := by
  have h1 : A ⊓ lieJ ε = Submodule.span ℝ (Set.range E) := Submodule.ext hs
  have h2 : LinearIndependent ℝ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h := congrArg (fun Z => ((Z * (E k)ᴴ).trace).re) hc
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
      Complex.smul_re, hE] at h
    simpa using h
  rw [h1, finrank_span_eq_card h2, Fintype.card_fin]


open scoped Matrix.Norms.Frobenius in
theorem exists_limit (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) (μ : Measure (algSub ε A hA)) [μ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun r : ℝ => (μ {g | Real.sqrt (Formalism.REAL.hs (uMat g.1 - 1)) ≤ r}).toReal /
        r ^ Module.finrank ℝ ↥(A ⊓ lieJ ε)) (𝓝[>] 0) (𝓝 c) := by
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAddCommGroup
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.frobeniusNormedAlgebra
  let L₀ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have h := exists_limit_of_chart ↥(A ⊓ lieJ ε) (Matrix (Fin n) (Fin n) ℂ) (algSub ε A hA) μ
    (expSub ε A hA) (fun g => uMat g.1)
    (A ⊓ lieJ ε).subtypeₗᵢ (fun g => L₀ (uMat g.1)) (continuous_expSub ε A hA)
    (by
      apply Subtype.ext
      apply uMat_injective ε
      change NormedSpace.exp 0 = 1
      exact NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))
    (by
      change HasStrictFDerivAt (fun x : ↥(A ⊓ lieJ ε) => NormedSpace.exp x.1)
        (A ⊓ lieJ ε).subtypeL 0
      exact CompactDualExists.exp_strict.comp
        (0 : ↥(A ⊓ lieJ ε)) (A ⊓ lieJ ε).subtypeL.hasStrictFDerivAt)
    (hL₀.comp ((continuous_uMat ε).comp continuous_subtype_val)).continuousAt
    (by
      change (L₀ 1) = ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)
      ext X
      simp [L₀]) (fun g h => rfl)
    (fun r hr => expSub_image_mem_nhds ε A hA (ball_mem_nhds 0 hr))
    ((uJEmb n ε).1.isInducing.comp IsInducing.subtypeVal)
  simp only [sqrt_hs]
  exact h

theorem exists_isGaugeSub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  intro n ε A d E hA hE hs
  have hcl := isClosed_algSub ε A hA
  haveI : LocallyCompactSpace (algSub ε A hA) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hemb : MeasurableEmbedding (Subtype.val : algSub ε A hA → UJ ε) :=
    MeasurableEmbedding.subtype_coe hcl.measurableSet
  obtain ⟨c, hc, h⟩ := exists_limit ε A hA Measure.haar
  rw [finrank_eq ε A E hE hs] at h
  set B := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hBdef
  have hBt : B ≠ ⊤ := measure_ball_lt_top.ne
  have hB : 0 < B.toReal := ENNReal.toReal_pos (measure_ball_pos _ 0 one_pos).ne' hBt
  have hq : 0 < B.toReal / c := div_pos hB hc
  set ν : Measure (algSub ε A hA) := (B.toReal / c).toNNReal • Measure.haar with hν
  haveI : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul _ (Real.toNNReal_pos.2 hq).ne'
  haveI : SecondCountableTopology (algSub ε A hA) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨ν.map Subtype.val, hemb.sigmaFinite_map, ?_, fun s hs => ?_, ?_⟩
  · rw [hemb.map_apply]
    convert measure_empty (μ := ν)
    ext g
    exact ⟨fun hg => hg g.2, False.elim⟩
  · rw [Measure.map_map (measurable_const_mul s) hemb.measurable]
    conv_rhs => rw [← map_mul_left_eq_self ν (⟨s, hs⟩ : algSub ε A hA)]
    rw [Measure.map_map hemb.measurable (measurable_const_mul _)]
    rfl
  · have h1 := ENNReal.tendsto_ofReal (h.const_mul (B.toReal / c))
    rw [div_mul_cancel₀ _ hc.ne', ENNReal.ofReal_toReal hBt] at h1
    refine h1.congr' ?_
    filter_upwards [h.eventually (lt_mem_nhds hc), self_mem_nhdsWithin] with r h2 hr
    have hr' : (0 : ℝ) < r := hr
    have h3 := (ENNReal.toReal_pos_iff.1 ((div_pos_iff_of_pos_right (pow_pos hr' d)).1 h2)).2.ne
    rw [hemb.map_apply, hν, Measure.coe_nnreal_smul_apply, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_div_of_pos (pow_pos hr' d), ENNReal.ofReal_toReal h3, mul_div_assoc]
    rfl

end GlobalTheory.GaugeSubExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRiemannianHaarUnitaryJSubgroupOfAlgebraStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_riemannianHaar_unitaryJSubgroupOfAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∃ μ : Measure (Formalism.REAL.UJ ε), SigmaFinite μ ∧ IsGaugeSub {g | uMat g - 1 ∈ A} d μ := by
  first | exact @GlobalTheory.GaugeSubExists.exists_isGaugeSub | exact GlobalTheory.GaugeSubExists.exists_isGaugeSub | (intros; apply GlobalTheory.GaugeSubExists.exists_isGaugeSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilpotentOfStrict
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.UnitriHaar

theorem map_add_nilpotent {k G : Type*} [NormedField k] [IsUltrametricDist k] [ProperSpace k]
    [AddCommGroup G] [Module k G] [Module.Finite k G] [TopologicalSpace G] [IsModuleTopology k G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (N : Module.End k G) (hN : IsNilpotent N) : μ.map (fun x => x + N x) = μ := by
  have : IsTopologicalAddGroup G := IsModuleTopology.topologicalAddGroup k G
  let e₀ : G ≃ₗ[k] (Fin (Module.finrank k G) → k) := (Module.finBasis k G).equivFun
  let e : G ≃ₜ (Fin (Module.finrank k G) → k) :=
    { e₀.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap }
  have : LocallyCompactSpace G := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology G := e.secondCountableTopology
  have hc : ∀ f : Module.End k G, Continuous f := fun f => IsModuleTopology.continuous_of_linearMap f
  let K₀ := IsUltrametricDist.closedBall_openAddSubgroup (Fin (Module.finrank k G) → k) one_pos
  let K : AddSubgroup G := K₀.toAddSubgroup.comap e₀.toLinearMap.toAddMonoidHom
  have hKo : IsOpen (K : Set G) := K₀.isOpen.preimage e.continuous
  have hKc : IsCompact (K : Set G) :=
    e.isCompact_preimage.2 (isCompact_closedBall (0 : Fin (Module.finrank k G) → k) 1)
  obtain ⟨m, hm⟩ := hN
  let B : AddSubgroup G := ⨅ j : ℕ, K.comap (N ^ j).toAddMonoidHom
  have hB : ∀ x, x ∈ B ↔ ∀ j : ℕ, (N ^ j) x ∈ K := fun x => by
    simp [B, AddSubgroup.mem_iInf]
  have hBo : IsOpen (B : Set G) := by
    have : (B : Set G) = ⋂ j ∈ Finset.range m, (N ^ j : Module.End k G) ⁻¹' (K : Set G) := by
      ext x
      simp only [SetLike.mem_coe, hB, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
      refine ⟨fun h j _ => h j, fun h j => ?_⟩
      by_cases hj : j < m
      · exact h j hj
      · rw [pow_eq_zero_of_le (not_lt.1 hj) hm]; exact K.zero_mem
    rw [this]
    exact isOpen_biInter_finset fun j _ => hKo.preimage (hc _)
  have hBc : IsCompact (B : Set G) :=
    hKc.of_isClosed_subset (B.isClosed_of_isOpen hBo) fun x hx => by
      simpa using (hB x).1 hx 0
  have hNB : ∀ x ∈ B, N x ∈ B := fun x hx => (hB _).2 fun j => by
    rw [← Module.End.mul_apply, ← pow_succ]; exact (hB x).1 hx _
  have hNp : ∀ (j : ℕ), ∀ x ∈ B, ((-N) ^ j) x ∈ B := fun j => by
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      exact B.neg_mem (hNB _ (ih x hx))
  have hm' : (-N) ^ m = 0 := by rw [neg_pow, hm, mul_zero]
  have h1 : (∑ j ∈ Finset.range m, (-N) ^ j) * (1 + N) = 1 := by
    have := geom_sum_mul_neg (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  have h2 : (1 + N) * (∑ j ∈ Finset.range m, (-N) ^ j) = 1 := by
    have := mul_neg_geom_sum (-N) m
    rwa [hm', sub_zero, sub_neg_eq_add] at this
  let L : G ≃ₜ+ G :=
    { toFun := fun x => x + N x
      invFun := (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G)
      left_inv := fun x => LinearMap.congr_fun h1 x
      right_inv := fun x => LinearMap.congr_fun h2 x
      map_add' := fun x y => by rw [map_add (f := _)]; abel
      continuous_toFun := continuous_id.add (hc N)
      continuous_invFun := hc _ }
  have hLB : L ⁻¹' (B : Set G) = B := by
    ext x
    refine ⟨fun hx => ?_, fun hx => B.add_mem hx (hNB x hx)⟩
    have : x = (∑ j ∈ Finset.range m, (-N) ^ j : Module.End k G) (L x) := (L.left_inv x).symm
    rw [this, LinearMap.sum_apply]
    exact B.sum_mem fun j _ => hNp j _ hx
  change μ.map L = μ
  have : (μ.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have h3 := Measure.isAddLeftInvariant_eq_smul (μ.map L) μ
  have h4 : μ.map L B = μ B := by
    rw [Measure.map_apply (show Continuous L from L.continuous).measurable hBo.measurableSet, hLB]
  have h5 : μ B ≠ 0 := (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne'
  have h6 : μ B ≠ ⊤ := hBc.measure_lt_top.ne
  have h7 : Measure.addHaarScalarFactor (μ.map L) μ = 1 := by
    rw [h3, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
    have := (ENNReal.mul_left_inj h5 h6).1 (h4.trans (one_mul _).symm)
    exact_mod_cast this
  rw [h3, h7, one_smul]

theorem nilpotent_of_strict {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ a b, ¬ a < b → A a b = 0) : A ^ n = 0 := by
  have : ∀ (j : ℕ) (a b : Fin n), b.val < a.val + j → (A ^ j) a b = 0 := fun j => by
    induction j with
    | zero => intro a b h; rw [pow_zero, Matrix.one_apply_ne]; rintro rfl; omega
    | succ j ih =>
      intro a b h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : c < b
      · rw [ih a c (by have : c.val < b.val := hc; omega), zero_mul]
      · rw [hA c b hc, mul_zero]
  exact Matrix.ext fun a b => this n a b (by omega)

def strictOf (R : Type*) [CommRing R] (n : ℕ) :
    ({p : Fin n × Fin n // p.1 < p.2} → R) →ₗ[R] Matrix (Fin n) (Fin n) R where
  toFun x := Matrix.of fun a b => if h : a < b then x ⟨(a, b), h⟩ else 0
  map_add' x y := by ext a b; simp only [Matrix.add_apply, Matrix.of_apply]; split_ifs <;> simp
  map_smul' c x := by ext a b; simp only [Matrix.smul_apply, Matrix.of_apply]; split_ifs <;> simp

def above (R : Type*) [CommRing R] (n : ℕ) :
    Matrix (Fin n) (Fin n) R →ₗ[R] ({p : Fin n × Fin n // p.1 < p.2} → R) where
  toFun A p := A p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_nilpotent {R : Type*} [CommRing R] {n : ℕ} (u : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ i, u i i = 1) (h0 : ∀ i j, j < i → u i j = 0) :
    ∃ N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R), IsNilpotent N ∧
      ∀ x : {p : Fin n × Fin n // p.1 < p.2} → R,
        (fun p : {p : Fin n × Fin n // p.1 < p.2} => (u * Matrix.of (fun a b : Fin n =>
          (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R))) p.1.1 p.1.2) =
        above R n u + (x + N x) := by
  have hu : ∀ a b, ¬ a < b → (u - 1) a b = 0 := fun a b h => by
    rcases (not_lt.1 h).eq_or_lt with rfl | h
    · simp [h1]
    · simp [h0 a b h, Matrix.one_apply_ne h.ne']
  have hs : ∀ x a b, ¬ a < b → strictOf R n x a b = 0 := fun x a b h => dif_neg h
  have has : ∀ x, above R n (strictOf R n x) = x := fun x => funext fun p => dif_pos p.2
  let N : Module.End R ({p : Fin n × Fin n // p.1 < p.2} → R) :=
    above R n ∘ₗ LinearMap.mulLeft R (u - 1) ∘ₗ strictOf R n
  have hN : ∀ x, strictOf R n (N x) = (u - 1) * strictOf R n x := fun x => by
    ext a b
    by_cases h : a < b
    · exact dif_pos h
    · rw [hs _ a b h, Matrix.mul_apply]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      by_cases hc : a < c
      · rw [hs x c b fun h' => h (hc.trans h'), mul_zero]
      · rw [hu a c hc, zero_mul]
  have hp : ∀ (j : ℕ) x, strictOf R n ((N ^ j) x) = (u - 1) ^ j * strictOf R n x := fun j => by
    induction j with
    | zero => simp
    | succ j ih => intro x; rw [pow_succ', pow_succ', Module.End.mul_apply, hN, ih, mul_assoc]
  refine ⟨N, ⟨n, LinearMap.ext fun x => ?_⟩, fun x => ?_⟩
  · rw [← has ((N ^ n) x), hp, nilpotent_of_strict _ hu, zero_mul, map_zero, LinearMap.zero_apply]
  · have : Matrix.of (fun a b : Fin n =>
        (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : R)) = 1 + strictOf R n x := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [hs x a a (lt_irrefl a)]
      · simp [hab, strictOf]
    rw [this]
    change above R n (u * (1 + strictOf R n x)) = _
    have h2 : u * (1 + strictOf R n x) = u + (strictOf R n x + (u - 1) * strictOf R n x) := by
      noncomm_ring
    rw [h2, map_add (f := _), map_add (f := _), has]
    rfl


open GlobalTheory.GaugeEx in
theorem map_unitri_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (r : ℕ) (μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E)), μU.IsAddHaarMeasure → ∀ u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Fv F v ⊗[F] E), (∀ i, u i i = 1) → (∀ i j, j < i → u i j = 0) → μU.map (fun (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}) => (u * Matrix.of (fun a b : Fin (r + 1) => (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E))) p.1.1 p.1.2) = μU := by
  intro F E _ _ _ _ _ v r μ hμ u h1 h0
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨N, hN, hx⟩ := exists_nilpotent u h1 h0
  have hN' : IsNilpotent (N.restrictScalars (Fv F v) : Module.End (Fv F v) _) := by
    obtain ⟨m, hm⟩ := hN
    refine ⟨m, LinearMap.ext fun x => ?_⟩
    have := LinearMap.congr_fun hm x
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h2 := map_add_nilpotent μ _ hN'
  have hc : Continuous fun x => x + N.restrictScalars (Fv F v) x :=
    continuous_id.add (IsModuleTopology.continuous_of_linearMap _)
  rw [funext hx]
  refine Eq.trans ?_ (map_add_left_eq_self μ (above _ (r + 1) u))
  conv_rhs => rw [← h2]
  rw [Measure.map_map (measurable_const_add _) hc.measurable]
  rfl

end GlobalTheory.UnitriHaar
end
