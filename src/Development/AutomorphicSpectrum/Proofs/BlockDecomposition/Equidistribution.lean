module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeCosetScaledRiemannSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantBoxApproximation

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLattice
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

private theorem forall_locMem_iff_exists_mem_ideal {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (z : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.CompanionTheory.Equi.LocMem I v z) ↔ ∃ y ∈ I, (y : F) = z := by
  constructor
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {s | ∃ y ∈ I, (s : F) * z = y}
        add_mem' := by
          rintro a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨y, hy, h₁⟩
          exact ⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : M ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      have hv := h ⟨M, hM.isPrime, hM0⟩
      unfold GlobalTheory.CompanionTheory.Equi.LocMem at hv
      obtain ⟨s, hs, y, hy, hsy⟩ := hv
      exact hs (hJM ⟨y, hy, hsy⟩)
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨y, hy, by simpa using hy1.symm⟩
  · rintro ⟨y, hy, rfl⟩ v
    unfold GlobalTheory.CompanionTheory.Equi.LocMem
    exact ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩

theorem cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  ext x
  simp only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i
  · intro h v _ i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v

end GlobalTheory.CompanionTheory.Equi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLatticeStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_empty_places_lattice : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (I : Ideal (𝓞 F)) (x0 : ι → F), cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | exact GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset | (intros; apply GlobalTheory.CompanionTheory.Equi.cosetOff_empty_eq_latCoset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegral
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

theorem locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp

theorem cosetOff_top : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]

end GlobalTheory.CompanionTheory.Equi.CosetTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegralStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_unit_ideal_integral : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | exact GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetTop.cosetOff_top <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinement
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi.CosetStep

variable {F : Type} [Field F] [NumberField F]

theorem exists_pow_mul (v : HeightOneSpectrum (𝓞 F)) {D : Ideal (𝓞 F)} (hD : D ≠ ⊥) :
    ∃ (m : ℕ) (B : Ideal (𝓞 F)), D = v.asIdeal ^ m * B ∧ ¬ B ≤ v.asIdeal := by
  have hv : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hex : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) := by
    by_contra h
    push_neg at h
    apply hD
    have h' : D ≤ ⨅ i : ℕ, v.asIdeal ^ i := by
      refine le_iInf fun i => ?_
      cases i with
      | zero => simp
      | succ i => exact h i
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hv] at h'
    exact le_bot_iff.mp h'
  obtain ⟨m, hm, hle⟩ : ∃ m : ℕ, ¬ D ≤ v.asIdeal ^ (m + 1) ∧ D ≤ v.asIdeal ^ m := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · simp [h0]
    · have h1 := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
      push_neg at h1
      have e : Nat.find hex - 1 + 1 = Nat.find hex := by omega
      rwa [e] at h1
  obtain ⟨B, hB⟩ := Ideal.dvd_iff_le.mpr hle
  refine ⟨m, B, hB, fun hBv => hm ?_⟩
  rw [hB, pow_succ]
  exact Ideal.mul_mono_right hBv

theorem exists_mem_pow_not_mem {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ) :
    ∃ e ∈ v.asIdeal ^ k, e ∉ w.asIdeal := by
  by_contra h
  push_neg at h
  have hle : v.asIdeal ^ k ≤ w.asIdeal := fun e he => h e he
  have hvw : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hvw).symm)

theorem locMem_add {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a + b) := by
  obtain ⟨s, hs, y, hy, hsy⟩ := ha
  obtain ⟨t, ht, z, hz, htz⟩ := hb
  refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, t * y + s * z,
    I.add_mem (I.mul_mem_left _ hy) (I.mul_mem_left _ hz), ?_⟩
  push_cast
  linear_combination (t : F) * hsy + (s : F) * htz

theorem locMem_neg {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a : F}
    (ha : LocMem I w a) : LocMem I w (-a) := by
  obtain ⟨s, hs, y, hy, hsy⟩ := ha
  refine ⟨s, hs, -y, I.neg_mem hy, ?_⟩
  push_cast
  rw [mul_neg, hsy]

theorem locMem_sub {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a b : F}
    (ha : LocMem I w a) (hb : LocMem I w b) : LocMem I w (a - b) := by
  rw [sub_eq_add_neg]; exact locMem_add ha (locMem_neg hb)

theorem locMem_mul_pow_iff {I : Ideal (𝓞 F)} {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ)
    {t : F} : LocMem (I * v.asIdeal ^ k) w t ↔ LocMem I w t := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    exact ⟨s, hs, y, (Ideal.mul_le_left : I * v.asIdeal ^ k ≤ I) hy, h⟩
  · rintro ⟨s, hs, y, hy, h⟩
    obtain ⟨e, he, hew⟩ := exists_mem_pow_not_mem hw k
    refine ⟨e * s, fun hm => (w.isPrime.mem_or_mem hm).elim hew hs, y * e, Ideal.mul_mem_mul hy he, ?_⟩
    push_cast
    rw [mul_assoc, h]
    ring

theorem val_le_of_mem_pow (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : y ∈ v.asIdeal ^ k) :
    v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem y k).2 hy

theorem mem_pow_of_val_le (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ))) :
    y ∈ v.asIdeal ^ k := by
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hy
  exact (v.intValuation_le_pow_iff_mem y k).1 hy

theorem val_eq_one_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : 𝓞 F} (hs : s ∉ v.asIdeal) :
    v.valuation F (algebraMap (𝓞 F) F s) = 1 := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl v s).mpr hs

theorem mem_ballV_iff (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (t : F) :
    algebraMap F (Fv F v) t ∈ ballV v k ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by
  show Valued.v (algebraMap F (Fv F v) t) ≤ _ ↔ _
  rw [show Valued.v (algebraMap F (Fv F v) t) = v.valuation F t by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t
      | rfl]

theorem ballV_add {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {a b : Fv F v}
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a + b ∈ ballV v k := by
  show Valued.v (a + b) ≤ _
  exact (Valuation.map_add _ a b).trans (max_le ha hb)

theorem ballV_sub {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {a b : Fv F v}
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a - b ∈ ballV v k := by
  show Valued.v (a - b) ≤ _
  exact (Valuation.map_sub _ a b).trans (max_le ha hb)

theorem locMem_v_iff {I : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)} (hI : ¬ I ≤ v.asIdeal) (k : ℕ)
    (t : F) : LocMem (I * v.asIdeal ^ k) v t ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by
  constructor
  · rintro ⟨s, hs, y, hy, h⟩
    have h1 := val_le_of_mem_pow v ((Ideal.mul_le_right : I * v.asIdeal ^ k ≤ v.asIdeal ^ k) hy)
    have h2 := val_eq_one_of_not_mem v hs
    have h3 : v.valuation F (algebraMap (𝓞 F) F s * t) = v.valuation F (algebraMap (𝓞 F) F y) := by
      exact congrArg (v.valuation F) h
    rw [map_mul, h2, one_mul] at h3
    rw [h3]
    exact h1
  · intro ht
    obtain ⟨s0, hs0I, hs0v⟩ := SetLike.not_le_iff_exists.mp hI
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) t
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbF : algebraMap (𝓞 F) F b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hspan : Ideal.span {b} ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    obtain ⟨m, B, hbB, hBv⟩ := exists_pow_mul v hspan
    obtain ⟨c, hcB, hcv⟩ := SetLike.not_le_iff_exists.mp hBv
    have hbm : b ∈ v.asIdeal ^ m := by
      have hb' : b ∈ Ideal.span {b} := Ideal.subset_span rfl
      rw [hbB] at hb'
      exact (Ideal.mul_le_left : v.asIdeal ^ m * B ≤ v.asIdeal ^ m) hb'
    have hk1 : WithZero.exp (-(k : ℤ)) ≤ 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    have hvala : v.valuation F (algebraMap (𝓞 F) F a) ≤ WithZero.exp (-(m : ℤ)) := by
      have e : algebraMap (𝓞 F) F a =
          (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) * algebraMap (𝓞 F) F b := by
        field_simp
      rw [e, map_mul]
      calc _ ≤ 1 * WithZero.exp (-(m : ℤ)) := mul_le_mul' (ht.trans hk1) (val_le_of_mem_pow v hbm)
        _ = _ := one_mul _
    have ham : a ∈ v.asIdeal ^ m := mem_pow_of_val_le v hvala
    have hac : a * c ∈ Ideal.span {b} := by
      rw [hbB]
      exact Ideal.mul_mem_mul ham hcB
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hac
    have hrF : algebraMap (𝓞 F) F c * (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) =
        algebraMap (𝓞 F) F r := by
      have := congrArg (algebraMap (𝓞 F) F) hr
      rw [map_mul, map_mul] at this
      field_simp
      linear_combination -this
    have hvr : v.valuation F (algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(k : ℤ)) := by
      rw [← hrF, map_mul, val_eq_one_of_not_mem v hcv, one_mul]
      exact ht
    have hrk : r ∈ v.asIdeal ^ k := mem_pow_of_val_le v hvr
    refine ⟨s0 * c, fun hm => (v.isPrime.mem_or_mem hm).elim hs0v hcv, s0 * r,
      Ideal.mul_mem_mul hs0I hrk, ?_⟩
    have e1 : ((s0 * c : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F c := by
      rw [← map_mul]
    have e2 : ((s0 * r : 𝓞 F) : F) = algebraMap (𝓞 F) F s0 * algebraMap (𝓞 F) F r := by
      rw [← map_mul]
    rw [e1, e2, ← hrF]
    ring

theorem exists_near (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (c : Fv F v) :
    ∃ a : F, algebraMap F (Fv F v) a - c ∈ ballV v k := by
  have hd : DenseRange (algebraMap F (Fv F v)) := HeightOneSpectrum.denseRange_algebraMap F v
  have hval : ∀ t : F, Valued.v (algebraMap F (Fv F v) t) = v.valuation F t := fun t => by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v t
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t
      | rfl
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := F) v
  have hvp : Valued.v (algebraMap F (Fv F v) (π ^ k)) = WithZero.exp (-(k : ℤ)) := by
    rw [hval, map_pow, hπ, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]
  have hp0 : algebraMap F (Fv F v) (π ^ k) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvp
    exact absurd hvp.symm (by simp)
  have hopen : IsOpen {z : Fv F v | Valued.v z ≤ WithZero.exp (-(k : ℤ))} := by
    have h1 := Valued.isOpen_closedBall (R := Fv F v)
      (r := (Valued.v : Valuation (Fv F v) _).restrict (algebraMap F (Fv F v) (π ^ k)))
      ((Valuation.ne_zero_iff _).mpr hp0)
    convert h1 using 2
    funext z
    rw [Valuation.restrict_le_iff, hvp]
  have ho : IsOpen {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hmem : {z : Fv F v | Valued.v (z - c) ≤ WithZero.exp (-(k : ℤ))} ∈ 𝓝 c :=
    ho.mem_nhds (by simp)
  obtain ⟨a, ha⟩ := hd.mem_nhds hmem
  exact ⟨a, ha⟩

private theorem exists_add_eq_one_lemma {v : HeightOneSpectrum (𝓞 F)} {C : Ideal (𝓞 F)}
    (hC : ¬ C ≤ v.asIdeal) (M : ℕ) : ∃ e ∈ C, ∃ f ∈ v.asIdeal ^ M, e + f = 1 := by
  have hcop : C ⊔ v.asIdeal ^ M = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    have h1 : v.asIdeal ^ M ≤ P := le_sup_right.trans hle
    have h2 : C ≤ P := le_sup_left.trans hle
    have h3 : v.asIdeal ≤ P := hP.isPrime.le_of_pow_le h1
    have h4 : v.asIdeal = P := v.isMaximal.eq_of_le hP.ne_top h3
    exact hC (h4 ▸ h2)
  have h1 : (1 : 𝓞 F) ∈ C ⊔ v.asIdeal ^ M := hcop ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  exact ⟨e, he, f, hf, hef⟩

theorem exists_approx {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ)
    (x0 : F) (c : Fv F v) :
    ∃ x1 : F, (∀ w, w ≠ v → LocMem I w (x1 - x0)) ∧ algebraMap F (Fv F v) x1 - c ∈ ballV v k := by
  obtain ⟨a, ha⟩ := exists_near v k c
  obtain ⟨a', b', hb', hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (a - x0)
  have hb0 : b' ≠ 0 := nonZeroDivisors.ne_zero hb'
  have hbF : algebraMap (𝓞 F) F b' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb'
  have hspan : Ideal.span {b'} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨r, B', hbB, hB'v⟩ := exists_pow_mul v hspan
  obtain ⟨m, B, hIB, hBv⟩ := exists_pow_mul v hI
  have hCv : ¬ B' * B ≤ v.asIdeal := fun hle => (v.isPrime.mul_le.mp hle).elim hB'v hBv
  obtain ⟨e, he, f, hf, hef⟩ := exists_add_eq_one_lemma hCv (k + r)
  obtain ⟨g, hgB', hgv⟩ := SetLike.not_le_iff_exists.mp hB'v
  have hgF : algebraMap (𝓞 F) F g ≠ 0 := by
    intro h0
    apply hgv
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mp h0]
    exact v.asIdeal.zero_mem
  have hfg : f * g ∈ Ideal.span {b'} * v.asIdeal ^ k := by
    have e1 : v.asIdeal ^ (k + r) * B' = Ideal.span {b'} * v.asIdeal ^ k := by
      rw [hbB, pow_add]
      ring
    rw [← e1]
    exact Ideal.mul_mem_mul hf hgB'
  obtain ⟨h, hh, hbh⟩ := Ideal.mem_span_singleton_mul.mp hfg
  refine ⟨x0 + (a - x0) * algebraMap (𝓞 F) F e, fun w hw => ?_, ?_⟩
  · rw [add_sub_cancel_left]
    obtain ⟨s1, hs1, hs1w⟩ := exists_mem_pow_not_mem hw r
    obtain ⟨s2, hs2, hs2w⟩ := exists_mem_pow_not_mem hw m
    have hs1e : s1 * e ∈ Ideal.span {b'} * B := by
      have e2 : v.asIdeal ^ r * (B' * B) = Ideal.span {b'} * B := by
        rw [hbB]
        ring
      rw [← e2]
      exact Ideal.mul_mem_mul hs1 he
    obtain ⟨β, hβ, hbβ⟩ := Ideal.mem_span_singleton_mul.mp hs1e
    refine ⟨s2 * s1, fun hm => (w.isPrime.mem_or_mem hm).elim hs2w hs1w, s2 * (a' * β), ?_, ?_⟩
    · rw [hIB]
      exact Ideal.mul_mem_mul hs2 (B.mul_mem_left _ hβ)
    · have h1 := congrArg (algebraMap (𝓞 F) F) hbβ
      rw [map_mul, map_mul] at h1
      have e1 : ((s2 * s1 : 𝓞 F) : F) = algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F s1 := by
        rw [← map_mul]
      have e2 : ((s2 * (a' * β) : 𝓞 F) : F) =
          algebraMap (𝓞 F) F s2 * (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F β) := by
        rw [← map_mul, ← map_mul]
      rw [e1, e2, ← hab]
      field_simp
      linear_combination (-(algebraMap (𝓞 F) F s2 * algebraMap (𝓞 F) F a')) * h1
  · have hy : algebraMap F (Fv F v) (x0 + (a - x0) * algebraMap (𝓞 F) F e) - c =
        algebraMap F (Fv F v) ((a - x0) * algebraMap (𝓞 F) F e - (a - x0)) +
          (algebraMap F (Fv F v) a - c) := by
      rw [map_sub, map_add (f := _), map_mul, map_sub]
      ring
    rw [hy]
    refine ballV_add ((mem_ballV_iff v k _).mpr ?_) ha
    have e3 : (a - x0) * algebraMap (𝓞 F) F e - (a - x0) =
        -(algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F h / algebraMap (𝓞 F) F g) := by
      have h1 := congrArg (algebraMap (𝓞 F) F) hbh
      have h2 := congrArg (algebraMap (𝓞 F) F) hef
      rw [map_mul, map_mul] at h1
      rw [map_add (f := _), map_one] at h2
      rw [← hab]
      field_simp
      linear_combination (algebraMap (𝓞 F) F a' * algebraMap (𝓞 F) F g) * h2 +
        algebraMap (𝓞 F) F a' * h1
    rw [e3, Valuation.map_neg, map_div₀, map_mul, val_eq_one_of_not_mem v hgv, div_one]
    calc _ ≤ 1 * WithZero.exp (-(k : ℤ)) :=
          mul_le_mul' (HeightOneSpectrum.valuation_le_one v a') (val_le_of_mem_pow v hh)
      _ = _ := one_mul _

theorem coset_step : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  intro F _ _ ι S v hvS I hI hIv k x0 c
  choose x1 hx1w hx1v using fun i => exists_approx hI v k (x0 i) (c i)
  refine ⟨x1, fun x => ?_⟩
  simp only [cosetOff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hball⟩ w hwS i
    by_cases hwv : w = v
    · subst hwv
      rw [locMem_v_iff hIv, ← mem_ballV_iff, map_sub]
      have h3 := ballV_sub (hball i) (hx1v i)
      convert h3 using 1
      abel
    · have h1 : LocMem I w (x i - x0 i) := hx w (by simp [hwv, hwS]) i
      have h2 := locMem_sub h1 (hx1w i w hwv)
      rw [locMem_mul_pow_iff hwv]
      convert h2 using 1
      ring
  · intro hx
    refine ⟨fun w hw i => ?_, fun i => ?_⟩
    · have hwv : w ≠ v := fun h => hw (by simp [h])
      have hwS : w ∉ S := fun h => hw (by simp [h])
      have h1 := (locMem_mul_pow_iff hwv k).mp (hx w hwS i)
      have h2 := locMem_add h1 (hx1w i w hwv)
      convert h2 using 1
      ring
    · have h1 := (locMem_v_iff hIv k (x i - x1 i)).mp (hx v hvS i)
      rw [← mem_ballV_iff, map_sub] at h1
      have h3 := ballV_add h1 (hx1v i)
      convert h3 using 1
      abel

end GlobalTheory.CompanionTheory.Equi.CosetStep

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCongruenceRefinementStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_congruence_refinement : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)), v ∉ S → ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → ¬ I ≤ v.asIdeal → ∀ (k : ℕ) (x0 : ι → F) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F, (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := by
  first | exact @GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | exact GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step | (intros; apply GlobalTheory.CompanionTheory.Equi.CosetStep.coset_step <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

theorem squeeze_of_approx {α : Type} {l : Filter α} {A : α → ℝ} {a K : ℝ} (hK : 0 ≤ K)
    (h : ∀ δ : ℝ, 0 < δ → ∃ (B E : α → ℝ) (b e : ℝ), Tendsto B l (𝓝 b) ∧ Tendsto E l (𝓝 e) ∧
      (∀ᶠ t in l, |A t - B t| ≤ δ * E t) ∧ |b - a| ≤ δ * K ∧ e ≤ K) : Tendsto A l (𝓝 a) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hK1 : 0 < K + 1 := by linarith
  set δ := η / (4 * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδK : δ * (K + 1) = η / 4 := by rw [hδ]; field_simp
  obtain ⟨B, E, b, e, hB, hE, hAB, hb, he⟩ := h δ hδ0
  have h1 := (Metric.tendsto_nhds.1 hB) (η / 4) (by linarith)
  have h2 : ∀ᶠ t in l, E t < K + 1 := hE.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2, hAB] with t t1 t2 t3
  rw [Real.dist_eq] at t1 ⊢
  have t4 : δ * E t ≤ δ * (K + 1) := by gcongr
  have t5 : δ * K ≤ δ * (K + 1) := by gcongr; linarith
  have e1 : A t - a = (A t - B t) + (B t - b) + (b - a) := by ring
  rw [e1]
  calc _ ≤ |A t - B t| + |B t - b| + |b - a| := abs_add_three _ _ _
    _ < η := by linarith

theorem summable_of_close {X γ : Type} {g : X → ℝ} (C : Finset γ) (a : γ → ℝ) (u w : γ → X → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ c ∈ C, Summable (u c)) (hw : ∀ c ∈ C, Summable (w c))
    (h : ∀ x, |g x - ∑ c ∈ C, a c * u c x| ≤ δ * ∑ c ∈ C, w c x) :
    Summable g ∧ |(∑' x, g x) - ∑ c ∈ C, a c * ∑' x, u c x| ≤ δ * ∑ c ∈ C, ∑' x, w c x := by
  have hsw : Summable fun x => δ * ∑ c ∈ C, w c x := (summable_sum hw).mul_left δ
  have hsu : Summable fun x => ∑ c ∈ C, a c * u c x := summable_sum fun c hc => (hu c hc).mul_left (a c)
  have hsh : Summable fun x => g x - ∑ c ∈ C, a c * u c x := Summable.of_norm_bounded hsw fun x => by simpa using h x
  have hg : Summable g := by simpa using hsh.add hsu
  refine ⟨hg, ?_⟩
  have e1 : (∑' x, g x) - ∑ c ∈ C, a c * ∑' x, u c x = ∑' x, (g x - ∑ c ∈ C, a c * u c x) := by
    rw [hg.tsum_sub hsu, Summable.tsum_finsetSum fun c hc => (hu c hc).mul_left (a c)]
    simp only [tsum_mul_left]
  have e2 : δ * ∑ c ∈ C, ∑' x, w c x = ∑' x, δ * ∑ c ∈ C, w c x := by
    rw [tsum_mul_left, Summable.tsum_finsetSum hw]
  rw [e1, e2]
  have hn : Summable fun x => ‖g x - ∑ c ∈ C, a c * u c x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => by simpa using h x) hsw
  calc _ = ‖∑' x, (g x - ∑ c ∈ C, a c * u c x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' x, ‖g x - ∑ c ∈ C, a c * u c x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := hn.tsum_le_tsum (fun x => by simpa using h x) hsw

variable {F : Type} [Field F] [NumberField F]

def Claim (θ : ℝ →+* Ainf F) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (ι : Type) [Fintype ι]
    (S : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ (I : Ideal (𝓞 F)), I ≠ ⊥ → (∀ v ∈ S, ¬ I ≤ v.asIdeal) → ∀ (x0 : ι → F) (φ : (ι → Ainf F) → ℝ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ), Continuous φ → HasCompactSupport φ →
    (∀ v ∈ S, Continuous (ψ v) ∧ HasCompactSupport (ψ v)) →
    (∀ ε : ℝ, 0 < ε → Summable fun x : cosetOff S I x0 => term θ S φ ψ ε x.1) ∧
    Tendsto (fun ε : ℝ => ε ^ (Module.finrank ℚ F * Fintype.card ι) * ∑' x : cosetOff S I x0, term θ S φ ψ ε x.1)
      (𝓝[>] 0) (𝓝 (((Ideal.absNorm I : ℝ) ^ Fintype.card ι)⁻¹ *
        ((∫ y, φ y ∂(Measure.pi fun _ => li)) * ∏ v ∈ S, ∫ y, ψ v y ∂(Measure.pi fun _ => lam v))))

theorem claim_empty (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F) (hθ : Continuous θ) (li : Measure (Ainf F)) (hli : IsStdInf li)
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)) (ι : Type) [Fintype ι] : Claim θ li lam ι ∅ := by
  intro I hI _ x0 φ ψ hφ hc _
  rw [GlobalTheory.T.coset_empty_places_lattice]
  have := GlobalTheory.T.lattice_coset_scaled_riemann_sum F hF θ hθ li hli ι I hI x0 φ hφ hc
  simpa [term] using this

theorem mul_pow_prime {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {I : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hc : ∀ w ∈ S, ¬ I ≤ w.asIdeal) (k : ℕ) :
    I * v.asIdeal ^ k ≠ ⊥ ∧ ∀ w ∈ S, ¬ I * v.asIdeal ^ k ≤ w.asIdeal := by
  refine ⟨mul_ne_zero hI (pow_ne_zero _ v.ne_bot), fun w hw h => ?_⟩
  rcases w.isPrime.mul_le.1 h with h | h
  · exact hc w hw h
  · have h1 := w.isPrime.le_of_pow_le h
    have h2 : v.asIdeal = w.asIdeal := v.isMaximal.eq_of_le w.isPrime.ne_top h1
    exact hv ((HeightOneSpectrum.ext h2) ▸ hw)

abbrev yV {ι : Type} (v : HeightOneSpectrum (𝓞 F)) (x : ι → F) : ι → Fv F v := fun i => algebraMap F (Fv F v) (x i)

theorem term_insert {ι : Type} (θ : ℝ →+* Ainf F) {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (φ : (ι → Ainf F) → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) :
    term θ (insert v S) φ ψ ε x = ψ v (yV v x) * term θ S φ ψ ε x := by
  simp only [term, Finset.prod_insert hv, yV]
  ring

theorem term_abs {ι : Type} (θ : ℝ →+* Ainf F) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (φ : (ι → Ainf F) → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε : ℝ) (x : ι → F) :
    term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x = |term θ S φ ψ ε x| := by
  simp only [term, abs_mul, Finset.abs_prod]

theorem indicator_box {ι : Type} {A A' : Set (ι → F)} {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {c : ι → Fv F v}
    (h : ∀ x : ι → F, (x ∈ A ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ A') (f : (ι → F) → ℝ) :
    (A.indicator fun x => boxInd v k c (yV v x) * f x) = A'.indicator f := by
  funext x
  by_cases hb : ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k
  · by_cases hA : x ∈ A
    · have hA' := (h x).1 ⟨hA, hb⟩
      simp [Set.indicator, hA, hA', boxInd, yV, hb]
    · have hA' : x ∉ A' := fun e => hA ((h x).2 e).1
      simp [Set.indicator, hA, hA']
  · have hA' : x ∉ A' := fun e => hb ((h x).2 e).2
    have hz : boxInd v k c (yV v x) = 0 := by simp only [boxInd, yV]; rw [if_neg hb]
    simp [Set.indicator, hA', hz]

theorem est {ι : Type} (θ : ℝ →+* Ainf F) {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (φ : (ι → Ainf F) → ℝ) (ψ : ∀ v : HeightOneSpectrum (𝓞 F), (ι → Fv F v) → ℝ) (ε δ : ℝ) (hδ : 0 ≤ δ) {A : Set (ι → F)}
    {k : ℕ} (C : Finset (ι → Fv F v)) (A' : (ι → Fv F v) → Set (ι → F))
    (hA : ∀ c ∈ C, ∀ x : ι → F, (x ∈ A ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔ x ∈ A' c)
    (hap : ∀ y, |ψ v y - ∑ c ∈ C, ψ v c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y)
    (hs : ∀ c ∈ C, Summable fun x : A' c => term θ S φ ψ ε x.1)
    (hs' : ∀ c ∈ C, Summable fun x : A' c => term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x.1) :
    Summable (fun x : A => term θ (insert v S) φ ψ ε x.1) ∧
      |(∑' x : A, term θ (insert v S) φ ψ ε x.1) - ∑ c ∈ C, ψ v c * ∑' x : A' c, term θ S φ ψ ε x.1| ≤
        δ * ∑ c ∈ C, ∑' x : A' c, term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x.1 := by
  set f : (ι → F) → ℝ := term θ S φ ψ ε with hf
  set f' : (ι → F) → ℝ := term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε with hf'
  set u : (ι → Fv F v) → (ι → F) → ℝ := fun c => (A' c).indicator f with hu
  set w : (ι → Fv F v) → (ι → F) → ℝ := fun c => (A' c).indicator f' with hw
  have key : ∀ x, |A.indicator (fun x => term θ (insert v S) φ ψ ε x) x - ∑ c ∈ C, ψ v c * u c x| ≤ δ * ∑ c ∈ C, w c x := by
    intro x
    have e1 : ∀ c ∈ C, u c x = A.indicator (fun x => boxInd v k c (yV v x) * f x) x := fun c hc => by
      simp only [hu]
      exact (congrFun (indicator_box (hA c hc) f) x).symm
    have e2 : ∀ c ∈ C, w c x = A.indicator (fun x => boxInd v k c (yV v x) * f' x) x := fun c hc => by
      simp only [hw]
      exact (congrFun (indicator_box (hA c hc) f') x).symm
    rw [Finset.sum_congr rfl fun c hc => by rw [e1 c hc], Finset.sum_congr rfl e2]
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, term_insert θ hv]
      have e3 : ψ v (yV v x) * f x - ∑ c ∈ C, ψ v c * (boxInd v k c (yV v x) * f x) =
          (ψ v (yV v x) - ∑ c ∈ C, ψ v c * boxInd v k c (yV v x)) * f x := by
        rw [sub_mul, Finset.sum_mul]
        simp only [mul_assoc]
      rw [e3, abs_mul, ← Finset.sum_mul, hf', term_abs, ← hf, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hap _) (abs_nonneg _)
    · simp [Set.indicator_of_notMem hx]
  have hsu : ∀ c ∈ C, Summable (u c) := fun c hc => summable_subtype_iff_indicator.1 (hs c hc)
  have hsw : ∀ c ∈ C, Summable (w c) := fun c hc => summable_subtype_iff_indicator.1 (hs' c hc)
  obtain ⟨h1, h2⟩ := summable_of_close C (ψ v) u w hδ hsu hsw key
  refine ⟨summable_subtype_iff_indicator.2 h1, ?_⟩
  have t1 : ∑' x : A, term θ (insert v S) φ ψ ε x.1 = ∑' x, A.indicator (fun x => term θ (insert v S) φ ψ ε x) x :=
    tsum_subtype A _
  have t2 : ∀ c, ∑' x : A' c, f x.1 = ∑' x, u c x := fun c => tsum_subtype (A' c) f
  have t3 : ∀ c, ∑' x : A' c, f' x.1 = ∑' x, w c x := fun c => tsum_subtype (A' c) f'
  simp only [t1, t2, t3]
  exact h2

theorem claim_insert {θ : ℝ →+* Ainf F} {li : Measure (Ainf F)} {lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)}
    (hlam : ∀ v, IsStdV v (lam v)) {ι : Type} [Fintype ι] {S : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) (hS : Claim θ li lam ι S) : Claim θ li lam ι (insert v S) := by
  intro I hI hcop x0 φ ψ hφ hφc hψ
  have hcopS : ∀ w ∈ S, ¬ I ≤ w.asIdeal := fun w hw => hcop w (Finset.mem_insert_of_mem hw)
  have hcopv : ¬ I ≤ v.asIdeal := hcop v (Finset.mem_insert_self _ _)
  have hψS : ∀ w ∈ S, Continuous (ψ w) ∧ HasCompactSupport (ψ w) := fun w hw => hψ w (Finset.mem_insert_of_mem hw)
  obtain ⟨hψc, hψs⟩ := hψ v (Finset.mem_insert_self _ _)
  have hφa : Continuous fun y => |φ y| := hφ.abs
  have hφca : HasCompactSupport fun y => |φ y| := hφc.comp_left (g := fun t : ℝ => |t|) abs_zero
  have hψa : ∀ w ∈ S, Continuous (fun y => |ψ w y|) ∧ HasCompactSupport (fun y => |ψ w y|) := fun w hw =>
    ⟨(hψS w hw).1.abs, (hψS w hw).2.comp_left (g := fun t : ℝ => |t|) abs_zero⟩
  obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.locally_constant_box_approximation F v (lam v) (hlam v) ι (ψ v) hψc hψs
  have hcell : ∀ (k : ℕ) (c : ι → Fv F v), ∃ x1 : ι → F, ∀ x : ι → F,
      (x ∈ cosetOff (insert v S) I x0 ∧ ∀ i, algebraMap F (Fv F v) (x i) - c i ∈ ballV v k) ↔
        x ∈ cosetOff S (I * v.asIdeal ^ k) x1 := fun k c => GlobalTheory.T.coset_congruence_refinement F ι S v hv I hI hcopv k x0 c
  choose x1 hx1 using hcell
  have hJ := fun k => mul_pow_prime hv hI hcopS k
  have hP := fun (k : ℕ) (c : ι → Fv F v) => hS _ (hJ k).1 (hJ k).2 (x1 k c) φ ψ hφ hφc hψS
  have hQ := fun (k : ℕ) (c : ι → Fv F v) => hS _ (hJ k).1 (hJ k).2 (x1 k c) (fun y => |φ y|) (fun w y => |ψ w y|) hφa hφca hψa
  have hest := fun (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) (C : Finset (ι → Fv F v))
      (hap : ∀ y, |ψ v y - ∑ c ∈ C, ψ v c * boxInd v k c y| ≤ δ * ∑ c ∈ C, boxInd v k c y) (ε : ℝ) (hε : 0 < ε) =>
    est θ hv φ ψ ε δ hδ C (fun c => cosetOff S (I * v.asIdeal ^ k) (x1 k c)) (fun c _ => hx1 k c) hap
      (fun c _ => (hP k c).1 ε hε) (fun c _ => (hQ k c).1 ε hε)
  refine ⟨fun ε hε => ?_, ?_⟩
  · obtain ⟨k, C, h1, -, -⟩ := hB 1 one_pos
    exact (hest 1 zero_le_one k C h1 ε hε).1
  set N := Fintype.card ι
  set D := Module.finrank ℚ F * N
  set Nf : ℝ := ((Ideal.absNorm I : ℝ) ^ N)⁻¹ with hNf
  have hNf0 : 0 ≤ Nf := by positivity
  set M : ℝ := (∫ y, φ y ∂(Measure.pi fun _ => li)) * ∏ w ∈ S, ∫ y, ψ w y ∂(Measure.pi fun _ => lam w) with hM
  set M' : ℝ := (∫ y, |φ y| ∂(Measure.pi fun _ => li)) * ∏ w ∈ S, ∫ y, |ψ w y| ∂(Measure.pi fun _ => lam w) with hM'
  have hM'0 : 0 ≤ M' := mul_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (Finset.prod_nonneg fun _ _ => integral_nonneg fun _ => abs_nonneg _)
  have hnorm : ∀ k : ℕ, ((Ideal.absNorm (I * v.asIdeal ^ k) : ℝ) ^ N)⁻¹ =
      Nf * (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ N)⁻¹ := fun k => by
    rw [map_mul, map_pow, hNf]
    push_cast
    rw [mul_pow, mul_inv]
  have htarget : ((Ideal.absNorm I : ℝ) ^ N)⁻¹ * ((∫ y, φ y ∂(Measure.pi fun _ => li)) *
      ∏ w ∈ insert v S, ∫ y, ψ w y ∂(Measure.pi fun _ => lam w)) =
      Nf * M * ∫ y, ψ v y ∂(Measure.pi fun _ => lam v) := by
    rw [Finset.prod_insert hv, hM]
    ring
  rw [htarget]
  refine squeeze_of_approx (K := Nf * M' * B + Nf * |M| * B) (by positivity) fun δ hδ => ?_
  obtain ⟨k, C, h1, h2, h3⟩ := hB δ hδ
  set q : ℝ := (((Ideal.absNorm v.asIdeal : ℝ) ^ k) ^ N)⁻¹ with hq
  refine ⟨fun ε => ∑ c ∈ C, ψ v c * (ε ^ D * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c), term θ S φ ψ ε x.1),
    fun ε => ∑ c ∈ C, ε ^ D * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c),
      term θ S (fun y => |φ y|) (fun w y => |ψ w y|) ε x.1,
    ∑ c ∈ C, ψ v c * (Nf * q * M), ∑ c ∈ C, Nf * q * M', ?_, ?_, ?_, ?_, ?_⟩
  · refine tendsto_finsetSum _ fun c _ => Tendsto.const_mul _ ?_
    have := (hP k c).2
    rwa [hnorm] at this
  · refine tendsto_finsetSum _ fun c _ => ?_
    have := (hQ k c).2
    rwa [hnorm] at this
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (0 : ℝ) < ε := hε
    have h4 := (hest δ hδ.le k C h1 ε hε0).2
    have hp : 0 ≤ ε ^ D := by positivity
    have e1 : ε ^ D * (∑' x : cosetOff (insert v S) I x0, term θ (insert v S) φ ψ ε x.1) -
        ∑ c ∈ C, ψ v c * (ε ^ D * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c), term θ S φ ψ ε x.1) =
        ε ^ D * ((∑' x : cosetOff (insert v S) I x0, term θ (insert v S) φ ψ ε x.1) -
          ∑ c ∈ C, ψ v c * ∑' x : cosetOff S (I * v.asIdeal ^ k) (x1 k c), term θ S φ ψ ε x.1) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1, abs_mul, abs_of_nonneg hp, ← Finset.mul_sum, mul_left_comm]
    exact mul_le_mul_of_nonneg_left h4 hp
  · have e1 : ∑ c ∈ C, ψ v c * (Nf * q * M) = Nf * M * ∑ c ∈ C, ψ v c * q := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [e1, ← mul_sub, abs_mul, abs_mul, abs_of_nonneg hNf0, abs_sub_comm]
    calc Nf * |M| * _ ≤ Nf * |M| * (δ * B) := by gcongr
      _ ≤ δ * (Nf * M' * B + Nf * |M| * B) := by
        have : 0 ≤ δ * (Nf * M' * B) := by positivity
        nlinarith
  · rw [Finset.sum_const, nsmul_eq_mul]
    have e1 : (C.card : ℝ) * (Nf * q * M') = Nf * M' * ((C.card : ℝ) * q) := by ring
    rw [e1]
    have h5 : Nf * M' * ((C.card : ℝ) * q) ≤ Nf * M' * B := by gcongr
    have h6 : 0 ≤ Nf * |M| * B := by positivity
    linarith

theorem equi : PositivityTheory.Rg.Mass.Equi := by
  intro F _ _ hF θ hθ li lam hli hlam ι _ S φ ψ hφ hφc hψ
  have hc : Claim θ li lam ι S := by
    induction S using Finset.induction_on with
    | empty => exact claim_empty hF θ hθ li hli lam ι
    | insert v S hv ih => exact claim_insert hlam hv (ih fun w hw => hψ w (Finset.mem_insert_of_mem hw))
  have h := (hc ⊤ top_ne_bot (fun w _ h => w.isPrime.ne_top (top_le_iff.1 h)) 0 φ ψ hφ hφc hψ).2
  rw [GlobalTheory.T.coset_unit_ideal_integral] at h
  simp only [term, Ideal.absNorm_top, Nat.cast_one, one_pow, inv_one, one_mul] at h
  exact h

end GlobalTheory.CompanionTheory.Equi

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquidistributionStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equidistribution : Equi := by
  first | exact @GlobalTheory.CompanionTheory.Equi.equi | exact GlobalTheory.CompanionTheory.Equi.equi | (intros; apply GlobalTheory.CompanionTheory.Equi.equi <;> assumption)
end
