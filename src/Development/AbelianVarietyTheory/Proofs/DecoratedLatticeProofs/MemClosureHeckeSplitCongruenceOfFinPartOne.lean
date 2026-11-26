module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetNormOne
noncomputable section

open NumberField IsDedekindDomain Topology Filter

namespace GlobalTheory.HeckeSplitAll.Approx

variable {F : Type} [Field F] [NumberField F]

theorem norm_alg_inf (w : InfinitePlace F) (x : F) : ‖algebraMap F w.Completion x‖ = w x := by
  rw [AbsoluteValue.Completion.algebraMap_def, AbsoluteValue.Completion.norm_coe]
  rfl

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (natCast_mem _ m)

theorem norm_int_le_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v o)

theorem norm_int_eq_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) (ho : o ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ = 1 := by
  refine le_antisymm (norm_int_le_one v o) (not_lt.1 fun h => ho ?_)
  rw [Valued.toNormedField.norm_lt_one_iff] at h
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v o
  rw [show algebraMap F (v.adicCompletion F) (o : F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F o) from rfl,
    e] at h
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v o).1 h

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  have h := (algebraMap F (v.adicCompletion F)).injective.ne (Nat.cast_ne_zero.2 hm : (m : F) ≠ 0)
  rwa [map_natCast, map_zero] at h

theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v (c : 𝓞 F)
  rw [map_natCast, map_natCast] at e
  rw [e]
  exact hval

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h2 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x⁻¹).2
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
  obtain ⟨ha, hb⟩ := hv
  have ha' : ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := (norm_le_one_iff_int v _).2 ha
  have hb' : ‖algebraMap F (v.adicCompletion F) x⁻¹‖ ≤ 1 := (norm_le_one_iff_int v _).2 hb
  rw [map_inv₀, norm_inv] at hb'
  have hpos : 0 < ‖algebraMap F (v.adicCompletion F) x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
  have hm := mul_inv_cancel₀ hpos.ne'
  refine le_antisymm ha' ?_
  nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hb')]

theorem exists_nat_small (x : F) (hx : x ≠ 0) : ∃ P : ℕ, P ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖algebraMap F (v.adicCompletion F) x‖ ≠ 1 → ‖(P : v.adicCompletion F)‖ < 1 := by
  classical
  obtain ⟨B, hB⟩ := exists_finset_norm_one x hx
  refine ⟨∏ v ∈ B, Ideal.absNorm v.asIdeal, ?_, fun v hv => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  · exact norm_natCast_lt_one v _ (Finset.dvd_prod_of_mem _ (by_contra fun h => hv (hB v h)))

theorem exists_int_near (F : Type) [Field F] [NumberField F] : ∃ C : ℝ, 0 < C ∧ ∀ t : InfiniteAdeleRing F,
    ∃ o : 𝓞 F, ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o : F) - t w‖ < C := by
  classical
  set b := integralBasis F with hb
  refine ⟨1 + ∑ w : InfinitePlace F, ∑ i, w (b i), by positivity, fun t => ?_⟩
  have hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub
        continuous_const).norm) continuous_const
  obtain ⟨f, hf⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen
    ⟨t, fun w => by
      show ‖t w - t w‖ < 1
      rw [sub_self, norm_zero]; exact one_pos⟩
  have hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < 1 := hf
  refine ⟨∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i, fun w => ?_⟩
  have e : ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f =
      ∑ i, (((⌊b.repr f i⌋ : ℚ) - b.repr f i : ℚ) : F) * b i := by
    conv_lhs => arg 2; rw [← b.sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) =
      algebraMap (𝓞 F) F (∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i) from rfl, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, ← hb, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  have h2 : ‖algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f)‖ ≤
      ∑ i, w (b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_alg_inf, map_mul]
    refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
    rw [← InfinitePlace.norm_embedding_eq, map_ratCast, Complex.norm_ratCast, ← Rat.cast_abs, ← Rat.cast_one, Rat.cast_le,
      abs_le]
    constructor <;> linarith [Int.floor_le (b.repr f i), Int.lt_floor_add_one (b.repr f i)]
  have h3 : ∑ i, w (b i) ≤ ∑ w : InfinitePlace F, ∑ i, w (b i) :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => ∑ i, w (b i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) (Finset.mem_univ w)
  have h4 := norm_add_le (algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f))
    (algebraMap F w.Completion f - t w)
  rw [map_sub, sub_add_sub_cancel, ← map_sub] at h4
  linarith [hf' w]


open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module in
open scoped nonZeroDivisors in
theorem exists_small_elt (v₀ : HeightOneSpectrum (𝓞 F)) (η : ℝ) (hη : 0 < η) :
    ∃ x : F, x ≠ 0 ∧ (∀ w : InfinitePlace F, w x < η) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := by
  classical
  let f : InfinitePlace F → NNReal := fun _ => ⟨η, hη.le⟩
  have hV : volume (convexBodyLT F f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hV0 : 0 < (volume (convexBodyLT F f)).toReal := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor F := by exact_mod_cast one_le_convexBodyLTFactor F
    refine mul_pos (by linarith) ?_
    rw [NNReal.coe_prod]
    exact Finset.prod_pos fun w _ => by rw [NNReal.coe_pow]; exact pow_pos hη _
  set B : ℝ := (volume (ZSpan.fundamentalDomain (latticeBasis F))).toReal * 2 ^ finrank ℝ (mixedSpace F) with hB
  have hq : (1 : ℝ) < Ideal.absNorm v₀.asIdeal := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
  have ht : Tendsto (fun k : ℕ => ((Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) ^ k * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hq)).mul_const B
    rwa [zero_mul] at this
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hV0)).exists
  have hI : ((v₀.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero k v₀.ne_bot)
  let J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 _ (inv_ne_zero hI)
  have h : minkowskiBound F J < volume (convexBodyLT F f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top F J).ne hV]
    refine lt_of_eq_of_lt ?_ hk
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, toReal_mul, toReal_mul, toReal_pow,
      ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hB]
    simp only [J, Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, toReal_ofNat]
    push_cast
    rw [inv_pow]
    ring
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt F J h
  refine ⟨a, hne, fun w => hlt w, fun v hv => ?_⟩
  obtain ⟨p, hp0, hpv⟩ : ∃ p ∈ v₀.asIdeal, p ∉ v.asIdeal := by
    by_contra hc
    push Not at hc
    exact hv (HeightOneSpectrum.ext (v₀.isMaximal.eq_of_le v.isPrime.ne_top hc).symm)
  have hm : a * algebraMap (𝓞 F) F (p ^ k) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← inv_mul_cancel₀ hI]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.pow_mem_pow hp0 k))
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  have h1 := norm_int_le_one v o
  rw [show (o : F) = algebraMap (𝓞 F) F o from rfl, ho, map_mul, norm_mul, map_pow, map_pow, norm_pow] at h1
  have h2 := norm_int_eq_one v p hpv
  rw [show (p : F) = algebraMap (𝓞 F) F p from rfl] at h2
  rwa [h2, one_pow, mul_one] at h1

theorem strong_approx (v₀ : HeightOneSpectrum (𝓞 F)) (t : InfiniteAdeleRing F) (s : FiniteAdeleRing (𝓞 F) F)
    (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : F, c ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion c - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) c - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hM)
  obtain ⟨u, hu⟩ := PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_approx_adele
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * s)
  obtain ⟨C, hC, hCt⟩ := exists_int_near F
  obtain ⟨x, hx0, hxw, hxv⟩ := exists_small_elt v₀ (ε / (M * (C + 1))) (by positivity)
  obtain ⟨o, ho⟩ := hCt fun w => (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)
  have key : ∀ o' : 𝓞 F, (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o' : F) -
      (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)‖ < C + 1) →
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (M * u + M * x * o') - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
    intro o' ho'
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · have h0 : algebraMap F w.Completion (M * x) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero hMF hx0)
      have e : algebraMap F w.Completion (M * u + M * x * o') - t w = algebraMap F w.Completion (M * x) *
          (algebraMap F w.Completion (o' : F) -
            (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)) := by
        rw [map_add (f := _), map_mul _ (M * x), mul_sub, mul_div_cancel₀ _ h0]; ring
      rw [e, norm_mul, norm_alg_inf, map_mul, InfinitePlace.map_natCast]
      calc _ ≤ (M * w x) * (C + 1) := mul_le_mul_of_nonneg_left (ho' w).le (by positivity)
        _ < (M * (ε / (M * (C + 1)))) * (C + 1) := by gcongr; exact hxw w
        _ = ε := by field_simp
    · have h0 := nat_ne_zero_fin v hM
      have hu' : ‖algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u‖ ≤ 1 :=
        (norm_le_one_iff_int v _).2 (hu v)
      have e : algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v = (M : v.adicCompletion F) *
          (-(algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u) +
            algebraMap F (v.adicCompletion F) x * algebraMap F (v.adicCompletion F) (o' : F)) := by
        simp only [map_add (f := _), map_mul, map_inv₀, map_natCast]
        field_simp
        ring
      rw [e, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
      · rwa [norm_neg]
      · rw [norm_mul]; exact mul_le_one₀ (hxv v hv) (norm_nonneg _) (norm_int_le_one v o')
  by_cases hc : (M : F) * u + M * x * o = 0
  · refine ⟨M * u + M * x * (o + 1 : 𝓞 F), ?_, key (o + 1) fun w => ?_⟩
    · have : (M : F) * u + M * x * (o + 1 : 𝓞 F) = M * x := by push_cast; linear_combination hc
      rw [this]; exact mul_ne_zero hMF hx0
    · have h1 := norm_add_le (1 : w.Completion) (algebraMap F w.Completion (o : F) -
        (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x))
      have e : ((o + 1 : 𝓞 F) : F) = 1 + o := by push_cast; ring
      rw [e, map_add (f := _), map_one, add_sub_assoc]
      rw [norm_one] at h1
      linarith [ho w]
  · exact ⟨_, hc, key o fun w => (ho w).trans (lt_add_one C)⟩

end GlobalTheory.HeckeSplitAll.Approx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOne
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Topology Filter
open Formalism.IndefR.Fin.U1 hiding norm_nat_le_one norm_le_one_iff_int nat_ne_zero_fin
open GlobalTheory.HeckeSplitAll.Approx
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeSplitAll

section Local

variable {F : Type} [Field F] [NumberField F]

def GoodAt (N : ℕ) (Δ α β : F) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ‖algebraMap F (v.adicCompletion F) α - 1‖ ≤ ‖(N : v.adicCompletion F)‖ ∧
  ‖algebraMap F (v.adicCompletion F) β‖ ≤ ‖(N : v.adicCompletion F)‖ ∧
  ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ = 1

theorem norm_eq_one_of_sub_lt {K : Type*} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x - 1‖ < 1) :
    ‖x‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x - 1) (y := 1) (by rw [norm_one]; exact h.ne)
  rw [sub_add_cancel, norm_one, max_eq_right h.le] at this
  exact this

theorem norm_le_one_of_sub_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x : K} (h : ‖x - 1‖ ≤ 1) :
    ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - 1) 1
  rw [sub_add_cancel, norm_one] at this
  exact this.trans (max_le h le_rfl)

theorem unit_or_square (v : HeightOneSpectrum (𝓞 F)) (Δ a b : v.adicCompletion F)
    (h2 : ‖(2 : v.adicCompletion F)‖ = 1) (hΔ : ‖Δ‖ = 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hab : ‖a‖ = 1 ∨ ‖b‖ = 1)
    (hn0 : a * a - Δ * (b * b) ≠ 0) (hn : ‖a * a - Δ * (b * b)‖ ≠ 1) : ∃ s, s * s = Δ := by
  have e1 : ‖a * a‖ = ‖a‖ * ‖a‖ := norm_mul _ _
  have e2 : ‖Δ * (b * b)‖ = ‖b‖ * ‖b‖ := by rw [norm_mul, norm_mul, hΔ, one_mul]
  have ha0 := norm_nonneg a
  have hb0 := norm_nonneg b
  have hab' : ‖a‖ = 1 ∧ ‖b‖ = 1 := by
    by_contra hc
    apply hn
    rcases hab with h | h
    · have hb1 : ‖b‖ < 1 := lt_of_le_of_ne hb fun h' => hc ⟨h, h'⟩
      rw [norm_sub_eq_max v (by rw [e1, e2, h]; nlinarith), e1, e2, h, max_eq_left (by nlinarith), one_mul]
    · have ha1 : ‖a‖ < 1 := lt_of_le_of_ne ha fun h' => hc ⟨h', h⟩
      rw [norm_sub_eq_max v (by rw [e1, e2, h]; nlinarith), e1, e2, h, max_eq_right (by nlinarith), one_mul]
  have hle : ‖a * a - Δ * (b * b)‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg, e1, e2, hab'.1, hab'.2]; simp
  refine sq_of_nonint v Δ ((a * a + Δ * (b * b)) / (a * a - Δ * (b * b))) (2 * a * b / (a * a - Δ * (b * b))) h2 hΔ
    ?_ (Or.inr ?_)
  · rw [div_mul_div_comm, div_mul_div_comm, ← mul_div_assoc, div_sub_div_same,
      div_eq_one_iff_eq (mul_ne_zero hn0 hn0)]
    ring
  · rw [norm_div, norm_mul, norm_mul, h2, hab'.1, hab'.2, one_mul, one_mul,
      one_lt_div (norm_pos_iff.2 hn0)]
    exact lt_of_le_of_ne hle hn

theorem exists_pair (v₀ : HeightOneSpectrum (𝓞 F)) (N : ℕ) (hN : N ≠ 0) (Δ : 𝓞 F) (hΔ : (Δ : F) ≠ 0)
    (hns : ∀ α β : F, α ≠ 0 → α * α - Δ * (β * β) ≠ 0) (a b : InfiniteAdeleRing F) (ε : ℝ) (hε : 0 < ε) :
    ∃ α β : F, α ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion α - a w‖ < ε) ∧
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion β - b w‖ < ε) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∉ T, GoodAt N (Δ : F) α β v) ∧
        ∀ v ∈ T, v = v₀ ∨ ∃ s, s * s = algebraMap F (v.adicCompletion F) Δ := by
  classical
  obtain ⟨Q, hQ0, hQ⟩ := exists_nat_small (2 * (Δ : F)) (mul_ne_zero two_ne_zero hΔ)
  obtain ⟨α, hα0, hαw, hαv⟩ := strong_approx v₀ a 1 (N * Q) (mul_ne_zero hN hQ0) ε hε
  obtain ⟨P, hP0, hP⟩ := exists_nat_small α hα0
  let s : FiniteAdeleRing (𝓞 F) F := RestrictedProduct.mk
    (fun v => if ‖algebraMap F (v.adicCompletion F) α‖ = 1 then 0 else 1)
    (Eventually.of_forall fun v => by
      split_ifs
      · exact zero_mem _
      · exact one_mem _)
  obtain ⟨β, -, hβw, hβv⟩ := strong_approx v₀ b s (N * Q * P) (mul_ne_zero (mul_ne_zero hN hQ0) hP0) ε hε
  have hn0 := hns α β hα0
  obtain ⟨B, hB⟩ := exists_finset_norm_one _ hn0
  have key : ∀ v, v ≠ v₀ → ¬ GoodAt N (Δ : F) α β v →
      ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ ≠ 1 ∧
        ∃ s, s * s = algebraMap F (v.adicCompletion F) Δ := by
    intro v hv hg
    have h1 : ‖algebraMap F (v.adicCompletion F) α - 1‖ ≤ ‖((N * Q : ℕ) : v.adicCompletion F)‖ := hαv v hv
    have h2 : ‖algebraMap F (v.adicCompletion F) β -
      (if ‖algebraMap F (v.adicCompletion F) α‖ = 1 then 0 else 1)‖ ≤ ‖((N * Q * P : ℕ) : v.adicCompletion F)‖ :=
      hβv v hv
    simp only [Nat.cast_mul, norm_mul] at h1 h2
    have hN1 := norm_nat_le_one v N
    have hQ1 := norm_nat_le_one v Q
    have hP1 := norm_nat_le_one v P
    have hN0 := norm_nonneg (N : v.adicCompletion F)
    have hQ0' := norm_nonneg (Q : v.adicCompletion F)
    have hP0' := norm_nonneg (P : v.adicCompletion F)
    have hΔ1 := norm_int_le_one v Δ
    have hNQ : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ ≤ ‖(N : v.adicCompletion F)‖ :=
      mul_le_of_le_one_right hN0 hQ1
    have hNQP : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ * ‖(P : v.adicCompletion F)‖ ≤
        ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ := mul_le_of_le_one_right (by positivity) hP1
    by_cases hlt : ‖(N : v.adicCompletion F)‖ * ‖(Q : v.adicCompletion F)‖ < 1
    · exfalso
      have ha := norm_eq_one_of_sub_lt (h1.trans_lt hlt)
      rw [if_pos ha, sub_zero] at h2
      refine hg ⟨h1.trans hNQ, h2.trans (hNQP.trans hNQ), ?_⟩
      have hb : ‖algebraMap F (v.adicCompletion F) β‖ < 1 := (h2.trans hNQP).trans_lt hlt
      have hb0 := norm_nonneg (algebraMap F (v.adicCompletion F) β)
      have hlt2 : ‖algebraMap F (v.adicCompletion F) Δ *
          (algebraMap F (v.adicCompletion F) β * algebraMap F (v.adicCompletion F) β)‖ < 1 := by
        rw [norm_mul, norm_mul]
        exact (mul_le_of_le_one_left (by positivity) hΔ1).trans_lt (by nlinarith)
      simp only [map_sub, map_mul]
      rw [norm_sub_eq_max v (by rw [norm_mul, ha, one_mul]; exact hlt2.ne'), norm_mul, ha, one_mul,
        max_eq_left hlt2.le]
    · have hN' : ‖(N : v.adicCompletion F)‖ = 1 := le_antisymm hN1 (by linarith)
      have hQ' : ‖algebraMap F (v.adicCompletion F) (2 * (Δ : F))‖ = 1 := by
        by_contra hc
        have := hQ v hc
        rw [hN'] at hlt
        linarith
      rw [map_mul, map_ofNat, norm_mul] at hQ'
      have h21 : ‖(2 : v.adicCompletion F)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one v 2
      have h20 := norm_nonneg (2 : v.adicCompletion F)
      have hΔ0 := norm_nonneg (algebraMap F (v.adicCompletion F) Δ)
      have ha : ‖algebraMap F (v.adicCompletion F) α‖ ≤ 1 := norm_le_one_of_sub_le (h1.trans (hNQ.trans hN1))
      have hb : ‖algebraMap F (v.adicCompletion F) β‖ ≤ 1 ∧
          (‖algebraMap F (v.adicCompletion F) α‖ = 1 ∨ ‖algebraMap F (v.adicCompletion F) β‖ = 1) := by
        by_cases hc : ‖algebraMap F (v.adicCompletion F) α‖ = 1
        · rw [if_pos hc, sub_zero] at h2
          exact ⟨h2.trans (hNQP.trans (hNQ.trans hN1)), Or.inl hc⟩
        · rw [if_neg hc] at h2
          have := norm_eq_one_of_sub_lt (h2.trans_lt
            ((mul_le_of_le_one_left hP0' (hNQ.trans hN1)).trans_lt (hP v hc)))
          exact ⟨this.le, Or.inr this⟩
      have hn : ‖algebraMap F (v.adicCompletion F) (α * α - Δ * (β * β))‖ ≠ 1 := fun h =>
        hg ⟨h1.trans hNQ, hN' ▸ hb.1, h⟩
      refine ⟨hn, unit_or_square v _ _ _ (le_antisymm h21 (by nlinarith)) (le_antisymm hΔ1 (by nlinarith)) ha hb.1 hb.2
        ?_ ?_⟩
      · have := (map_ne_zero (algebraMap F (v.adicCompletion F))).2 hn0
        simpa only [map_sub, map_mul] using this
      · simpa only [map_sub, map_mul] using hn
  refine ⟨α, β, hα0, hαw, hβw, (insert v₀ B).filter fun v => ¬ GoodAt N (Δ : F) α β v, fun v hv => ?_, fun v hv => ?_⟩
  · by_contra hg
    rw [Finset.mem_filter, Finset.mem_insert, not_and] at hv
    have h := not_or.1 (mt hv (not_not.2 hg))
    exact (key v h.1 hg).1 (hB v h.2)
  · by_cases h : v = v₀
    · exact Or.inl h
    · exact Or.inr (key v h (Finset.mem_filter.1 hv).2).2

end Local

section Cut

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

def cut {ε : S} (hε : ε * ε = ε) (x : Rˣ) : Rˣ where
  val := algebraMap S R ε * x + (1 - algebraMap S R ε)
  inv := algebraMap S R ε * (x⁻¹ : Rˣ) + (1 - algebraMap S R ε)
  val_inv := by
    have h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε := by rw [← map_mul, hε]
    linear_combination algebraMap S R ε ^ 2 * x.mul_inv + (2 - (x : R) - (x⁻¹ : Rˣ)) * h
  inv_val := by
    have h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε := by rw [← map_mul, hε]
    linear_combination algebraMap S R ε ^ 2 * x.mul_inv + (2 - (x : R) - (x⁻¹ : Rˣ)) * h

theorem idem_compl {ε : S} (hε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε

theorem cut_val {ε : S} (hε : ε * ε = ε) (x : Rˣ) :
    (cut hε x : R) = algebraMap S R ε * x + (1 - algebraMap S R ε) := rfl

theorem cut_inv {ε : S} (hε : ε * ε = ε) (x : Rˣ) :
    (((cut hε x)⁻¹ : Rˣ) : R) = algebraMap S R ε * (x⁻¹ : Rˣ) + (1 - algebraMap S R ε) := rfl

theorem cut_mul {ε : S} (hε : ε * ε = ε) (x : Rˣ) : cut hε x * cut (idem_compl hε) x = x := by
  apply Units.ext
  have h : algebraMap S R ε * algebraMap S R ε = algebraMap S R ε := by rw [← map_mul, hε]
  rw [Units.val_mul, cut_val, cut_val, map_sub, map_one]
  linear_combination (2 * (x : R) - x * x - 1) * h

theorem map_mkE {F E : Type} [Field F] [Field E] [Algebra F E] {R R' : Type} [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (δ : E) (a b : R) :
    (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom (mkE (F := F) δ R a b) =
      mkE (F := F) δ R' (φ a) (φ b) := by
  simp [mkE]

theorem mkE_sub_one {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] (δ : E)
    (N : ℕ) (a b za zb : R) (ha : a - 1 = N * za) (hb : b = N * zb) :
    mkE (F := F) δ R a b - 1 = (N : R ⊗[F] E) * mkE (F := F) δ R za zb := by
  rw [← mkE_one (F := F) δ R, mkE_sub, sub_zero, ha, hb, ← smul_mkE, map_natCast]

theorem af_sub_one {F : Type} [Field F] [NumberField F] (y : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    (y - 1) v = y v - 1 := rfl

end Cut

section Main

variable {D : D7}

theorem cut_pt (δ : D.host.E) (ε a b : AF D.host.F) :
    algebraMap (AF D.host.F) (AE D) ε * pt δ a b + (1 - algebraMap (AF D.host.F) (AE D) ε) =
      pt δ (ε * a + (1 - ε)) (ε * b) := by
  rw [← map_one (algebraMap (AF D.host.F) (AE D)), ← map_sub, pt, pt, smul_mkE,
    algebraMap_eq_mkE δ (AF D.host.F) (1 - ε), mkE_add, add_zero]

theorem finPart_pt (δ : D.host.E) (a b : AF D.host.F) :
    finPart D (pt δ a b) = mkE (F := D.host.F) δ (Af D.host.F) a.2 b.2 :=
  map_mkE (sndA D.host.F) δ a b

theorem infPart_pt (δ : D.host.E) (a b : AF D.host.F) :
    infPart D (pt δ a b) = mkE (F := D.host.F) δ (Ainf D.host.F) a.1 b.1 :=
  map_mkE (fstA D.host.F) δ a b

theorem tendsto_pt (δ : D.host.E) {A B : ℕ → AF D.host.F} {a b : AF D.host.F} (hA : Tendsto A atTop (𝓝 a))
    (hB : Tendsto B atTop (𝓝 b)) : Tendsto (fun k => pt δ (A k) (B k)) atTop (𝓝 (pt δ a b)) := by
  have := ((continuous_pt δ).tendsto (a, b)).comp (hA.prodMk_nhds hB)
  simpa only [Function.comp_def] using this

theorem mkE_mem_intAE (δ : 𝓞 D.host.E) (a b : Af D.host.F) (ha : ∀ v, ‖a v‖ ≤ 1) (hb : ∀ v, ‖b v‖ ≤ 1) :
    mkE (F := D.host.F) (δ : D.host.E) (Af D.host.F) a b ∈ intAE D :=
  add_mem (AddSubgroup.subset_closure ⟨a, fun v => (norm_le_one_iff_int v _).1 (ha v), 1, rfl⟩)
    (AddSubgroup.subset_closure ⟨b, fun v => (norm_le_one_iff_int v _).1 (hb v), δ, rfl⟩)

theorem exists_div_nat {F : Type} [Field F] [NumberField F] (y : Af F) (N : ℕ) (hN : N ≠ 0)
    (hy : ∀ v, ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖) :
    ∃ z : Af F, (∀ v, ‖z v‖ ≤ 1) ∧ y = (N : Af F) * z := by
  refine ⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩
  · show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1
    have hN0 : 0 < ‖(N : v.adicCompletion F)‖ := norm_pos_iff.2 (nat_ne_zero_fin v hN)
    rw [map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]
    exact hy v
  · rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]

theorem mem_grpH_of_good (N : ℕ) (hN : N ≠ 0) (δ : 𝓞 D.host.E) (T : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    (∀ v ∈ T, ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v)) →
    ∀ (x : (AE D)ˣ) (a b a' b' : AF D.host.F), (x : AE D) = pt (δ : D.host.E) a b →
      ((x⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) a' b' → a.1 = 1 → b.1 = 0 →
      (∀ v ∉ T, ‖a.2 v - 1‖ ≤ ‖(N : v.adicCompletion D.host.F)‖ ∧ ‖b.2 v‖ ≤ ‖(N : v.adicCompletion D.host.F)‖ ∧
        ‖a'.2 v‖ ≤ 1 ∧ ‖b'.2 v‖ ≤ 1) → x ∈ grpH D N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro _ x a b a' b' hx hx' ha hb hg
    have hg' := fun v => hg v (Finset.notMem_empty v)
    refine Subgroup.subset_closure (Or.inr ⟨?_, ?_, ?_⟩)
    · rw [hx, infPart_pt, ha, hb, mkE_one]
    · obtain ⟨za, hza, ea⟩ := exists_div_nat (a.2 - 1) N hN fun v => by rw [af_sub_one]; exact (hg' v).1
      obtain ⟨zb, hzb, eb⟩ := exists_div_nat b.2 N hN fun v => (hg' v).2.1
      refine ⟨_, mkE_mem_intAE δ za zb hza hzb, ?_⟩
      rw [hx, finPart_pt]
      exact mkE_sub_one _ N _ _ _ _ ea eb
    · rw [hx', finPart_pt]
      exact mkE_mem_intAE δ _ _ (fun v => (hg' v).2.2.1) fun v => (hg' v).2.2.2
  | insert v T hvT ih =>
    intro hT x a b a' b' hx hx' ha hb hg
    obtain ⟨e, he, hee⟩ := hT v (Finset.mem_insert_self v T)
    rw [← cut_mul (epv_sq v) x]
    refine mul_mem (Subgroup.subset_closure (Or.inl (Or.inr ⟨e, he, ?_⟩))) ?_
    · have h : algebraMap (AF D.host.F) (AE D) (epv v) * algebraMap (AF D.host.F) (AE D) (epv v) =
          algebraMap (AF D.host.F) (AE D) (epv v) := by rw [← map_mul, epv_sq]
      rw [hee, cut_val]
      linear_combination ((x : AE D) - 1) * h
    · refine ih (fun w hw => hT w (Finset.mem_insert_of_mem hw)) _ _ _ _ _
        (by rw [cut_val, hx, cut_pt]) (by rw [cut_inv, hx', cut_pt]) ?_ ?_ fun w hw => ?_
      · simp only [finite_adele_fst_add, finite_adele_fst_mul, finite_adele_fst_sub, ha, epv_fst, finite_adele_fst_one]; ring
      · rw [finite_adele_fst_mul, hb, mul_zero]
      · simp only [finite_adele_snd_add, finite_adele_snd_mul, finite_adele_snd_sub, finite_adele_snd_one]
        by_cases hwv : w = v
        · subst hwv
          rw [epv_self]
          simp
        · rw [epv_ne hwv]
          simpa using hg w (by rw [Finset.mem_insert, not_or]; exact ⟨hwv, hw⟩)

theorem placeIdem_eq {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) : ε = epv v := by
  obtain ⟨α, rfl, h1, h2⟩ := h
  rw [epv, pairA_eq_iff]
  refine ⟨rfl, fa_ext fun w => ?_⟩
  by_cases hw : w = v
  · subst hw; rw [single_self]; exact h1
  · rw [single_ne _ hw]; exact h2 w hw

theorem exists_int_delta (D : D7) : ∃ (δ : 𝓞 D.host.E) (Δ : 𝓞 D.host.F), D.sp.cm.sig (δ : D.host.E) = -δ ∧
    (δ : D.host.E) ≠ 0 ∧ algebraMap D.host.F D.host.E Δ = δ * δ := by
  obtain ⟨δ0, h1, h2⟩ := exists_delta_D D
  obtain ⟨d, hd0, hd⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2
    (Algebra.IsAlgebraic.isAlgebraic δ0)).exists_integral_multiple
  have h3 : D.sp.cm.sig (d • δ0) = -(d • δ0) := by rw [map_zsmul, h1, smul_neg]
  obtain ⟨Δ, hΔ⟩ := exists_Delta D (d • δ0) h3
  have h4 : IsIntegral ℤ Δ :=
    (isIntegral_algebraMap_iff ).1 (hΔ ▸ hd.mul hd)
  exact ⟨⟨d • δ0, hd⟩, ⟨Δ, h4⟩, h3, smul_ne_zero hd0 h2, hΔ⟩

def epInf (F : Type) [Field F] [NumberField F] : AF F := pairA F 1 0

theorem epInf_sq (F : Type) [Field F] [NumberField F] : epInf F * epInf F = epInf F := by
  rw [epInf, pairA_mul, mul_one, mul_zero]

theorem exists_mem_grpH (N : ℕ) (hN : N ≠ 0) (δ : 𝓞 D.host.E) (Δ : 𝓞 D.host.F)
    (hδ : D.sp.cm.sig (δ : D.host.E) = -δ) (hδ0 : (δ : D.host.E) ≠ 0)
    (hΔ : algebraMap D.host.F D.host.E Δ = δ * δ) (α β : D.host.F) (hn : α * α - Δ * (β * β) ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hg : ∀ v ∉ T, GoodAt N (Δ : D.host.F) α β v)
    (hT : ∀ v ∈ T, ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) (epv v)) :
    ∃ g ∈ grpH D N,
      (g : AE D) = pt (δ : D.host.E) (pairA D.host.F (algebraMap _ _ α) 1) (pairA D.host.F (algebraMap _ _ β) 0) ∧
      ((g⁻¹ : (AE D)ˣ) : AE D) =
        pt (δ : D.host.E) (pairA D.host.F (algebraMap _ _ (α / (α * α - Δ * (β * β)))) 1)
          (pairA D.host.F (algebraMap _ _ (-β / (α * α - Δ * (β * β)))) 0) := by
  set n : D.host.F := α * α - Δ * (β * β) with hndef
  have hyy : (algebraMap D.host.F D.host.E α + algebraMap D.host.F D.host.E β * δ) *
      (algebraMap D.host.F D.host.E (α / n) + algebraMap D.host.F D.host.E (-β / n) * δ) = 1 := by
    have h0 : algebraMap D.host.F D.host.E n ≠ 0 := (map_ne_zero _).2 hn
    have h1 : algebraMap D.host.F D.host.E n = algebraMap D.host.F D.host.E α * algebraMap D.host.F D.host.E α -
        δ * δ * (algebraMap D.host.F D.host.E β * algebraMap D.host.F D.host.E β) := by
      rw [hndef, map_sub, map_mul, map_mul, map_mul, hΔ]
    rw [map_div₀, map_div₀, map_neg]
    field_simp
    rw [h1]; ring
  let y : D.host.Eˣ := ⟨_, _, hyy, by rw [mul_comm]; exact hyy⟩
  let Y : (AE D)ˣ := Units.map (incA D).toMonoidHom y
  have hY : Y ∈ grpH D N := Subgroup.subset_closure (Or.inl (Or.inl ⟨y, rfl⟩))
  have hY1 : (Y : AE D) = pt (δ : D.host.E) (algebraMap _ _ α) (algebraMap _ _ β) := incA_eq_pt _ α β
  have hY2 : ((Y⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) (algebraMap _ _ (α / n)) (algebraMap _ _ (-β / n)) :=
    incA_eq_pt _ _ _
  have e1 : ∀ c : D.host.F, epInf D.host.F * algebraMap _ _ c + (1 - epInf D.host.F) =
      pairA D.host.F (algebraMap _ _ c) 1 := fun c => by
    refine Prod.ext ?_ ?_
    · show 1 * algebraMap D.host.F (Ainf D.host.F) c + (1 - 1) = algebraMap D.host.F (Ainf D.host.F) c
      ring
    · show 0 * algebraMap D.host.F (Af D.host.F) c + (1 - 0) = 1
      ring
  have e2 : ∀ c : D.host.F, epInf D.host.F * algebraMap _ _ c = pairA D.host.F (algebraMap _ _ c) 0 := fun c => by
    refine Prod.ext ?_ ?_
    · show 1 * algebraMap D.host.F (Ainf D.host.F) c = algebraMap D.host.F (Ainf D.host.F) c
      ring
    · show 0 * algebraMap D.host.F (Af D.host.F) c = 0
      ring
  have e3 : ∀ (c : D.host.F) v, ((1 - epInf D.host.F) * algebraMap _ _ c + (1 - (1 - epInf D.host.F))).2 v =
      algebraMap D.host.F (v.adicCompletion D.host.F) c := fun c v => by
    show (1 - 0) * algebraMap D.host.F (v.adicCompletion D.host.F) c + (1 - (1 - 0)) = _
    ring
  have e4 : ∀ (c : D.host.F) v, ((1 - epInf D.host.F) * algebraMap _ _ c).2 v =
      algebraMap D.host.F (v.adicCompletion D.host.F) c := fun c v => by
    show (1 - 0) * algebraMap D.host.F (v.adicCompletion D.host.F) c = _
    ring
  have hx : cut (idem_compl (epInf_sq D.host.F)) Y ∈ grpH D N := by
    refine mem_grpH_of_good N hN δ T hT _ _ _ _ _ (by rw [cut_val, hY1, cut_pt]) (by rw [cut_inv, hY2, cut_pt])
      ?_ ?_ fun v hv => ?_
    · show (1 - 1) * algebraMap D.host.F (Ainf D.host.F) α + (1 - (1 - 1)) = 1
      ring
    · show (1 - 1) * algebraMap D.host.F (Ainf D.host.F) β = 0
      ring
    · obtain ⟨g1, g2, g3⟩ := hg v hv
      rw [e3, e4, e3, e4, map_div₀, map_div₀, norm_div, norm_div, g3, div_one, div_one, map_neg, norm_neg]
      exact ⟨g1, g2, norm_le_one_of_sub_le (g1.trans (norm_nat_le_one v N)), g2.trans (norm_nat_le_one v N)⟩
  refine ⟨cut (epInf_sq D.host.F) Y, ?_, by rw [cut_val, hY1, cut_pt, e1, e2], by rw [cut_inv, hY2, cut_pt, e1, e2]⟩
  rw [eq_mul_inv_of_mul_eq (cut_mul (epInf_sq D.host.F) Y)]
  exact mul_mem hY (inv_mem hx)

theorem mem_closure_grpH_of_finPart_eq_one (D : D7) (N : ℕ) (hN : 0 < N) (z : (AE D)ˣ)
    (hz : finPart D (z : AE D) = 1) : z ∈ closure (grpH D N : Set (AE D)ˣ) := by
  obtain ⟨δ, Δ, hδ, hδ0, hΔ⟩ := exists_int_delta D
  have hΔ0 : (Δ : D.host.F) ≠ 0 := by
    intro h; rw [h, map_zero] at hΔ; exact hδ0 (mul_self_eq_zero.mp hΔ.symm)
  have hns : ∀ α β : D.host.F, α ≠ 0 → α * α - Δ * (β * β) ≠ 0 := by
    intro α β hα h
    have hli := LinearIndependent.pair_iff.1 (linIndep_one_delta D.sp.cm.sig (δ : D.host.E) hδ hδ0)
    have h1 : (α • (1 : D.host.E) + β • (δ : D.host.E)) * (α • (1 : D.host.E) + (-β) • (δ : D.host.E)) = 0 := by
      have := congrArg (algebraMap D.host.F D.host.E) h
      rw [map_sub, map_mul, map_mul, map_mul, hΔ, map_zero] at this
      simp only [Algebra.smul_def, map_neg]
      linear_combination this
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact hα (hli _ _ h2).1
    · exact hα (hli _ _ h2).1
  obtain ⟨e₀, he₀⟩ := Formalism.IndefR.Fin.SplitChar.exists_splitIdem_D D
  obtain ⟨v₀, ε₀, hε₀, hee₀⟩ := he₀.2.2
  rw [placeIdem_eq hε₀] at hee₀
  obtain ⟨a, b, hab⟩ : ∃ a b, (z : AE D) = pt (δ : D.host.E) a b := ⟨_, _, (pt_co _ hδ hδ0 _).symm⟩
  obtain ⟨a', b', hab'⟩ : ∃ a b, ((z⁻¹ : (AE D)ˣ) : AE D) = pt (δ : D.host.E) a b :=
    ⟨_, _, (pt_co _ hδ hδ0 _).symm⟩
  have hz' : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    have := congrArg (finPart D) z.mul_inv
    rwa [map_mul, hz, one_mul, map_one] at this
  rw [hab, finPart_pt, ← mkE_one (F := D.host.F) (δ : D.host.E) (Af D.host.F)] at hz
  rw [hab', finPart_pt, ← mkE_one (F := D.host.F) (δ : D.host.E) (Af D.host.F)] at hz'
  obtain ⟨f1, f2⟩ := mkE_inj D.sp.cm.sig _ hδ hδ0 D.sp.cm.deg2 _ hz
  obtain ⟨f1', f2'⟩ := mkE_inj D.sp.cm.sig _ hδ hδ0 D.sp.cm.deg2 _ hz'
  have hmul := z.mul_inv
  rw [hab, hab', pt_mul _ _ hΔ, ← pt_one (δ : D.host.E)] at hmul
  obtain ⟨m1, m2⟩ := pt_inj _ hδ hδ0 hmul
  have hch := fun k : ℕ => exists_pair v₀ N hN.ne' Δ hΔ0 hns a.1 b.1 (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  choose α β hα0 hα hβ T hg hT using hch
  have hG := fun k => exists_mem_grpH N hN.ne' δ Δ hδ hδ0 hΔ (α k) (β k) (hns _ _ (hα0 k)) (T k) (hg k) fun v hv => by
    rcases hT k v hv with rfl | ⟨s, hs⟩
    · exact ⟨e₀, he₀, hee₀⟩
    · exact exists_splitIdem' _ hδ hδ0 _ hΔ v s hs
  choose g hgm hg1 hg2 using hG
  have tα : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (α k)) atTop (𝓝 (a.1 w)) := fun w =>
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hα k w).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tβ : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (β k)) atTop (𝓝 (b.1 w)) := fun w =>
    tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun k => (hβ k w).le)
      tendsto_one_div_add_atTop_nhds_zero_nat)
  have tinv : ∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (α k / (α k * α k - Δ * (β k * β k)))) atTop
      (𝓝 (a'.1 w)) ∧ Tendsto (fun k => algebraMap D.host.F w.Completion (-β k / (α k * α k - Δ * (β k * β k)))) atTop
      (𝓝 (b'.1 w)) := fun w => by
    have p1 : a.1 w * a'.1 w + algebraMap D.host.F w.Completion Δ * (b.1 w * b'.1 w) = 1 :=
      congrArg (fun x : AF D.host.F => x.1 w) m1
    have p2 : a.1 w * b'.1 w + b.1 w * a'.1 w = 0 := congrArg (fun x : AF D.host.F => x.1 w) m2
    have h0 : a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w) ≠ 0 :=
      left_ne_zero_of_mul_eq_one (b := a'.1 w * a'.1 w - algebraMap D.host.F w.Completion Δ * (b'.1 w * b'.1 w)) (by
        linear_combination (a.1 w * a'.1 w + algebraMap D.host.F w.Completion Δ * (b.1 w * b'.1 w) + 1) * p1 -
          algebraMap D.host.F w.Completion Δ * (a.1 w * b'.1 w + b.1 w * a'.1 w) * p2)
    have tn := ((tα w).mul (tα w)).sub (((tβ w).mul (tβ w)).const_mul (algebraMap D.host.F w.Completion Δ))
    have q1 : a'.1 w = a.1 w / (a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w)) := by
      rw [eq_div_iff h0]
      linear_combination a.1 w * p1 - algebraMap D.host.F w.Completion Δ * b.1 w * p2
    have q2 : b'.1 w = -b.1 w / (a.1 w * a.1 w - algebraMap D.host.F w.Completion Δ * (b.1 w * b.1 w)) := by
      rw [eq_div_iff h0]
      linear_combination a.1 w * p2 - b.1 w * p1
    rw [q1, q2]
    simp only [map_div₀, map_sub, map_mul, map_neg]
    exact ⟨(tα w).div tn h0, (tβ w).neg.div tn h0⟩
  have tpt : ∀ (c d : ℕ → D.host.F) (A B : AF D.host.F), A.2 = 1 → B.2 = 0 →
      (∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (c k)) atTop (𝓝 (A.1 w))) →
      (∀ w, Tendsto (fun k => algebraMap D.host.F w.Completion (d k)) atTop (𝓝 (B.1 w))) →
      Tendsto (fun k => pt (δ : D.host.E) (pairA D.host.F (algebraMap _ _ (c k)) 1)
        (pairA D.host.F (algebraMap _ _ (d k)) 0)) atTop (𝓝 (pt (δ : D.host.E) A B)) := by
    intro c d A B hA hB hc hd
    have t1 : Tendsto (fun k => pairA D.host.F (algebraMap _ _ (c k)) 1) atTop (𝓝 A) := by
      rw [← hA]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hc) tendsto_const_nhds
    have t2 : Tendsto (fun k => pairA D.host.F (algebraMap _ _ (d k)) 0) atTop (𝓝 B) := by
      rw [← hB]
      exact Tendsto.prodMk_nhds (tendsto_pi_nhds.2 hd) tendsto_const_nhds
    exact tendsto_pt _ t1 t2
  refine mem_closure_of_tendsto (f := g) (b := atTop) ?_ (Eventually.of_forall hgm)
  refine Units.isInducing_embedProduct.tendsto_nhds_iff.2 (Tendsto.prodMk_nhds ?_ ?_)
  · show Tendsto (fun k => (g k : AE D)) atTop (𝓝 (z : AE D))
    simp only [hg1, hab]
    exact tpt _ _ _ _ f1 f2 tα tβ
  · refine (MulOpposite.continuous_op.tendsto _).comp ?_
    show Tendsto (fun k => (((g k)⁻¹ : (AE D)ˣ) : AE D)) atTop (𝓝 ((z⁻¹ : (AE D)ˣ) : AE D))
    simp only [hg2, hab']
    exact tpt _ _ _ _ f1' f2' (fun w => (tinv w).1) fun w => (tinv w).2

end Main

end GlobalTheory.HeckeSplitAll

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemClosureHeckeSplitCongruenceOfFinPartOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_heckeSplitCongruence_of_finPart_one : ∀ (D : D7) (N : ℕ), 0 < N → ∀ z : (AE D)ˣ, finPart D (z : AE D) = 1 → z ∈ closure (GlobalTheory.HeckeSplitAll.grpH D N : Set (AE D)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | exact GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitAll.mem_closure_grpH_of_finPart_eq_one <;> assumption)
end
