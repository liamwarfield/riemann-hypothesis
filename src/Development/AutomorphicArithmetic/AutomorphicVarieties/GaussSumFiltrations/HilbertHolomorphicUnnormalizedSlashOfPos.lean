module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.HolKeep

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

def U (F : Type) [Field F] [NumberField F] : Set (InfinitePlace F → ℂ) := {z | ∀ v, 0 < (z v).im}

theorem cmp_det (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  simp [cmp, Matrix.GeneralLinearGroup.map_det]

def mob (h : GL (Fin 2) (InfinitePlace F → ℝ)) (z : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun v => num (cmp v h) (z v) / denom (cmp v h) (z v)

theorem mob_im_pos {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) (v) :
    0 < (mob h z v).im := by
  have hd : 0 < ((cmp v h).det : ℝ) := by
    rw [cmp_det]
    exact hh v
  have hzv : 0 < (z v).im := hz v
  show 0 < (num (cmp v h) (z v) / denom (cmp v h) (z v)).im
  rw [moebius_im]
  exact div_pos (mul_pos hd hzv) (normSq_denom_pos _ hzv.ne')

theorem mob_mapsTo {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) : Set.MapsTo (mob h) (U F) (U F) := by
  intro z hz
  show ∀ v, 0 < (mob h z v).im
  exact fun v => mob_im_pos hh hz v

theorem mob_diff (h : GL (Fin 2) (InfinitePlace F → ℝ)) : DifferentiableOn ℂ (mob h) (U F) := by
  rw [differentiableOn_pi]
  intro v z hz
  have hzv : (z v).im ≠ 0 := (hz v).ne'
  have hp : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => w v) z := differentiable_apply v z
  have hn : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => num (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  have hd : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => denom (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w => num (cmp v h) (w v) / denom (cmp v h) (w v)) z
  simp only [div_eq_mul_inv]
  exact hn.mul (hd.inv (denom_ne_zero_of_im _ hzv))

theorem act_eq {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) :
    act h (fun v => ofComplex (z v)) = fun v => ofComplex (mob h z v) := by
  funext v
  rw [act.eq_1, ofComplex_apply_of_im_pos (hz v), ofComplex_apply_of_im_pos (mob_im_pos hh hz v)]
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [cmp_det]; exact hh v)]
  rfl

theorem hilbertHolomorphic_unnormalizedSlash_of_pos (k : ℕ) {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {f : Hn F → ℂ} (hf : Hol f) :
    Hol (sl0 k h f) := by
  have hF : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f (fun v => ofComplex (z v))) (U F) := hf
  have hcomp := hF.comp (mob_diff h) (mob_mapsTo hh)
  have hden : DifferentiableOn ℂ
      (fun z : InfinitePlace F → ℂ => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k) (U F) := by
    intro z hz
    have hne : (∏ v, denom (cmp v h) (z v)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => denom_ne_zero_of_im _ (hz v).ne'
    have hpr : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => ∏ v, denom (cmp v h) (w v)) z := by
      simp only [denom]
      fun_prop
    exact ((hpr.inv hne).pow k).differentiableWithinAt
  show DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => sl0 k h f (fun v => ofComplex (z v))) (U F)
  refine (hden.mul hcomp).congr ?_
  intro z hz
  have hc : ∀ v, ((ofComplex (z v) : ℍ) : ℂ) = z v := fun v => by
    rw [ofComplex_apply_of_im_pos (hz v)]
  simp only [sl0.eq_1, act_eq hh hz, hc, Function.comp_apply, Pi.mul_apply]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Hol f → Hol g → Hol (f + g) ∧ Hol (c • f) ∧ Hol (f * g) ∧ Hol (1 : Hn F → ℂ) ∧ Hol (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Hol (sl0 k h f) ∧ Hol (sl k h f) := by
  intro F _ _ k f g c hf hg
  refine ⟨DifferentiableOn.add hf hg, DifferentiableOn.const_smul hf c, DifferentiableOn.mul hf hg,
    differentiableOn_const 1, differentiableOn_const 0, fun h hh => ⟨hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf, ?_⟩⟩
  exact DifferentiableOn.mul (differentiableOn_const _) (hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf)

end GlobalTheory.HilbertThetaSeries.HolKeep
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IsDelNeZeroCoprimeDenominatorsDifferentGenerator
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HilbertThetaSeries.DenP
variable {F : Type} [Field F] [NumberField F]

theorem val_nat (w : HeightOneSpectrum (𝓞 F)) (n : ℕ) : w.valuation F (n : F) = w.intValuation (n : 𝓞 F) := by
  rw [← map_natCast (algebraMap (𝓞 F) F) n, HeightOneSpectrum.valuation_of_algebraMap]

theorem isIntegral_iff_val (x : F) : IsIntegral ℤ x ↔ ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ 1 := by
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · have := w.valuation_le_one (K := F) (⟨x, h⟩ : 𝓞 F)
    exact this
  · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x h
    rw [← hr]; exact RingOfIntegers.isIntegral_coe r

theorem not_mem_of_coprime {p N : ℕ} (hc : N.Coprime p) {w : HeightOneSpectrum (𝓞 F)}
    (hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((N : ℕ) : 𝓞 F) ∉ w.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have h1 : ((u : 𝓞 F) * (N : 𝓞 F) + (v : 𝓞 F) * (p : 𝓞 F)) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) huv
    push_cast at this
    exact this
  have : (1 : 𝓞 F) ∈ w.asIdeal := by
    rw [← h1]; exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hN) (w.asIdeal.mul_mem_left _ hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem val_coprime {p N : ℕ} (hc : N.Coprime p) {w : HeightOneSpectrum (𝓞 F)}
    (hp : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.valuation F (N : F) = 1 := by
  rw [val_nat]; exact HeightOneSpectrum.intValuation_eq_one_iff.2 (not_mem_of_coprime hc hp)

theorem val_ordCompl {p : ℕ} (n : ℕ) {w : HeightOneSpectrum (𝓞 F)} (hp : ((p : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    w.valuation F ((n / p ^ n.factorization p : ℕ) : F) = w.valuation F (n : F) := by
  conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [Nat.cast_mul, map_mul, Nat.cast_pow, map_pow, val_nat w p, HeightOneSpectrum.intValuation_eq_one_iff.2 hp,
    one_pow, one_mul]

theorem exists_nat_mul (x : F) : ∃ D : ℕ, D ≠ 0 ∧ IsIntegral ℤ ((D : F) * x) := by
  have ha : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
  obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
  rw [zsmul_eq_mul] at hy
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · exact ⟨n, by simpa using hy0, by simpa using hy⟩
  · exact ⟨n, by simpa using hy0, by simpa using hy.neg⟩

theorem exists_away {p : ℕ} (hp : p.Prime) (x : F) : ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧
    ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∉ w.asIdeal → w.valuation F ((N : F) * x) ≤ 1 := by
  obtain ⟨D, hD0, hD⟩ := exists_nat_mul x
  refine ⟨D / p ^ D.factorization p, Nat.ordCompl_pos p hD0, (Nat.coprime_ordCompl hp hD0).symm, fun w hw => ?_⟩
  rw [map_mul, val_ordCompl D hw, ← map_mul]
  exact (isIntegral_iff_val _).1 hD w

theorem exists_place {p : ℕ} (hp : p.Prime) : ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hne : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [← map_natCast (algebraMap ℤ (𝓞 F)) p, Algebra.norm_algebraMap,
      isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 F)).ne'] at h1
    exact (Nat.prime_iff_prime_int.1 hp).not_unit h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hmem : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by simpa using hmem)

theorem diff_ne : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot

theorem coe_diff_ne : (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 diff_ne

theorem count_diff (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) :=
  FractionalIdeal.count_coe F w diff_ne

theorem mem_diff_iff (x : F) : x ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ↔
    ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F x ≤ WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  rw [GlobalTheory.Idele.mem_iff_valuation_le coe_diff_ne]
  simp only [count_diff]

theorem trace_int {y : F} (h : ∀ w : HeightOneSpectrum (𝓞 F), w.valuation F y ≤ WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)))
    {x : F} (hx : IsIntegral ℤ x) : ∃ n : ℤ, Algebra.trace ℚ F (y * x) = n := by
  have h1 : y ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    rw [GlobalTheory.Idele.mem_iff_valuation_le (inv_ne_zero coe_diff_ne)]
    intro w
    rw [FractionalIdeal.count_inv, count_diff, neg_neg]
    exact h w
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv, FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 F)⁰ F))] at h1
  obtain ⟨n, hn⟩ := h1 x ((FractionalIdeal.mem_one_iff _).2 ⟨⟨x, hx⟩, rfl⟩)
  exact ⟨n, by rw [← Algebra.traceForm_apply, ← hn]; simp⟩

end GlobalTheory.HilbertThetaSeries.DenP


open GlobalTheory.HilbertThetaSeries.DenP in
theorem GlobalTheory.HilbertThetaSeries.denominators_prime_to : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → δ ≠ 0 ∧ (∀ x : F, PInt p x → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsIntegral ℤ ((N : F) * x)) ∧ (∀ b : F, PInt p (δ * b) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ ∀ x : F, IsIntegral ℤ x → ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * b * x) = n) ∧ ∃ (d : 𝓞 F) (N : ℕ), d ∈ differentIdeal ℤ (𝓞 F) ∧ N.Coprime p ∧ 0 < N ∧ PUnit p ((d : F) / δ) := by
  intro F _ _ p hp δ hδ
  have h0 : δ ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_place (F := F) hp
    rintro rfl
    have := hδ w hw
    rw [map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨h0, fun x hx => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp x
    refine ⟨N, hN0, hNc, (isIntegral_iff_val _).2 fun w => ?_⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, val_coprime hNc hw, one_mul]; exact hx w hw
    · exact hN w hw
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp b
    refine ⟨N, hN0, hNc, fun x hx => trace_int (fun w => ?_) hx⟩
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, val_coprime hNc hw, one_mul]
      have h1 := hb w hw
      rw [map_mul, hδ w hw, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_one] at h1
      exact h1
    · refine (hN w hw).trans ?_
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      positivity
  · obtain ⟨N, hN0, hNc, hN⟩ := exists_away hp δ
    set c : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 F)) with hc
    have hc0 : c ≠ 0 := fun h => diff_ne (Ideal.absNorm_eq_zero_iff.1 h)
    have hcm : (c : F) ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨c, Ideal.absNorm_mem _, map_natCast _ _⟩
    have hcc : (c / p ^ c.factorization p).Coprime p := (Nat.coprime_ordCompl hp hc0).symm
    have hm : ((c / p ^ c.factorization p : ℕ) : F) * ((N : F) * δ) ∈ (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [mem_diff_iff]
      intro w
      by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
      · rw [map_mul, map_mul, val_coprime hNc hw, val_coprime hcc hw, one_mul, one_mul, hδ w hw]
      · rw [map_mul, val_ordCompl c hw]
        simpa using mul_le_mul' ((mem_diff_iff _).1 hcm w) (hN w hw)
    obtain ⟨d, hd, hd'⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
    refine ⟨d, 1, hd, Nat.coprime_one_left p, one_pos, fun w hw => ?_⟩
    have : (d : F) / δ = ((c / p ^ c.factorization p : ℕ) : F) * (N : F) := by
      rw [div_eq_iff h0, mul_assoc]; exact hd'
    rw [this, map_mul, val_coprime hNc hw, val_coprime hcc hw, one_mul]

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDel_ne_zero_coprime_denominators_different_generator : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → δ ≠ 0 ∧ (∀ x : F, PInt p x → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ IsIntegral ℤ ((N : F) * x)) ∧ (∀ b : F, PInt p (δ * b) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ ∀ x : F, IsIntegral ℤ x → ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * b * x) = n) ∧ ∃ (d : 𝓞 F) (N : ℕ), d ∈ differentIdeal ℤ (𝓞 F) ∧ N.Coprime p ∧ 0 < N ∧ PUnit p ((d : F) / δ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.denominators_prime_to | exact GlobalTheory.HilbertThetaSeries.denominators_prime_to | (intros; apply GlobalTheory.HilbertThetaSeries.denominators_prime_to <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.RepsLat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mem_aL_iff (a : F) (x : κ → F) :
    x ∈ aL κ a ↔ ∃ m : κ → 𝓞 F, x = fun i => a * (m i : F) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => ⟨l i, (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ _)⟩, ?_⟩
    funext i
    rfl
  · rintro ⟨m, rfl⟩
    refine ⟨fun i => (m i : F), ?_, ?_⟩
    · exact (AddSubgroup.mem_pi _).2 fun i _ => (m i).2
    · funext i
      rfl

end GlobalTheory.HilbertThetaSeries.RepsLat

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.RepsLat in
theorem exists_isReps_aL : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F),
    a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧
      aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  intro F _ _ κ _ _ a b ha hb hc
  obtain ⟨c, hcF⟩ : ∃ c : 𝓞 F, (c : F) = a / b := ⟨⟨a / b, hc⟩, rfl⟩
  have hab : a = b * (c : F) := by rw [hcF]; field_simp
  have hc0 : c ≠ 0 := by
    intro h
    apply ha
    have h0 : (c : F) = 0 := by rw [h]; rfl
    rw [hcF, div_eq_zero_iff] at h0
    tauto
  let I : Ideal (𝓞 F) := Ideal.span {c}
  have hcard : Nat.card (𝓞 F ⧸ I) = (Algebra.norm ℤ c).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : (Algebra.norm ℤ c).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hc0
  haveI : Finite (𝓞 F ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ hne)
  letI : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  classical
  let s : 𝓞 F ⧸ I → 𝓞 F := fun q => if q = 0 then 0 else Classical.choose (Ideal.Quotient.mk_surjective q)
  have hs : ∀ q, Ideal.Quotient.mk I (s q) = q := by
    intro q
    by_cases h : q = 0
    · simp [s, h]
    · simp only [s, if_neg h]
      exact Classical.choose_spec (Ideal.Quotient.mk_surjective q)
  have hs0 : s 0 = 0 := by simp [s]
  let e : (κ → 𝓞 F ⧸ I) → (κ → F) := fun q i => b * (s (q i) : F)
  have he : Function.Injective e := by
    intro q q' h
    funext i
    have h1 := mul_left_cancel₀ hb (congrFun h i)
    have h3 : s (q i) = s (q' i) := RingOfIntegers.ext h1
    rw [← hs (q i), ← hs (q' i), h3]
  refine ⟨Finset.univ.image e, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (mem_aL_iff b _).2 ⟨fun i => s (q i), rfl⟩
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff b x).1 hx
    refine ⟨e (fun i => Ideal.Quotient.mk I (m i)), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have hI : ∀ i, m i - s (Ideal.Quotient.mk I (m i)) ∈ I := fun i => by
        rw [← Ideal.Quotient.eq, hs]
      choose r hr using fun i => Ideal.mem_span_singleton'.1 (hI i)
      refine (mem_aL_iff a _).2 ⟨r, ?_⟩
      funext i
      have h1 := congrArg (fun z : 𝓞 F => (z : F)) (hr i)
      simp only [map_mul, map_sub] at h1
      simp only [e, Pi.sub_apply]
      rw [hab]
      linear_combination -b * h1
    · rintro y ⟨hyT, hy⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyT
      have hq : q = fun i => Ideal.Quotient.mk I (m i) := by
        funext i
        obtain ⟨r, hr⟩ := (mem_aL_iff a _).1 hy
        have h1 := congrFun hr i
        simp only [e, Pi.sub_apply] at h1
        have h2 : ((m i - s (q i) : 𝓞 F) : F) = ((r i * c : 𝓞 F) : F) := by
          simp only [map_mul, map_sub]
          apply mul_left_cancel₀ hb
          rw [hab] at h1
          linear_combination h1
        have h3 : m i - s (q i) ∈ I := Ideal.mem_span_singleton'.2 ⟨r i, (RingOfIntegers.ext h2).symm⟩
        rw [← hs (q i)]
        exact (Ideal.Quotient.eq.2 h3).symm
      rw [hq]
  · refine Finset.mem_image.2 ⟨0, Finset.mem_univ _, ?_⟩
    funext i
    simp [e, hs0]
  · intro x hx
    obtain ⟨m, rfl⟩ := (mem_aL_iff a x).1 hx
    refine (mem_aL_iff b _).2 ⟨fun i => c * m i, ?_⟩
    funext i
    simp only [map_mul]
    rw [hab]
    ring
  · rw [Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fun, ← Nat.card_eq_fintype_card,
      hcard, ← hcF, Nat.cast_pow, Nat.cast_natAbs, ← Algebra.coe_norm_int, Int.cast_abs]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (a b : F), a ≠ 0 → b ≠ 0 → IsIntegral ℤ (a / b) → ∃ T : Finset (κ → F), IsReps (aL κ a) (aL κ b) T ∧ 0 ∈ T ∧ aL κ a ≤ aL κ b ∧ (T.card : ℚ) = |Algebra.norm ℚ (a / b)| ^ Fintype.card κ := by
  first | exact @GlobalTheory.HilbertThetaSeries.exists_isReps_aL | exact GlobalTheory.HilbertThetaSeries.exists_isReps_aL | (intros; apply GlobalTheory.HilbertThetaSeries.exists_isReps_aL <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertModerateGrowthUnnormalizedSlash
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.Growth

open UpperHalfPlane hiding I

def sF (w : ℍ) : ℝ := (1 + ‖(w : ℂ)‖ ^ 2) / w.im

lemma sq_norm_coe (w : ℍ) : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, coe_re, coe_im]
  ring

lemma one_le_sF (w : ℍ) : 1 ≤ sF w := by
  have him := w.im_pos
  rw [sF, le_div_iff₀ him, one_mul, sq_norm_coe]
  nlinarith [sq_nonneg w.re, sq_nonneg (w.im - 1)]

lemma sF_nonneg (w : ℍ) : 0 ≤ sF w := zero_le_one.trans (one_le_sF w)

lemma poly_bound (a b c d x y : ℝ) :
    (c * x + d) ^ 2 + (c * y) ^ 2 + ((a * x + b) ^ 2 + (a * y) ^ 2) ≤
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (1 + (x ^ 2 + y ^ 2)) := by
  nlinarith [sq_nonneg (a - b * x), sq_nonneg (c - d * x), sq_nonneg (b * y), sq_nonneg (d * y)]

lemma normSq_lin (a b : ℝ) (z : ℍ) :
    Complex.normSq ((a : ℂ) * z + b) = (a * z.re + b) ^ 2 + (a * z.im) ^ 2 := by
  simp [Complex.normSq_apply]; ring

lemma sF_smul (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, sF (g • z) ≤ K * sF z := by
  have hD : 0 < |g.det.val| := abs_pos.mpr g.det.ne_zero
  refine ⟨((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) / |g.det.val|, by positivity, fun z => ?_⟩
  have hN : 0 < Complex.normSq (denom g z) := normSq_denom_pos g z.im_ne_zero
  have him := z.im_pos
  have h1 : sF (g • z) =
      (Complex.normSq (denom g z) + Complex.normSq (num g z)) / (|g.det.val| * z.im) := by
    rw [sF, im_smul_eq_div_normSq, coe_smul, norm_σ, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm]
    field_simp
  have h2 : Complex.normSq (denom g z) + Complex.normSq (num g z) ≤
      ((g 0 0) ^ 2 + (g 0 1) ^ 2 + (g 1 0) ^ 2 + (g 1 1) ^ 2) * (1 + ‖(z : ℂ)‖ ^ 2) := by
    have e1 : Complex.normSq (denom g z) = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    have e2 : Complex.normSq (num g z) = (g 0 0 * z.re + g 0 1) ^ 2 + (g 0 0 * z.im) ^ 2 :=
      normSq_lin _ _ z
    rw [e1, e2, sq_norm_coe]
    exact poly_bound _ _ _ _ _ _
  rw [h1, sF, div_mul_div_comm]
  exact div_le_div_of_nonneg_right h2 (mul_pos hD him).le

lemma denom_inv (g : GL (Fin 2) ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℍ, ‖denom g z‖⁻¹ ≤ K * sF z := by
  have hq : 0 < (g 1 0) ^ 2 + (g 1 1) ^ 2 := by
    by_contra hc
    push_neg at hc
    have h10 : g 1 0 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have h11 : g 1 1 = 0 := by nlinarith [sq_nonneg (g 1 0), sq_nonneg (g 1 1)]
    have hdet := g.det.ne_zero
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h11] at hdet
  refine ⟨1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2), by positivity, fun z => ?_⟩
  have him := z.im_pos
  have hm : 0 < ‖denom g z‖ := norm_pos_iff.mpr (denom_ne_zero g z)
  have hN : ‖denom g z‖ ^ 2 = (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2 := by
    rw [Complex.sq_norm]
    exact normSq_lin _ _ z
  have key : ((g 1 0) ^ 2 + (g 1 1) ^ 2) * z.im ^ 2 ≤ ‖denom g z‖ ^ 2 * (1 + ‖(z : ℂ)‖ ^ 2) := by
    rw [hN, sq_norm_coe]
    nlinarith [sq_nonneg (g 1 0 * z.re + g 1 1),
      sq_nonneg ((g 1 0 * z.re + g 1 1) * z.re + g 1 0 * z.im ^ 2)]
  have hK1 : 1 ≤ 1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by
    have : 0 ≤ 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2) := by positivity
    linarith
  have hKq : (1 + 1 / ((g 1 0) ^ 2 + (g 1 1) ^ 2)) * ((g 1 0) ^ 2 + (g 1 1) ^ 2) =
      ((g 1 0) ^ 2 + (g 1 1) ^ 2) + 1 := by
    field_simp
  have hT1 : 1 ≤ 1 + ‖(z : ℂ)‖ ^ 2 := by nlinarith [sq_nonneg ‖(z : ℂ)‖]
  set q := (g 1 0) ^ 2 + (g 1 1) ^ 2 with hqdef
  set K := 1 + 1 / q with hKdef
  set T := 1 + ‖(z : ℂ)‖ ^ 2 with hTdef
  set m := ‖denom g z‖ with hmdef
  have h1 : 1 ≤ K ^ 2 * q * T := by
    have e : K ^ 2 * q * T = K * (K * q) * T := by ring
    rw [e, hKq]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK1 (by linarith)) hT1
  have hsq : z.im ^ 2 ≤ (K * T * m) ^ 2 := by
    have e : (K * T * m) ^ 2 = K ^ 2 * T * (m ^ 2 * T) := by ring
    rw [e]
    have hKT : 0 ≤ K ^ 2 * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hKT, mul_le_mul_of_nonneg_right h1 (sq_nonneg z.im)]
  have hP : 0 ≤ K * T * m := by positivity
  have hy : z.im ≤ K * T * m := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ hm, sF, ← hTdef,
    show K * (T / z.im) * m = (K * T * m) / z.im by ring, le_div_iff₀ him, one_mul]
  exact hy

variable {F : Type} [Field F] [NumberField F]

def sP (z : Hn F) : ℝ := ∏ v, sF (z v)

lemma one_le_sP (z : Hn F) : 1 ≤ sP z := by
  calc (1 : ℝ) = ∏ v, (1 : ℝ) := by simp
    _ ≤ ∏ v, sF (z v) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun v _ => one_le_sF _)

lemma sP_nonneg (z : Hn F) : 0 ≤ sP z := zero_le_one.trans (one_le_sP z)

lemma gr_iff (f : Hn F → ℂ) : Gr f ↔ ∃ (C : ℝ) (A : ℕ), 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ C * sP z ^ A := by
  rw [Gr.eq_1]
  constructor
  · rintro ⟨C, A, hC⟩
    refine ⟨max C 0, A, le_max_right _ _, fun z => (hC z).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (sP_nonneg z) A)
  · rintro ⟨C, A, -, hC⟩
    exact ⟨C, A, hC⟩

lemma gr_add {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f + g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 + C2, A1 + A2, add_nonneg hC1 hC2, fun z => ?_⟩
  have hP := one_le_sP z
  have e1 : sP z ^ A1 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  have e2 : sP z ^ A2 ≤ sP z ^ (A1 + A2) := pow_le_pow_right₀ hP (by omega)
  calc ‖(f + g) z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ C1 * sP z ^ A1 + C2 * sP z ^ A2 := add_le_add (h1 z) (h2 z)
    _ ≤ C1 * sP z ^ (A1 + A2) + C2 * sP z ^ (A1 + A2) :=
      add_le_add (mul_le_mul_of_nonneg_left e1 hC1) (mul_le_mul_of_nonneg_left e2 hC2)
    _ = (C1 + C2) * sP z ^ (A1 + A2) := by ring

lemma gr_mul {f g : Hn F → ℂ} (hf : Gr f) (hg : Gr g) : Gr (f * g) := by
  rw [gr_iff] at hf hg ⊢
  obtain ⟨C1, A1, hC1, h1⟩ := hf
  obtain ⟨C2, A2, hC2, h2⟩ := hg
  refine ⟨C1 * C2, A1 + A2, mul_nonneg hC1 hC2, fun z => ?_⟩
  calc ‖(f * g) z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ (C1 * sP z ^ A1) * (C2 * sP z ^ A2) :=
      mul_le_mul (h1 z) (h2 z) (norm_nonneg _) (mul_nonneg hC1 (pow_nonneg (sP_nonneg z) _))
    _ = C1 * C2 * sP z ^ (A1 + A2) := by ring

lemma gr_const (c : ℂ) : Gr (fun _ : Hn F => c) := by
  rw [gr_iff]
  exact ⟨‖c‖, 0, norm_nonneg _, fun z => by simp⟩

lemma gr_smul (c : ℂ) {f : Hn F → ℂ} (hf : Gr f) : Gr (c • f) := gr_mul (gr_const c) hf

lemma gr_act (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (fun z => f (act h z)) := by
  rw [gr_iff] at hf ⊢
  obtain ⟨C, A, hC, hfz⟩ := hf
  choose K hK0 hK using fun v : InfinitePlace F => sF_smul (cmp v h)
  have hact : ∀ z : Hn F, sP (act h z) ≤ (∏ v, K v) * sP z := by
    intro z
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      exact sF_nonneg _
    · intro v _
      rw [act.eq_1]
      exact hK v (z v)
  refine ⟨C * (∏ v, K v) ^ A, A,
    mul_nonneg hC (pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) A), fun z => ?_⟩
  calc ‖f (act h z)‖ ≤ C * sP (act h z) ^ A := hfz _
    _ ≤ C * ((∏ v, K v) * sP z) ^ A :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sP_nonneg _) (hact z) A) hC
    _ = C * (∏ v, K v) ^ A * sP z ^ A := by ring

lemma gr_denom (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    Gr (fun z : Hn F => (∏ v, denom (GlobalTheory.HilbertThetaSeries.cmp v h) (z v))⁻¹ ^ k) := by
  rw [gr_iff]
  choose K hK0 hK using fun v : InfinitePlace F => denom_inv (cmp v h)
  refine ⟨(∏ v, K v) ^ k, k, pow_nonneg (Finset.prod_nonneg fun v _ => hK0 v) k, fun z => ?_⟩
  have hb : ‖(∏ v, denom (cmp v h) (z v))⁻¹‖ ≤ (∏ v, K v) * sP z := by
    rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib]
    unfold sP
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro v _
      positivity
    · intro v _
      exact hK v (z v)
  rw [norm_pow, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hb k

lemma hilbertModerateGrowth_unnormalizedSlash (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl0 k h f) :=
  gr_mul (gr_denom k h) (gr_act h hf)

lemma gr_sl (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) {f : Hn F → ℂ} (hf : Gr f) : Gr (sl k h f) :=
  gr_mul (gr_const _) (hilbertModerateGrowth_unnormalizedSlash k h hf)

theorem gr_closed : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Gr f → Gr g → Gr (f + g) ∧ Gr (c • f) ∧ Gr (f * g) ∧ Gr (1 : Hn F → ℂ) ∧ Gr (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Gr (sl0 k h f) ∧ Gr (sl k h f) :=
  fun _ _ _ k _ _ c hf hg =>
    ⟨gr_add hf hg, gr_smul c hf, gr_mul hf hg, gr_const 1, gr_const 0, fun h _ => ⟨hilbertModerateGrowth_unnormalizedSlash k h hf, gr_sl k h hf⟩⟩

end GlobalTheory.HilbertThetaSeries.Growth
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.NormSumFreeOrbitsLeInvPrime
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem freeOrbit_prime_dvd_card {p : ℕ} [Fact p.Prime] {α : Type} (σ : α → α) (F : Finset α)
    (hF : ∀ x ∈ F, σ x ∈ F) (hp : ∀ x ∈ F, σ^[p] x = x) (hfree : ∀ x ∈ F, σ x ≠ x) :
    p ∣ F.card := by
  classical
  let f : Function.End F := fun y => ⟨σ y, hF y y.2⟩
  have hf : ∀ (n : ℕ) (y : F), (((f ^ n) y : F) : α) = σ^[n] y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', Function.iterate_succ_apply', ← ih y]
      rfl
  have h1 : f ^ p ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hf]
    exact hp y y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) h1
  have h3 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    constructor
    rintro ⟨y, hy⟩
    exact hfree y y.2 (congrArg Subtype.val hy)
  rw [h3, Fintype.card_coe] at h2
  exact Nat.modEq_zero_iff_dvd.mp h2

theorem norm_prime_Qbar_eq (p : ℕ) [Fact p.Prime] : ‖(p : Qbar p)‖ = (p : ℝ)⁻¹ := by
  have h := PadicAlgCl.valuation_p p
  rw [← PadicAlgCl.valuation_coe, h]
  simp

theorem norm_sum_free_orbits_le : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  intro p _ ι α σ s Φ hs hp hfree hinv hle
  classical
  have hna := PadicAlgCl.isNonarchimedean p
  have key : ∀ c ∈ s.image Φ,
      ‖ι.symm ((s.filter (fun x => Φ x = c)).card • c)‖ ≤ (p : ℝ)⁻¹ := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    have hd : p ∣ (s.filter (fun x => Φ x = Φ y)).card := by
      apply freeOrbit_prime_dvd_card σ
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨hs x hx.1, (hinv x hx.1).trans hx.2⟩
      · intro x hx
        exact hp x (Finset.mem_filter.1 hx).1
      · intro x hx
        exact hfree x (Finset.mem_filter.1 hx).1
    obtain ⟨k, hk⟩ := hd
    rw [map_nsmul, nsmul_eq_mul, norm_mul, hk, Nat.cast_mul, norm_mul, norm_prime_Qbar_eq]
    have h1 : ‖((k : ℕ) : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ k
    have h2 := hle y hy
    calc (p : ℝ)⁻¹ * ‖((k : ℕ) : Qbar p)‖ * ‖ι.symm (Φ y)‖ ≤ (p : ℝ)⁻¹ * 1 * 1 := by gcongr
      _ = (p : ℝ)⁻¹ := by ring
  have hsum : ∑ x ∈ s, Φ x = ∑ c ∈ s.image Φ, (s.filter (fun x => Φ x = c)).card • c :=
    Finset.sum_comp (fun c => c) Φ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  generalize s.image Φ = T at key
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact (hna _ _).trans (max_le (key a (Finset.mem_insert_self a T))
      (ih fun c hc => key c (Finset.mem_insert_of_mem hc)))

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_sum_free_orbits_le_inv_prime : ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (α : Type) (σ : α → α) (s : Finset α) (Φ : α → ℂ), (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, σ^[p] x = x) → (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, Φ (σ x) = Φ x) → (∀ x ∈ s, ‖ι.symm (Φ x)‖ ≤ 1) → ‖ι.symm (∑ x ∈ s, Φ x)‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | exact GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le | (intros; apply GlobalTheory.HilbertThetaSeries.norm_sum_free_orbits_le <;> assumption)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesTranslationTwistsCoefficients
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

open UpperHalfPlane hiding I

namespace GlobalTheory.HilbertThetaSeries

theorem reAt_eq_rhom {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    reAt v x = rhom x v := by
  unfold reAt
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]
  rfl

theorem reAt_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x y : F) :
    reAt v (x * y) = reAt v x * reAt v y := by
  rw [reAt_eq_rhom, reAt_eq_rhom, reAt_eq_rhom, map_mul, Pi.mul_apply]

theorem sum_reAt_eq_trace {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (x : F) :
    ∑ v, (reAt v x : ℂ) = ((Algebra.trace ℚ F x : ℚ) : ℂ) := by
  have key : ∑ v : InfinitePlace F, reAt v x = ∑ σ : F →+* ℝ, σ x := by
    refine Fintype.sum_bijective (fun v => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v))
      ⟨?_, ?_⟩ _ _ ?_
    · intro v w h
      have hvw : v.embedding = w.embedding := by
        ext y
        rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v),
          ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal w)]
        exact congrArg (fun f : F →+* ℝ => ((f y : ℝ) : ℂ)) h
      rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding w, hvw]
    · intro φ
      have hψ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp φ) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        simp
      refine ⟨InfinitePlace.mk (Complex.ofRealHom.comp φ), ?_⟩
      ext y
      apply Complex.ofReal_injective
      rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hψ]
      rfl
    · intro v
      exact reAt_eq_rhom v x
  rw [← Complex.ofReal_sum, key, ← trace_eq_sum_realEmbeddings, Complex.ofReal_ratCast]

theorem cmp_toInf_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : GL (Fin 2) F)
    (v : InfinitePlace F) (i j : Fin 2) :
    ((cmp v (toInf g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = rhom ((g : Matrix (Fin 2) (Fin 2) F) i j) v := rfl

theorem denom_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℂ) :
    denom (cmp v (toInf (aff 1 b))) w = 1 := by
  simp [denom, cmp_toInf_apply, aff]

theorem coe_translate_smul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b : F) (v : InfinitePlace F) (w : ℍ) :
    ((cmp v (toInf (aff 1 b)) • w : ℍ) : ℂ) = (w : ℂ) + (reAt v b : ℂ) := by
  have e : ∀ i j, ((cmp v (toInf (aff 1 b)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      rhom ((aff (1 : Fˣ) b : Matrix (Fin 2) (Fin 2) F) i j) v := fun i j => cmp_toInf_apply _ v i j
  have hdet : 0 < ((Matrix.GeneralLinearGroup.det (cmp v (toInf (aff 1 b)))) : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, e, e, e, e]
    simp [aff]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet, denom_translate]
  simp only [UpperHalfPlane.num, e]
  simp [aff, reAt_eq_rhom]

theorem ez_translate {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (b ξ : F) (z : Hn F) :
    ez ξ (act (toInf (aff 1 b)) z) = et (b * ξ) * ez ξ z := by
  rw [mul_comm b ξ]
  have h := sum_reAt_eq_trace (ξ * b)
  simp only [ez, et, act, coe_translate_smul]
  rw [← Complex.exp_add, ← h]
  congr 1
  simp only [reAt_mul, Complex.ofReal_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem th_translate : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ),
    sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  intro F _ _ _ κ _ _ G k b Φ
  funext z
  simp only [sl0, denom_translate, Finset.prod_const_one, inv_one, one_pow, one_mul, th]
  refine tsum_congr fun x => ?_
  rw [ez_translate]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_translation_twists_coefficients : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (k : ℕ) (b : F) (Φ : (κ → F) → ℂ), sl0 k (toInf (aff 1 b)) (th G Φ) = th G (fun x => Φ x * et (b * QF G x)) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_translate | exact GlobalTheory.HilbertThetaSeries.th_translate | (intros; apply GlobalTheory.HilbertThetaSeries.th_translate <;> assumption)
end
