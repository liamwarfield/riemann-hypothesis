module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
public import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BlochKatoIntegralScalars

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_of_norm_le_one (K : Loc.FinExt l) (x : K.1) (h : ‖(x : PadicAlgCl l)‖ ≤ 1) :
    x ∈ Loc.OL K :=
  (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1
    (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : Loc.FinExt l) : CompactSpace ↥(Loc.GK K) := by
  haveI := K.2
  have h : IsClosed ((Loc.GK K : Subgroup (Loc.GQ l)) : Set (Loc.GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed K.1
  exact isCompact_iff_compactSpace.1 h.isCompact

theorem exists_pow_mul_mem_OL {X : Type} [TopologicalSpace X] [CompactSpace X] (K : Loc.FinExt l) {m : ℕ}
    (c : X → Fin m → K.1) (hc : Continuous c) :
    ∃ N : ℕ, ∀ g j, (l : K.1) ^ N * c g j ∈ Loc.OL K := by
  have hc' : Continuous fun g (j : Fin m) => ((c g j : K.1) : PadicAlgCl l) :=
    continuous_pi fun j => continuous_subtype_val.comp ((continuous_apply j).comp hc)
  obtain ⟨C, hC⟩ := (isCompact_range hc').isBounded.exists_norm_le
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt C hl
  refine ⟨N, fun g j => mem_OL_of_norm_le_one K _ ?_⟩
  have h1 : ‖((c g j : K.1) : PadicAlgCl l)‖ ≤ C :=
    (norm_le_pi_norm (fun j : Fin m => ((c g j : K.1) : PadicAlgCl l)) j).trans (hC _ ⟨g, rfl⟩)
  have h2 : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    have := PadicAlgCl.norm_extends l (l : ℚ_[l])
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
  have h3 : (((l : K.1) ^ N * c g j : K.1) : PadicAlgCl l) =
      (l : PadicAlgCl l) ^ N * ((c g j : K.1) : PadicAlgCl l) := by
    push_cast
    rfl
  rw [h3, norm_mul, norm_pow, h2, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  exact h1.trans hN.le

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

end Local

theorem mem_of_mk_mem_span {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (ρ : Representation R G M) (S : Submodule R (G → M)) (hB : ∀ x : M, (fun g => ρ g x - x) ∈ S)
    (A : Set (ReciprocityTheory.Gal.H1 ρ))
    (hA : ∀ x ∈ A, ∃ w : ReciprocityTheory.Gal.Z1 ρ, (w : G → M) ∈ S ∧ x = Submodule.Quotient.mk w)
    (w : ReciprocityTheory.Gal.Z1 ρ) (hw : Submodule.Quotient.mk w ∈ Submodule.span R A) : (w : G → M) ∈ S := by
  have hB' : (ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype ≤ S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype := by
    intro w hw
    obtain ⟨x, hx⟩ := (mem_coboundaries1 ρ _).1 hw
    have : (ReciprocityTheory.Gal.Z1 ρ).subtype w = fun g => ρ g x - x := funext hx
    rw [Submodule.mem_comap, this]
    exact hB x
  have hle : Submodule.span R A ≤ (S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map (Submodule.mkQ _) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hA x hx
    exact ⟨w, hw, rfl⟩
  have h2 : w ∈ ((S.comap (ReciprocityTheory.Gal.Z1 ρ).subtype).map
      (Submodule.mkQ ((ReciprocityTheory.Gal.B1 ρ).comap (ReciprocityTheory.Gal.Z1 ρ).subtype))).comap (Submodule.mkQ _) :=
    hle hw
  rw [Submodule.comap_map_mkQ, sup_eq_right.2 hB'] at h2
  exact h2

end GlobalTheory.BlochKatoIntegralScalars
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulPowIntegral
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

noncomputable section

namespace GlobalTheory.Square.AwayClosure

variable {K : Type} [Field K] [NumberField K]

open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.Square.AwayClosure.of_integral {m k l : ℕ} {x : K} (hx : x ≠ 0) {a b : 𝓞 K}
    (ha : x * (m : K) ^ k = a) (hb : x⁻¹ * (m : K) ^ l = b) : _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hab : ((m : K)) ^ (k + l) = (a : K) * (b : K) := by
    rw [← ha, ← hb, pow_add]
    field_simp
  refine ⟨a, k, k + l, ⟨b, RingOfIntegers.coe_injective ?_⟩, ha⟩
  simpa using hab

open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.Square.AwayClosure.of_pow_eq_one (m : ℕ) {x : K} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) :
    _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hk.ne'] at h
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hk (h ▸ isIntegral_one)
  have hxinv : IsIntegral ℤ x⁻¹ :=
    IsIntegral.of_pow hk (by rw [inv_pow, h, inv_one]; exact isIntegral_one)
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral (k := 0) (l := 0) (a := ⟨x, hxi⟩)
    (b := ⟨x⁻¹, hxinv⟩) hx (by rw [pow_zero, mul_one]; rfl) (by rw [pow_zero, mul_one]; rfl)

open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.Square.AwayClosure.of_dvd {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) :
    _root_.GlobalTheory.Square.IsAwayUnit m (a : K) :=
  ⟨a, 0, k, h, by simp⟩

open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.Square.AwayClosure.mul {m : ℕ} {x y : K} (hx : _root_.GlobalTheory.Square.IsAwayUnit m x)
    (hy : _root_.GlobalTheory.Square.IsAwayUnit m y) : _root_.GlobalTheory.Square.IsAwayUnit m (x * y) :=
  by
    obtain ⟨a, k, j, ha, hx⟩ := hx
    obtain ⟨b, l, i, hb, hy⟩ := hy
    refine ⟨a * b, k + l, j + i, by rw [pow_add]; exact mul_dvd_mul ha hb, ?_⟩
    calc
      x * y * (m : K) ^ (k + l) = (x * (m : K) ^ k) * (y * (m : K) ^ l) := by rw [pow_add]; ring
      _ = ((a * b : 𝓞 K) : K) := by rw [hx, hy]; push_cast; rfl

open scoped nonZeroDivisors in
theorem _root_.GlobalTheory.Square.AwayClosure.inv {m : ℕ} (hm : 0 < m) {x : K} (hx : _root_.GlobalTheory.Square.IsAwayUnit m x) :
    _root_.GlobalTheory.Square.IsAwayUnit m x⁻¹ := by
  obtain ⟨a, k, k', ⟨c, hc⟩, hxa⟩ := hx
  have hcK : (m : K) ^ k' = (a : K) * (c : K) := by
    have := congrArg (fun t : 𝓞 K => (t : K)) hc
    simpa using this
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hxa
    rw [← hxa, zero_mul] at hcK
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hm.ne') hcK
  refine ⟨(m : 𝓞 K) ^ k * c, k', k + k', ⟨a, by rw [pow_add, hc]; ring⟩, ?_⟩
  push_cast
  rw [hcK, ← hxa]
  field_simp

end GlobalTheory.Square.AwayClosure

namespace GlobalTheory.Square

open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma valuation_coe_integer_eq_exp_neg_count (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (r : K) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (r : K))) := by
  have hspan : Ideal.span {r} ≠ 0 := by simpa using hr
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg _ hr, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K v hspan]

open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma valuation_eq_exp_neg_count_spanSingleton_foundation (v : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) :
    v.valuation K y =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by simpa using hs0
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hy
  have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) *
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K s) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hsK]
  have hcount := congrArg (FractionalIdeal.count K v) hmul
  rw [FractionalIdeal.count_mul K v (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])
    (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])] at hcount
  have hr' := valuation_coe_integer_eq_exp_neg_count v hr0
  have hs' := valuation_coe_integer_eq_exp_neg_count v hs0
  simp only [show ∀ t : 𝓞 K, (t : K) = algebraMap (𝓞 K) K t from fun _ => rfl] at hr' hs'
  rw [map_div₀, hr', hs', div_eq_iff (by simp), ← WithZero.exp_add, ← hcount]
  congr 1
  ring

open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_integer_eq_of_count_nonneg {y : K} (hy : y ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      0 ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ y)) :
    ∃ b : 𝓞 K, y = b := by
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K y fun v => by
    rw [valuation_eq_exp_neg_count_spanSingleton_foundation v hy, ← WithZero.exp_zero, WithZero.exp_le_exp]
    linarith [h v]
  exact ⟨b, hb.symm⟩

open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
private lemma exists_mul_pow_integer_of_count_eq_zero_coprime {m : ℕ} (hm : 0 < m) {y : K} (hy : y ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) = 0) :
    ∃ n : ℕ, ∃ b : 𝓞 K, y * (m : K) ^ n = b := by
  set I := FractionalIdeal.spanSingleton (𝓞 K)⁰ y with hIdef
  have hI : I ≠ 0 := by rwa [Ne, hIdef, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hfin : {w | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  set n := ∑ w ∈ hfin.toFinset, (FractionalIdeal.count K w I).natAbs
  have hbound : ∀ w, -(n : ℤ) ≤ FractionalIdeal.count K w I := by
    intro w
    by_cases hw : FractionalIdeal.count K w I = 0
    · rw [hw]
      simp
    · have hmem : w ∈ hfin.toFinset := by simpa using hw
      have hle : (FractionalIdeal.count K w I).natAbs ≤ n :=
        Finset.single_le_sum (f := fun w => (FractionalIdeal.count K w I).natAbs)
          (fun _ _ => Nat.zero_le _) hmem
      omega
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hm0 : (m : 𝓞 K) ≠ 0 := fun h0 => hmK (by simpa using congrArg (fun t : 𝓞 K => (t : K)) h0)
  have hmalg : (m : K) = algebraMap (𝓞 K) K (m : 𝓞 K) := by simp
  obtain ⟨b, hb⟩ := exists_integer_eq_of_count_nonneg (y := y * (m : K) ^ n)
    (mul_ne_zero hy (pow_ne_zero _ hmK)) fun w => by
      rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow,
        FractionalIdeal.count_mul K w hI
          (pow_ne_zero _ (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff])),
        FractionalIdeal.count_pow]
      have hc0 : 0 ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) := by
        rw [hmalg, ← FractionalIdeal.coeIdeal_span_singleton]
        exact FractionalIdeal.count_coe_nonneg K w _
      by_cases hw : (m : 𝓞 K) ∈ w.asIdeal
      · have h1 : 1 ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K)) := by
          rw [hmalg]
          exact _root_.Formalism.DivisionValues.idxChange_cnt_mem w hm0 hw
        nlinarith [hbound w]
      · rw [h w hw]
        positivity
  exact ⟨n, b, hb⟩

open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Square.isAwayUnit_closure : ∀ (K : Type) [Field K] [NumberField K]
    [StarRing K] (m : ℕ), 0 < m →
    (∀ (x : K) (k : ℕ), 0 < k → x ^ k = 1 → _root_.GlobalTheory.Square.IsAwayUnit m x) ∧
    (∀ (a : 𝓞 K) (k : ℕ), a ∣ (m : 𝓞 K) ^ k → _root_.GlobalTheory.Square.IsAwayUnit m (a : K)) ∧
    (∀ x y : K, _root_.GlobalTheory.Square.IsAwayUnit m x → _root_.GlobalTheory.Square.IsAwayUnit m y →
      _root_.GlobalTheory.Square.IsAwayUnit m (x * y)) ∧
    (∀ x : K, _root_.GlobalTheory.Square.IsAwayUnit m x → _root_.GlobalTheory.Square.IsAwayUnit m x⁻¹) ∧
    (∀ x : K, x ≠ 0 → (∀ w : _root_.Formalism.PairingDivisionLocalBalance.Pl K, (m : 𝓞 K) ∉ w.asIdeal → _root_.Formalism.DivisionValues.vw w x = 0) →
      _root_.GlobalTheory.Square.IsAwayUnit m x) := by
  intro K _ _ _ m hm
  refine ⟨fun x k hk h => _root_.GlobalTheory.Square.AwayClosure.of_pow_eq_one m hk h,
    fun a k h => _root_.GlobalTheory.Square.AwayClosure.of_dvd h,
    fun x y hx hy => _root_.GlobalTheory.Square.AwayClosure.mul hx hy,
    fun x hx => _root_.GlobalTheory.Square.AwayClosure.inv hm hx, fun x hx hv => ?_⟩
  have hI : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = 0 :=
    fun w hw => hv w hw
  have hI' : ∀ w : HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ w.asIdeal →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x⁻¹) = 0 := by
    intro w hw
    rw [← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, hI w hw, neg_zero]
  obtain ⟨k, a, ha⟩ := exists_mul_pow_integer_of_count_eq_zero_coprime hm hx hI
  obtain ⟨l, b, hb⟩ := exists_mul_pow_integer_of_count_eq_zero_coprime hm (inv_ne_zero hx) hI'
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral hx ha hb

end GlobalTheory.Square
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedOfPowFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory.WildInertiaChar

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

theorem wild_pow (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (i : ℕ) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((σ ^ i) y / y - 1) < 1 := by
  induction i with
  | zero => intro y hy; simp [hy]
  | succ i ih =>
    intro y hy
    have hz : (σ ^ i) y ≠ 0 := (map_ne_zero (σ ^ i)).mpr hy
    have h1 := h _ hz
    have h2 := ih y hy
    have e : (σ ^ (i + 1)) y / y - 1
        = (σ ((σ ^ i) y) / (σ ^ i) y - 1) * ((σ ^ i) y / y - 1)
          + ((σ ((σ ^ i) y) / (σ ^ i) y - 1) + ((σ ^ i) y / y - 1)) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [e]
    refine A.valuation.map_add_lt ?_ (A.valuation.map_add_lt h1 h2)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h2.le) h1

theorem fixed_of_pow_fixed (A : ValuationSubring Ω) (τ : Ω ≃ₐ[E] Ω)
    (h : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (k : ℕ)
    (hk : ¬ A.valuation (k : Ω) < 1) (x : Ω) (hx : (τ ^ k) x = x) : τ x = x := by
  by_contra hne
  have hd : τ x - x ≠ 0 := sub_ne_zero.mpr hne
  have hs : ∑ i ∈ Finset.range k, (τ ^ i) (τ x - x) = 0 := by
    have : ∀ i, (τ ^ i) (τ x - x) = (τ ^ (i + 1)) x - (τ ^ i) x := by
      intro i; rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (τ ^ i) x), hx]
    simp
  have e : (k : Ω) = - ∑ i ∈ Finset.range k, ((τ ^ i) (τ x - x) / (τ x - x) - 1) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    simp
  apply hk
  rw [e, Valuation.map_neg]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => wild_pow A τ h i _ hd

theorem trivial_on_wild (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (l : ℕ)
    (hl : l.Prime) (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (hA : IsPlaceOver A v)
    (Γ : Type) [CommGroup Γ] (ψ : G E Ω →* Γ) (hop : IsOpen (ψ.ker : Set (G E Ω)))
    (hψ : ∀ g, ∃ n : ℕ, ψ g ^ (l ^ n) = 1) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : ψ σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (one_mem ψ.ker))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ m ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine fixed_of_pow_fixed A (σ ^ m) (wild_pow A σ hσ m) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : ψ σ ^ m = 1 := by
    rw [← map_pow]; exact hsub hτ
  obtain ⟨n, hn⟩ := hψ σ
  have hc : Nat.Coprime (l ^ n) m := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hm).pow_left n
  have := (pow_gcd_eq_one (a := ψ σ) (m := l ^ n) (n := m)).mpr ⟨hn, h1⟩
  rwa [hc, pow_one] at this

end GlobalTheory.WildInertiaChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.EmbThroughCompletion

section Norm

theorem norm_le_one_of_isIntegral {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {E C : Type} [Field E] [NumberField E] [NormedField C] [IsUltrametricDist C]

theorem norm_int_le_one (a : E →+* C) (x : 𝓞 E) : ‖a (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (R := ℤ) (fun r => by simpa using IsUltrametricDist.norm_intCast_le_one C r)
    (map_isIntegral_int a x.isIntegral_coe)

theorem norm_lt_one_iff (v : HeightOneSpectrum (𝓞 E)) (a b : E →+* C)
    (ha : ∀ x : 𝓞 E, ‖a (x : E)‖ < 1 ↔ x ∈ v.asIdeal) (hb : ∀ x : 𝓞 E, ‖b (x : E)‖ < 1 ↔ x ∈ v.asIdeal)
    (x : E) : ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  have hd : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ‖c ((d : 𝓞 E) : E)‖ = 1 :=
    fun c hc => le_antisymm (norm_int_le_one c _) (not_lt.1 fun h' => d.2 ((hc _).1 h'))
  rcases h with h | h
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) →
        (‖c x‖ < 1 ↔ n ∈ v.asIdeal) := by
      intro c hc
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      rw [← hc n]
      change ‖c x‖ * ‖c ((d : 𝓞 E) : E)‖ = ‖c (n : E)‖ at h1
      rw [hd c hc, mul_one] at h1
      rw [h1]
    rw [key a ha, key b hb]
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ¬ ‖c x‖ < 1 := by
      intro c hc hlt
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      change ‖c x‖ * ‖c (n : E)‖ = ‖c ((d : 𝓞 E) : E)‖ at h1
      rw [hd c hc] at h1
      have h2 := norm_int_le_one c n
      have h3 := norm_nonneg (c x)
      have h4 := norm_nonneg (c (n : E))
      nlinarith
    exact iff_of_false (key a ha) (key b hb)

end Norm

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (K : Loc.FinExt l) (x : K.1) : x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  refine (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).symm.trans
    ⟨fun h => norm_le_one_of_isIntegral (fun r => ?_) h, fun h => isIntegral_of_norm_le_one _ h⟩
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact r.2

theorem not_isUnit_iff (K : Loc.FinExt l) (x : Loc.OL K) :
    ¬ IsUnit x ↔ ‖((x : K.1) : PadicAlgCl l)‖ < 1 := by
  have hx := (mem_OL_iff K _).1 x.2
  constructor
  · intro h
    refine lt_of_le_of_ne hx fun h1 => h ?_
    have h0 : (x : K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K.1)⁻¹, (mem_OL_iff K _).2 ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
  · intro h hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hu
    have hy' := (mem_OL_iff K _).1 y.2
    have h1 := congrArg (fun z : Loc.OL K => ‖((z : K.1) : PadicAlgCl l)‖) hy
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
    have h3 := norm_nonneg ((x : K.1) : PadicAlgCl l)
    have h4 := norm_nonneg ((y : K.1) : PadicAlgCl l)
    nlinarith

variable {E : Type} [Field E] [NumberField E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {n : ℕ}
    (y : Fin n → E) (c : Fin n → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) : ∑ k, c k • b (y k) = 0 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : Fin n → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : Fin n → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : Fin n → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_conj (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, g (a x) = b x := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  have hroot : Polynomial.aeval (b pb.gen) (minpoly ℚ_[l] (a pb.gen)) = 0 := by
    have h0 := minpoly.aeval ℚ_[l] (a pb.gen)
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range] at h0 ⊢
    simp only [← map_pow] at h0 ⊢
    exact sum_eq_zero a b h _ _ h0
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) hroot
  refine ⟨g, fun x => ?_⟩
  have : ((g : PadicAlgCl l →+* PadicAlgCl l).comp a).toRatAlgHom = b.toRatAlgHom :=
    pb.algHom_ext hg
  exact DFunLike.congr_fun this x

variable {Ω : Type} [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

end Padic

end GlobalTheory.EmbThroughCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationLtOneIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

noncomputable section

namespace GlobalTheory.EmbInj

open Formalism.BasicNotions.Loc

section Local

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_iff_norm (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact ((minpoly ℤ_[l] x).coeff n).2
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (LL : FinExt l) (x : ↥LL.1) : x ∈ OL LL ↔ ‖(x : Om l)‖ ≤ 1 := by
  rw [← isIntegral_iff_norm, OL, mem_integralClosure_iff]
  exact (isIntegral_algHom_iff (LL.1.val.restrictScalars ℤ_[l]) LL.1.val.toRingHom.injective).symm

theorem norm_algHom (K L : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective x
  have h2 := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type}
  [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : _root_.Formalism.BasicNotions.LocBridge l E Ω Gw O)

theorem norm_le_one_iff (y : ↥B.LL.1) : ‖(y : Om l)‖ ≤ 1 ↔ ∃ n : O, y = B.toLL n := by
  rw [← mem_OL_iff]
  constructor
  · intro h
    refine ⟨B.eO.symm ⟨y, h⟩, ?_⟩
    simp [LocBridge.toLL]
  · rintro ⟨n, rfl⟩
    exact (B.eO n).2

theorem toLL_inj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)

theorem exists_frac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
  by_cases h : ‖(y : Om l)‖ ≤ 1
  · obtain ⟨n, hn⟩ := (norm_le_one_iff B y).1 h
    refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
    have := congrArg B.toLL h1
    simp at this
  · have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
    obtain ⟨d, hd⟩ := (norm_le_one_iff B _).1 h'
    refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
    rw [h1, map_zero] at hd
    exact hy (inv_eq_zero.1 hd)

theorem algHom_ext (τ τ' : ↥B.Kw.1 →ₐ[ℚ_[l]] ↥B.LL.1)
    (h : ∀ x : E, τ ⟨B.j (algebraMap E Ω x), B.j_E x⟩ = τ' ⟨B.j (algebraMap E Ω x), B.j_E x⟩) :
    τ = τ' := by
  ext y
  by_contra hne
  have hpos : 0 < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 (B.j_dense y.2) _ (half_pos hpos)
  rw [dist_eq_norm] at hx
  set z : ↥B.Kw.1 := ⟨B.j (algebraMap E Ω x), B.j_E x⟩ with hz
  have e : ((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1) =
      ((τ (y - z) : ↥B.LL.1) : Om l) - (τ' (y - z) : ↥B.LL.1) := by
    rw [map_sub, map_sub, hz, h x]
    push_cast
    ring
  have h1 := norm_algHom _ _ τ (y - z)
  have h2 := norm_algHom _ _ τ' (y - z)
  have h3 := norm_sub_le ((τ (y - z) : ↥B.LL.1) : Om l) (τ' (y - z) : ↥B.LL.1)
  have h4 : ‖((y - z : ↥B.Kw.1) : Om l)‖ < ‖((τ y : ↥B.LL.1) : Om l) - (τ' y : ↥B.LL.1)‖ / 2 := hx
  rw [← e, h1, h2] at h3
  linarith

end Local

end GlobalTheory.EmbInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped Pointwise

namespace GlobalTheory.AntiRamConj

section General
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

def moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) : ValuationSubring Ω :=
  B.comap (c.symm : Ω →+* Ω)

theorem mem_moveVal (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    y ∈ moveVal c B ↔ c.symm y ∈ B := Iff.rfl

theorem moveVal_lt_one (c : Ω ≃+* Ω) (B : ValuationSubring Ω) (y : Ω) :
    (moveVal c B).valuation y < 1 ↔ B.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_moveVal, mem_moveVal, map_inv₀,
    map_eq_zero_iff _ c.symm.injective]

def conjAut (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (σ : G E Ω) : G E Ω :=
  { (c.symm.trans (σ : Ω ≃+* Ω)).trans c with
    commutes' := fun x => by
      obtain ⟨y, hy⟩ := hc x
      show c (σ (c.symm (algebraMap E Ω x))) = algebraMap E Ω x
      rw [hy, σ.commutes, ← hy, RingEquiv.apply_symm_apply] }

theorem conjAut_apply (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) (σ : G E Ω) (x : Ω) :
    conjAut c hc σ x = c (σ (c.symm x)) := rfl

theorem conjAut_mem_ine [NumberField E] (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) {B : ValuationSubring Ω}
    {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) : conjAut c hc σ ∈ Ine (F := E) (moveVal c B) := by
  have hd : σ ∈ Dec (F := E) B := hσ.1
  refine ⟨?_, fun x hx => ?_⟩
  · show conjAut c hc σ ∈ Dec (F := E) (moveVal c B)
    rw [mem_Dec]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
    obtain ⟨z, rfl⟩ := (conjAut c hc σ).surjective x
    have h1 : ((conjAut c hc σ)⁻¹ : G E Ω) (conjAut c hc σ z) = z := (conjAut c hc σ).symm_apply_apply z
    rw [h1, mem_moveVal, mem_moveVal, conjAut_apply, RingEquiv.symm_apply_apply,
      apply_mem_iff_of_mem_Dec hd]
  · rw [moveVal_lt_one, map_sub, conjAut_apply, RingEquiv.symm_apply_apply]
    apply hσ.2
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact hx

end General

theorem host_conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  let φ : D.host.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => D.host.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

theorem cc_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply
    (j.comp (algebraMap D.host.E D.nd.Om)) x).symm

theorem cc_symm_algebraMap_host (D : D7) (x : D.host.E) :
    D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  rw [RingEquiv.symm_apply_eq, cc_algebraMap_host, host_conj_conj]

theorem isPlaceOver_moveVal (D : D7) {P P' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : IsConjPl D.host P P') {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) :
    IsPlaceOver (moveVal D.ntw.cc B) P' := by
  intro y
  have hi : IsIntegral ℤ (D.host.conj (y : D.host.E)) :=
    (y.isIntegral_coe).map_of_comp_eq (RingHom.id ℤ) (D.host.conj : D.host.E →+* D.host.E) (by ext; simp)
  let x : 𝓞 D.host.E := ⟨_, hi⟩
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := rfl
  rw [moveVal_lt_one, cc_symm_algebraMap_host, ← hx, hB x]
  exact h x y (by rw [hx, host_conj_conj])

end GlobalTheory.AntiRamConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTypePrimesOfAdmissible
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles
open Formalism.MainNotions.N
open scoped Matrix Pointwise

namespace GlobalTheory.InertiaTypePrimes

section General

variable {Γ R : Type} [Group Γ] [CommRing R] {r : ℕ}

theorem mem_ker_mapRep_iff (J : Ideal R) (ρ : Γ →* GL (Fin r) R) (g : Γ) :
    g ∈ (mapRep (Ideal.Quotient.mk J) ρ).ker ↔
      ∀ a b, (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b ∈ J := by
  rw [MonoidHom.mem_ker, Units.ext_iff]
  change (Ideal.Quotient.mk J).mapMatrix ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) = 1 ↔ _
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, ← Matrix.ext_iff]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

theorem isOpen_ker_mapRep [TopologicalSpace Γ] [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (hJ : IsOpen (J : Set R)) (ρ : Γ →* GL (Fin r) R)
    (hρ : Continuous fun g => ((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R)) :
    IsOpen ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) := by
  have : ((mapRep (Ideal.Quotient.mk J) ρ).ker : Set Γ) = ⋂ a, ⋂ b,
      (fun g => (((ρ g : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) - 1) a b) ⁻¹' (J : Set R) := by
    ext g
    simp only [SetLike.mem_coe, mem_ker_mapRep_iff, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => hJ.preimage ?_
  exact (hρ.sub continuous_const).matrix_elem a b

end General

theorem isWild_of_isWildAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω) (h : IsWildAt A σ) : IsWild A σ := by
  have h1 : ∀ x : Ω, x ≠ 0 → A.valuation (σ x - x) < A.valuation x := fun x hx => by
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    have h0 : 0 < A.valuation x := zero_lt_iff.mpr (by simpa using hx)
    rw [e, map_mul]
    exact mul_lt_of_lt_one_left h0 (h x hx)
  have h2 : ∀ x : Ω, A.valuation (σ x) = A.valuation x := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact Valuation.map_eq_of_sub_lt _ (h1 x hx)
  refine ⟨⟨?_, fun x hx => ?_⟩, h1⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← h2, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    · exact (h1 x hx0).trans_le hx

section Wild

variable {E Ω R : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
  {r : ℕ} {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 E)}

end Wild

end GlobalTheory.InertiaTypePrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ToNatAddValMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.NormValExt

open IsDiscreteValuationRing

variable {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

theorem toNat_addVal_mul {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    (addVal R (a * b)).toNat = (addVal R a).toNat + (addVal R b).toNat := by
  rw [addVal_mul]
  exact ENat.toNat_add (fun h => ha ((addVal_eq_top_iff).mp h)) (fun h => hb ((addVal_eq_top_iff).mp h))

theorem nval_mul (l : ℕ) {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    BlochKatoReduction.Gen.nval R l (a * b) =
      BlochKatoReduction.Gen.nval R l a + BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.nval
  rw [toNat_addVal_mul ha hb, Nat.cast_add, add_div]

theorem vK_eq (l : ℕ) {x : FractionRing R} (hx : x ≠ 0) {a b : R} (hb : b ≠ 0)
    (h : x * algebraMap R (FractionRing R) b = algebraMap R (FractionRing R) a) :
    BlochKatoReduction.Gen.vK R l x =
      BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
  unfold BlochKatoReduction.Gen.vK
  generalize_proofs hE
  have hinj := IsFractionRing.injective R (FractionRing R)
  have key : ∀ q : R × nonZeroDivisors R,
      x * algebraMap R (FractionRing R) q.2 = algebraMap R (FractionRing R) q.1 →
      BlochKatoReduction.Gen.nval R l q.1 - BlochKatoReduction.Gen.nval R l q.2 =
        BlochKatoReduction.Gen.nval R l a - BlochKatoReduction.Gen.nval R l b := by
    intro q hq
    have hq2 : (q.2 : R) ≠ 0 := nonZeroDivisors.ne_zero q.2.2
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hb) h
    have hq1 : q.1 ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hq
      exact mul_ne_zero hx ((map_ne_zero_iff _ hinj).mpr hq2) hq
    have hcross : a * q.2 = q.1 * b := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hq]
      ring
    have hc := congrArg (BlochKatoReduction.Gen.nval R l) hcross
    rw [nval_mul l ha hq2, nval_mul l hq1 hb] at hc
    linarith
  exact key hE.choose hE.choose_spec

end GlobalTheory.NormValExt
end
