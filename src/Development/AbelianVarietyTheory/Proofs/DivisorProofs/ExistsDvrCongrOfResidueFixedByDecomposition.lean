module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariantsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvr
set_option autoImplicit false

noncomputable section

open Polynomial GlobalTheory.Published.AbVarRed IsLocalRing

namespace GlobalTheory.ValAbove

theorem partialSum_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (c : ℕ → R) (n : ℕ)
    (x : Ω) (h : ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0) {m t : ℕ} (hm : m ≤ n) (ht : t ≤ n + 1) :
    (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
  have hmem : ∀ e, e ≤ n → ∀ r : R, r • x ^ e ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
    intro e he r
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ (Set.mem_Iic.2 he)
  by_cases htm : t < m
  · rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [smul_mul_assoc, ← pow_add]
    exact hmem _ (by omega) _
  · push_neg at htm
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => c i • x ^ i) (show m ≤ n + 1 by omega)
    rw [h] at hsplit
    have e1 : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ i) * x ^ (t - m) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [smul_mul_assoc, smul_mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    have key : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = -∑ i ∈ Finset.range m, c i • x ^ (i + (t - m)) := by
      rw [e1, eq_neg_of_add_eq_zero_right hsplit, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, ← pow_add]
    rw [key]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact hmem _ (by omega) _

theorem isIntegral_of_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (n : ℕ) (x z : Ω)
    (hz : ∀ t ≤ n, z * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) :
    IsIntegral R z := by
  refine isIntegral_of_smul_mem_submodule
    (Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) ?_ (Submodule.fg_span ((Set.finite_Iic n).image _)) z ?_
  · rw [Ne, Submodule.span_eq_bot]
    push_neg
    refine ⟨1, ?_, one_ne_zero⟩
    exact ⟨0, Set.mem_Iic.2 (Nat.zero_le n), pow_zero x⟩
  · intro w hw
    refine Submodule.span_induction (fun w hw => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [smul_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => by rw [smul_eq_mul, mul_smul_comm]; exact Submodule.smul_mem _ r ha) hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [Set.mem_Iic] at ht
    rw [smul_eq_mul]
    exact hz t (by omega)

theorem exists_integral_mul_eq_of_isAbove : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω,
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV y hy
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιinj : Function.Injective ((algebraMap K Ω).comp (algebraMap R K)) :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hmemV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  have hle : ∀ r : R, V.valuation (algebraMap R Ω r) ≤ 1 := fun r => (V.valuation_le_one_iff _).2 (hmemV r)
  have hlt : ∀ r : R, ¬ IsUnit r → V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    refine lt_of_le_of_ne (hle r) fun h1 => hr ?_
    have h0 : algebraMap R Ω r ≠ 0 := by
      intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
    have hinv : (algebraMap R Ω r)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])
    have hK : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω ((algebraMap R K r)⁻¹) ∈ V
      rw [map_inv₀]; exact hinv
    rw [hV] at hK
    obtain ⟨r', hr'⟩ := hK
    have hrK : algebraMap R K r ≠ 0 := by
      intro h; apply h0; change algebraMap K Ω (algebraMap R K r) = 0; rw [h, map_zero]
    have hrr : r * r' = 1 :=
      IsFractionRing.injective R K (by rw [map_mul, hr', mul_inv_cancel₀ hrK, map_one])
    exact ⟨⟨r, r', hrr, by rw [mul_comm, hrr]⟩, rfl⟩
  have hunit : ∀ r : R, IsUnit r → V.valuation (algebraMap R Ω r) = 1 := by
    intro r hr
    obtain ⟨u, rfl⟩ := hr
    have h := congrArg (fun w => V.valuation (algebraMap R Ω w)) u.mul_inv
    simp only [map_mul, map_one] at h
    refine le_antisymm (hle _) ?_
    by_contra hlt'
    push_neg at hlt'
    have : V.valuation (algebraMap R Ω ↑u) * V.valuation (algebraMap R Ω ↑u⁻¹) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt'
    rw [h] at this
    exact lt_irrefl _ this

  classical
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have halgK : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
  have halgR : IsAlgebraic R y := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨f, hf0, hfy⟩ := halgR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∃ e : ℕ, ¬ (C (ϖ ^ (e + 1)) ∣ f) := by
    have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨e, fun hd => ?_⟩
    have hd' : ϖ ^ e * ϖ ∣ ϖ ^ e * (u : R) := by
      rw [← pow_succ, mul_comm]; rw [← hu]
      exact (C_dvd_iff_dvd_coeff _ _).1 hd _
    have : ϖ ∣ (u : R) := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd'
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
  have hdiv : ∀ e, (∀ k < e, ¬ ¬ (C (ϖ ^ (k + 1)) ∣ f)) → C (ϖ ^ e) ∣ f := by
    intro e he
    cases e with
    | zero => simp
    | succ k => exact not_not.1 (he k (Nat.lt_succ_self k))
  obtain ⟨g, hg⟩ := hdiv (Nat.find hex) (fun k hk => Nat.find_min hex hk)
  have hgunit : ∃ i, IsUnit (g.coeff i) := by
    by_contra hno
    push_neg at hno
    apply Nat.find_spec hex
    have hmax : maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hCg : C ϖ ∣ g := (C_dvd_iff_dvd_coeff _ _).2 fun i => by
      have : g.coeff i ∈ maximalIdeal R := (mem_maximalIdeal _).2 (hno i)
      rw [hmax] at this
      exact Ideal.mem_span_singleton.1 this
    have h2 := mul_dvd_mul_left (C (ϖ ^ Nat.find hex)) hCg
    rw [← hg, ← C_mul, ← pow_succ] at h2
    exact h2
  have hgy : aeval y g = 0 := by
    rw [hg, map_mul, aeval_C] at hfy
    refine (mul_eq_zero.1 hfy).resolve_left ?_
    exact fun h => pow_ne_zero _ hϖ.ne_zero (hιinj (h.trans (map_zero _).symm))
  set n := g.natDegree with hn
  set c := g.coeff with hc
  have hsum : ∑ i ∈ Finset.range (n + 1), c i • y ^ i = 0 := by
    rw [← hgy, aeval_eq_sum_range]
  obtain ⟨i₀, hi₀⟩ := hgunit
  have hS : ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi₀.ne_zero)), hi₀⟩⟩
  set j := ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).max' hS with hj
  have hjmem := Finset.max'_mem _ hS
  rw [← hj, Finset.mem_filter, Finset.mem_range] at hjmem
  have hjn : j ≤ n := Nat.le_of_lt_succ hjmem.1
  have hbig : ∀ i, j < i → i ≤ n → ¬ IsUnit (c i) := by
    intro i hji hin hu
    have := Finset.le_max' ((Finset.range (n + 1)).filter fun i => IsUnit (c i)) i
      (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hu⟩)
    rw [← hj] at this
    omega
  set b := ∑ i ∈ Finset.Ico j (n + 1), c i • y ^ (i - j) with hb
  have hyle : V.valuation y ≤ 1 := (V.valuation_le_one_iff y).2 hy
  have hvb : V.valuation b = 1 := by
    rw [hb, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero, Algebra.smul_def,
      mul_one, add_comm]
    rw [Valuation.map_add_eq_of_lt_right, hunit _ hjmem.2]
    rw [hunit _ hjmem.2]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [Algebra.smul_def, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hyle _)) (hlt _ (hbig i (by omega) (by omega)))
  refine ⟨y * b, b, ?_, ?_, hvb, rfl⟩
  · exact isIntegral_of_mul_pow_mem n y (y * b) fun t ht => by
      rw [show y * b * y ^ t = b * y ^ (t + 1) by ring]
      exact partialSum_mul_pow_mem c n y hsum hjn (by omega)
  · exact isIntegral_of_mul_pow_mem n y b fun t ht => partialSum_mul_pow_mem c n y hsum hjn (by omega)

end GlobalTheory.ValAbove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralQuotientOfValuationSubringAboveDvrStatement
open GlobalTheory.Published.AbVarRed IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω, ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧ ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  first | exact @GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | exact GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove | (intros; apply GlobalTheory.ValAbove.exists_integral_mul_eq_of_isAbove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecomposition
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResidueFixed

theorem residue_fixed_mem : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ x ∈ V, (∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → V.valuation (σ x - x) < 1) → ∃ r : R, V.valuation (x - algebraMap K Ω (algebraMap R K r)) < 1 := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV x hx hfix
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have h : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact h
  let φ : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV

  have hmR : ∀ r ∈ maximalIdeal R, V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    by_contra hlt
    have h1 : V.valuation (algebraMap R Ω r) = 1 :=
      le_antisymm (V.valuation_le_one (φ r)) (not_lt.1 hlt)
    have hu : IsUnit (φ r) := (V.valuation_eq_one_iff (φ r)).2 h1
    have hne : algebraMap R K r ≠ 0 := by
      intro h0
      rw [show algebraMap R Ω r = algebraMap K Ω (algebraMap R K r) from rfl, h0, map_zero, map_zero] at h1
      exact zero_ne_one h1
    have hinv : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω (algebraMap R K r)⁻¹ ∈ V
      obtain ⟨u, hu'⟩ := hu
      have : ((u⁻¹ : Vˣ) : V) * φ r = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V)) : Ω) = algebraMap K Ω (algebraMap R K r)⁻¹ := by
        rw [map_inv₀]
        refine (eq_inv_of_mul_eq_one_left ?_)
        exact congrArg Subtype.val this
      rw [← h2]; exact SetLike.coe_mem _
    rw [hV] at hinv
    obtain ⟨r', hr'⟩ := hinv
    apply (mem_maximalIdeal r).1 hr
    refine isUnit_iff_exists_inv.2 ⟨r', IsFractionRing.injective R K ?_⟩
    rw [map_mul, hr', map_one, mul_inv_cancel₀ hne]

  let B := integralClosure R Ω
  have hBV : ∀ b : B, (b : Ω) ∈ V := by
    intro b
    obtain ⟨p, hpm, hp⟩ := b.2
    have hint : IsIntegral V (b : Ω) := by
      refine ⟨p.map φ, hpm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    rw [← hy]; exact y.2
  let ψ : B →+* V := (B.val : B →+* Ω).codRestrict V.toSubring hBV
  let Q : Ideal B := (maximalIdeal V).comap ψ
  have hQ : ∀ b : B, b ∈ Q ↔ V.valuation (b : Ω) < 1 := fun b => V.valuation_lt_one_iff (ψ b)
  let G := Ω ≃ₐ[K] Ω
  have hc : SMulCommClass G R Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : ContinuousSMul G B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant R B G := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral R k := by
      have h2 : IsIntegral R (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff ).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hQP : Q.LiesOver (maximalIdeal R) := by
    constructor
    refine le_antisymm (fun r hr => ?_) (IsLocalRing.le_maximalIdeal ?_)
    · change algebraMap R B r ∈ Q
      rw [hQ]; exact hmR r hr
    · intro h1
      have h : (1 : R) ∈ Q.comap (algebraMap R B) := by
        change (1 : R) ∈ Q.under R
        rw [h1]; exact Submodule.mem_top
      rw [Ideal.mem_comap, map_one, hQ] at h
      simp at h
  have hQmax : Q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal Q (maximalIdeal R)
  letI := Ideal.Quotient.field (maximalIdeal R)
  letI := Ideal.Quotient.field Q
  haveI hN : Normal (R ⧸ maximalIdeal R) (B ⧸ Q) := GlobalTheory.T.residue_normal_of_profinite_invariants G (maximalIdeal R) Q
  haveI : PerfectField (R ⧸ maximalIdeal R) := ‹PerfectField (ResidueField R)›
  haveI : IsGalois (R ⧸ maximalIdeal R) (B ⧸ Q) := {}

  have hBle : ∀ b : B, V.valuation (b : Ω) ≤ 1 := fun b => V.valuation_le_one (ψ b)

  have hsub : ∀ g ∈ MulAction.stabilizer G Q, ∀ y ∈ V, g y ∈ V := by
    intro g hg y hy
    obtain ⟨a, s, ha, hs, hsv, hys⟩ := GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr R K Ω V hV y hy
    let a' : B := ⟨a, ha⟩
    let s' : B := ⟨s, hs⟩
    have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
    have hgs : g • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : g • s' ∈ g • Q := by rw [MulAction.mem_stabilizer_iff.1 hg]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hgsv : V.valuation (g s) = 1 := by
      rw [hQ] at hgs
      exact le_antisymm (hBle (g • s')) (not_lt.1 hgs)
    have hga : V.valuation (g a) ≤ 1 := hBle (g • a')
    apply V.mem_of_valuation_le_one
    have : g y * g s = g a := by rw [← map_mul, hys]
    rw [← this, map_mul, hgsv, _root_.mul_one] at hga
    exact hga
  have hstabV : ∀ g ∈ MulAction.stabilizer G Q, g • V = V := by
    intro g hg
    ext z
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro hz
      have := hsub g hg _ hz
      have e : g (g⁻¹ • z) = z := smul_inv_smul g z
      rwa [e] at this
    · intro hz
      exact hsub g⁻¹ (inv_mem hg) z hz

  obtain ⟨a, s, ha, hs, hsv, hxs⟩ := GlobalTheory.T.exists_integral_quotient_of_valuationSubring_above_dvr R K Ω V hV x hx
  let a' : B := ⟨a, ha⟩
  let s' : B := ⟨s, hs⟩
  have hs'Q : s' ∉ Q := by rw [hQ]; exact fun h => (ne_of_lt h) hsv
  have hsne : Ideal.Quotient.mk Q s' ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  let ξ : B ⧸ Q := Ideal.Quotient.mk Q a' / Ideal.Quotient.mk Q s'
  have hξ : ∀ τ : (B ⧸ Q) ≃ₐ[R ⧸ maximalIdeal R] (B ⧸ Q), τ ξ = ξ := by
    intro τ
    obtain ⟨⟨σ, hσQ⟩, hστ⟩ :=
      Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G) (maximalIdeal R) Q τ
    have hlt := hfix σ (hstabV σ hσQ)
    have hσs : σ • s' ∉ Q := by
      intro h
      apply hs'Q
      have h' : σ • s' ∈ σ • Q := by rw [MulAction.mem_stabilizer_iff.1 hσQ]; exact h
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h'
      exact h'
    have hσsv : V.valuation (σ s) = 1 := by
      have h := hσs
      rw [hQ] at h
      exact le_antisymm (hBle (σ • s')) (not_lt.1 h)
    have hσs0 : Ideal.Quotient.mk Q (σ • s') ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    rw [← hστ]
    simp only [ξ, map_div₀, Ideal.Quotient.stabilizerHom_apply]
    change Ideal.Quotient.mk Q (σ • a') / Ideal.Quotient.mk Q (σ • s') = _
    rw [div_eq_div_iff hσs0 hsne, ← map_mul, ← map_mul, Ideal.Quotient.eq, hQ]
    have e : ((σ • a' * s' - a' * σ • s' : B) : Ω) = (σ x - x) * s * σ s := by
      change σ a * s - a * σ s = _
      rw [← hxs, map_mul]; ring
    rw [e, map_mul, map_mul, hsv, hσsv, _root_.mul_one, _root_.mul_one]
    exact hlt
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := R ⧸ maximalIdeal R) ξ).2 hξ
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨r, ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap R B r) = ξ := hc
  have h2 : Ideal.Quotient.mk Q (algebraMap R B r * s') = Ideal.Quotient.mk Q a' := by
    rw [map_mul, h1, div_mul_cancel₀ _ hsne]
  rw [Ideal.Quotient.eq, hQ] at h2
  have e : ((algebraMap R B r * s' - a' : B) : Ω) = (algebraMap K Ω (algebraMap R K r) - x) * s := by
    change algebraMap K Ω (algebraMap R K r) * s - a = _
    rw [← hxs]; ring
  rw [e, map_mul, hsv, _root_.mul_one, Valuation.map_sub_swap] at h2
  exact h2

end GlobalTheory.ResidueFixed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCongrOfResidueFixedByDecompositionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_congr_of_residue_fixed_by_decomposition : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ x ∈ V, (∀ σ : Ω ≃ₐ[K] Ω, σ • V = V → V.valuation (σ x - x) < 1) → ∃ r : R, V.valuation (x - algebraMap K Ω (algebraMap R K r)) < 1 := by
  first | exact @GlobalTheory.ResidueFixed.residue_fixed_mem | exact GlobalTheory.ResidueFixed.residue_fixed_mem | (intros; apply GlobalTheory.ResidueFixed.residue_fixed_mem <;> assumption)
end
