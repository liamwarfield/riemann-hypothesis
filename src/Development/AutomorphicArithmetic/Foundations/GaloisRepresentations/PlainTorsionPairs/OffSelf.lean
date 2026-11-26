module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.RedAbs
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ComplY
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IneInclOntoUnits
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NiceAt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FxTwflag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.FixLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin GlobalTheory.CompHt.fintypePsi Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.PlaceFree
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.WtUnit
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.W

namespace UpperTheory.V.J.Wu

section Ball

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_near {u : Qbar l} {r : ℝ} (hr : r ≤ 1) (h : ‖u - 1‖ ≤ r) : ‖u‖ ≤ 1 := by
  have e : u = (u - 1) + 1 := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans hr) (by simp))

theorem near_mul {u v : Qbar l} {r : ℝ} (hr : r ≤ 1) (hu : ‖u - 1‖ ≤ r) (hv : ‖v - 1‖ ≤ r) :
    ‖u * v - 1‖ ≤ r := by
  have e : u * v - 1 = (u - 1) * v + (v - 1) := by ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hv)
  rw [norm_mul]
  calc ‖u - 1‖ * ‖v‖ ≤ ‖u - 1‖ * 1 := by
        gcongr
        exact norm_le_one_of_near hr hv
    _ ≤ r := by simpa using hu

theorem near_pow {u : Qbar l} {r : ℝ} (hr : r ≤ 1) (hu : ‖u - 1‖ ≤ r) (n : ℕ) : ‖u ^ n - 1‖ ≤ r := by
  induction n with
  | zero => simpa using (norm_nonneg _).trans hu
  | succ n ih => rw [pow_succ]; exact near_mul hr ih hu

theorem ball_lt : ((l : ℝ)⁻¹) ^ 2 < (l : ℝ)⁻¹ := by
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h0 : 0 < (l : ℝ)⁻¹ := by positivity
  have h1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  nlinarith

theorem ball_le : ((l : ℝ)⁻¹) ^ 2 ≤ 1 := by
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact ball_lt.le.trans h1.le

theorem eq_one_of_pow_eq_one {u : Qbar l} (hu : ‖u - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2) {n : ℕ} (hn : 0 < n)
    (h : u ^ n = 1) : u = 1 := by
  by_contra hne
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, h⟩
  have ho : orderOf u ≠ 0 := hfin.orderOf_pos.ne'
  have ho1 : orderOf u ≠ 1 := by simpa [orderOf_eq_one_iff] using hne
  have hp : (orderOf u).minFac.Prime := Nat.minFac_prime ho1
  have hpd : (orderOf u).minFac ∣ orderOf u := Nat.minFac_dvd _
  obtain ⟨p, hpe⟩ : ∃ p, p = (orderOf u).minFac := ⟨_, rfl⟩
  rw [← hpe] at hp hpd
  obtain ⟨v, hve⟩ : ∃ v, v = u ^ (orderOf u / p) := ⟨_, rfl⟩
  have hv : orderOf v = p := by rw [hve]; exact orderOf_pow_orderOf_div ho hpd
  have hv1 : v ≠ 1 := fun e => hp.one_lt.ne' (by rw [← hv, e, orderOf_one])
  have hvp : v ^ p = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hnear : ‖v - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2 := by rw [hve]; exact near_pow ball_le hu _
  have hS : ∑ i ∈ Finset.range p, v ^ i = 0 := by
    have := geom_sum_mul v p
    rw [hvp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hv1)
  have hd : (p : Qbar l) = -∑ i ∈ Finset.range p, (v ^ i - 1) := by
    simp [Finset.sum_sub_distrib, hS]
  have hn1 : ‖(p : Qbar l)‖ ≤ ((l : ℝ)⁻¹) ^ 2 := by
    rw [hd, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      fun i _ => near_pow ball_le hnear i
  have hn2 : (l : ℝ)⁻¹ ≤ ‖(p : Qbar l)‖ := by
    have e : (p : Qbar l) = algebraMap ℚ_[l] (Qbar l) (p : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    by_cases hpl : p = l
    · subst hpl
      rw [Padic.norm_p]
    · have h1 : ‖(p : ℚ_[l])‖ = 1 :=
        Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes Fact.out hp).2 (Ne.symm hpl))
      rw [h1]
      have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
      exact (inv_lt_one_of_one_lt₀ (by linarith)).le
  linarith [ball_lt (l := l)]

theorem norm_int_le_one {F : Type} [Field F] [NumberField F] (c : F →+* Qbar l) (x : 𝓞 F) :
    ‖c x‖ ≤ 1 := by
  have h1 : IsIntegral ℤ (c x) := (RingOfIntegers.isIntegral_coe x).map c.toIntAlgHom
  have h : IsIntegral ℤ_[l] (c x) := h1.tower_top
  have hi : IsIntegral ℚ_[l] (c x) := Algebra.IsIntegral.isIntegral _
  have h0 : ‖c x‖ = spectralValue (minpoly ℚ_[l] (c x)) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

end Ball

section Place

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

theorem emb_val_lt (j : Emb l w) {y : w.adicCompletion F} (hy : Valued.v y < 1) : ‖j.1 y‖ < 1 := by
  have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one hy)
  rw [map_zero] at h2
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun m => map_pow _ _ _)

theorem emb_lt (j : Emb l w) {x : 𝓞 F} (hx : x ∈ w.asIdeal) :
    ‖j.1 (algebraMap F (w.adicCompletion F) (x : F))‖ < 1 := by
  refine emb_val_lt j ?_
  rw [show algebraMap F (w.adicCompletion F) (x : F) = ((x : F) : w.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact (w.valuation_lt_one_iff_mem x).2 hx

theorem emb_lt_iff (j : Emb l w) (x : 𝓞 F) :
    ‖j.1 (algebraMap F (w.adicCompletion F) (x : F))‖ < 1 ↔ x ∈ w.asIdeal := by
  refine ⟨fun h => ?_, emb_lt j⟩
  by_contra hx
  obtain ⟨y, i, hi, e⟩ := w.isMaximal.exists_inv hx
  let c : F →+* Qbar l := j.1.comp (algebraMap F (w.adicCompletion F))
  have h1 : ‖c ((y : F) * (x : F))‖ < 1 := by
    rw [map_mul, norm_mul]
    calc ‖c y‖ * ‖c x‖ ≤ 1 * ‖c x‖ := by
          gcongr
          exact norm_int_le_one c y
      _ < 1 := by
          rw [one_mul]
          exact h
  have h2 : ‖c (i : F)‖ < 1 := emb_lt j hi
  have e' : c ((y : F) * (x : F)) + c (i : F) = 1 := by
    rw [← map_add (f := _), ← map_one c]
    congr 1
    exact_mod_cast congrArg (fun t : 𝓞 F => (t : F)) e
  have h3 := IsUltrametricDist.norm_add_le_max (c ((y : F) * (x : F))) (c (i : F))
  rw [e', norm_one] at h3
  exact absurd h3 (not_le.2 (max_lt h1 h2))

theorem emb_val_eq (j : Emb l w) {y : w.adicCompletion F} (hy : ‖j.1 y‖ = 1) : Valued.v y = 1 := by
  rcases lt_trichotomy (Valued.v y) 1 with h | h | h
  · exact absurd hy (emb_val_lt j h).ne
  · exact h
  · have hy0 : y ≠ 0 := fun e => by simp [e] at hy
    have h1 : Valued.v y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
    have h2 := emb_val_lt j h1
    rw [map_inv₀, norm_inv, hy, inv_one] at h2
    exact absurd h2 (lt_irrefl _)

theorem liesOver (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) := by
  haveI := w.isMaximal
  have hp : (Ideal.span {(l : ℤ)}).IsMaximal := by
    refine PrincipalIdealRing.isMaximal_of_irreducible ?_
    exact (Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)).irreducible
  refine ⟨hp.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  simpa using hl

theorem norm_data (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : ℚ_[l] →+* w.adicCompletion F, (∀ (τ : Emb l w) (c : ℚ_[l]), τ.1 (φ c) = algebraMap ℚ_[l] (Qbar l) c) ∧
      Nonempty (Emb l w) ∧ Finite (Emb l w) ∧
      ∀ z : w.adicCompletion F, ∃ c : ℚ_[l], ∏ᶠ τ : Emb l w, τ.1 z = algebraMap ℚ_[l] (Qbar l) c := by
  haveI := liesOver hl
  obtain ⟨-, φ, -, hφ, -⟩ := KStar.Ram.existsUnique_padic_hom w l
  letI : Algebra ℚ_[l] (w.adicCompletion F) := φ.toAlgebra
  haveI : ContinuousSMul ℚ_[l] (w.adicCompletion F) := continuousSMul_of_algebraMap _ _ hφ
  haveI : FiniteDimensional ℚ_[l] (w.adicCompletion F) := (KStar.Ram.finrank_compl w l).1
  haveI : CharZero (w.adicCompletion F) := φ.charZero_iff φ.injective |>.1 inferInstance
  have hcomp : ∀ (τ : Emb l w) (c : ℚ_[l]), τ.1 (φ c) = algebraMap ℚ_[l] (Qbar l) c := fun τ c => by
    have := (Padic.denseRange_ratCast l).equalizer (g := fun x => τ.1 (φ x)) (h := algebraMap ℚ_[l] (Qbar l))
      (τ.2.comp hφ) (continuous_algebraMap _ _) (by
        funext q
        simp only [Function.comp_apply, map_ratCast])
    exact congrFun this c
  have hc : ∀ σ : w.adicCompletion F →ₐ[ℚ_[l]] Qbar l, Continuous σ := fun σ =>
    LinearMap.continuous_of_finiteDimensional σ.toLinearMap
  let e : (w.adicCompletion F →ₐ[ℚ_[l]] Qbar l) ≃ Emb l w :=
    { toFun := fun σ => ⟨σ, hc σ⟩
      invFun := fun τ => { τ.1 with commutes' := hcomp τ }
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨φ, hcomp, ⟨e (IsAlgClosed.lift)⟩, Finite.of_equiv _ e, fun z => ⟨Algebra.norm ℚ_[l] z, ?_⟩⟩
  rw [Algebra.norm_eq_prod_embeddings ℚ_[l] (Qbar l) z, ← finprod_eq_prod_of_fintype,
    ← finprod_comp_equiv e]
  rfl

end Place

section Unit

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] {w : Plc F}

theorem norm_eq_one_of_near {u : Qbar l} (h : ‖u - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2) : ‖u‖ = 1 := by
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h1 : ‖u - 1‖ < 1 := h.trans_lt (ball_lt.trans (inv_lt_one_of_one_lt₀ (by linarith)))
  have e : (1 : Qbar l) = u + -(u - 1) := by ring
  have h2 : (1 : ℝ) ≤ max ‖u‖ ‖u - 1‖ := by
    have := IsUltrametricDist.norm_add_le_max u (-(u - 1))
    rwa [← e, norm_one, norm_neg] at this
  have h3 : 1 ≤ ‖u‖ := by
    rcases le_max_iff.1 h2 with h4 | h4
    · exact h4
    · exact absurd h4 (not_le.2 h1)
  exact le_antisymm (norm_le_one_of_near ball_le h) h3

theorem exists_unit (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (x : 𝓞 F) (τ₁ τ₂ : Emb l w)
    (hne : τ₁.1 (algebraMap F (w.adicCompletion F) (x : F)) ≠ τ₂.1 (algebraMap F (w.adicCompletion F) (x : F))) :
    ∃ y : (w.adicCompletion F)ˣ, Valued.v (y : w.adicCompletion F) = 1 ∧
      ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) = 1 ∧
      ∀ (τ : Emb l w) (m : ℕ), 0 < m → τ.1 (y : w.adicCompletion F) ^ m ≠ 1 := by
  obtain ⟨φ, hφ, ⟨τ₀⟩, hfin, hN⟩ := norm_data hl
  haveI := hfin
  letI := Fintype.ofFinite (Emb l w)
  obtain ⟨z, hze⟩ : ∃ z : w.adicCompletion F, z = 1 + (l : w.adicCompletion F) ^ 2 * algebraMap F _ (x : F) := ⟨_, rfl⟩
  have hlnorm : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
    rw [e, norm_algebraMap', Padic.norm_p]
  have hz : ∀ τ : Emb l w, ‖τ.1 z - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2 := fun τ => by
    have e : τ.1 z - 1 = ((l : ℕ) : Qbar l) ^ 2 * (τ.1.comp (algebraMap F (w.adicCompletion F))) (x : F) := by
      rw [hze]
      simp
    rw [e, norm_mul, norm_pow, hlnorm]
    have := norm_int_le_one (τ.1.comp (algebraMap F (w.adicCompletion F))) x
    have h0 : (0 : ℝ) ≤ ((l : ℝ)⁻¹) ^ 2 := by positivity
    nlinarith
  have hz1 : ∀ τ : Emb l w, ‖τ.1 z‖ = 1 := fun τ => norm_eq_one_of_near (hz τ)
  have hz0 : z ≠ 0 := fun e => by
    have := hz1 τ₀
    simp [e] at this
  obtain ⟨c, hc⟩ := hN z
  rw [finprod_eq_prod_of_fintype] at hc
  have hcn : ‖algebraMap ℚ_[l] (Qbar l) c‖ = 1 := by
    rw [← hc, norm_prod]
    exact Finset.prod_eq_one fun τ _ => hz1 τ
  have hc0 : algebraMap ℚ_[l] (Qbar l) c ≠ 0 := fun e => by simp [e] at hcn
  have hφ0 : φ c ≠ 0 := fun e => hc0 (by rw [← hφ τ₀ c, e, map_zero])
  obtain ⟨d, hd⟩ : ∃ d, d = Fintype.card (Emb l w) := ⟨_, rfl⟩
  have hdpos : 0 < d := by
    rw [hd]
    exact Fintype.card_pos_iff.2 ⟨τ₀⟩
  have hy : ∀ τ : Emb l w, τ.1 (z ^ d * (φ c)⁻¹) = τ.1 z ^ d * (algebraMap ℚ_[l] (Qbar l) c)⁻¹ := fun τ => by
    rw [map_mul, map_pow, map_inv₀, hφ]
  have hy0 : z ^ d * (φ c)⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) (inv_ne_zero hφ0)
  refine ⟨Units.mk0 _ hy0, ?_, ?_, fun τ m hm e => ?_⟩
  · refine emb_val_eq τ₀ ?_
    rw [Units.val_mk0, hy, norm_mul, norm_pow, hz1, norm_inv, hcn]
    simp
  · rw [Units.val_mk0, finprod_eq_prod_of_fintype]
    simp only [hy]
    rw [Finset.prod_mul_distrib, Finset.prod_pow, ← hc, Finset.prod_const, Finset.card_univ, ← hd, ← mul_pow,
      mul_inv_cancel₀ (by rw [hc]; exact hc0), one_pow]
  · have hy1 : (z ^ d * (φ c)⁻¹) ^ m = 1 := τ.1.injective (by rw [map_pow, map_one]; simpa using e)
    rw [mul_pow, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hφ0), ← pow_mul] at hy1
    have h1 : ∀ τ : Emb l w, τ.1 z ^ (d * m) = algebraMap ℚ_[l] (Qbar l) c ^ m := fun τ => by
      rw [← map_pow, hy1, map_pow, hφ]
    have hz2 : τ₂.1 z ≠ 0 := fun e => by
      have := hz1 τ₂
      simp [e] at this
    have hu : ‖τ₁.1 z / τ₂.1 z - 1‖ ≤ ((l : ℝ)⁻¹) ^ 2 := by
      have e1 : τ₁.1 z / τ₂.1 z - 1 = ((τ₁.1 z - 1) + -(τ₂.1 z - 1)) / τ₂.1 z := by
        field_simp
        ring
      rw [e1, norm_div, hz1, div_one]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz _) ?_)
      rw [norm_neg]
      exact hz _
    have hup : (τ₁.1 z / τ₂.1 z) ^ (d * m) = 1 := by
      rw [div_pow, h1, h1, div_self (pow_ne_zero _ hc0)]
    have h2 := eq_one_of_pow_eq_one hu (Nat.mul_pos hdpos hm) hup
    have h3 : τ₁.1 z = τ₂.1 z := (div_eq_one_iff_eq hz2).1 h2
    apply hne
    rw [hze] at h3
    simp only [map_add (f := _), map_one, map_mul, map_pow, map_natCast, add_right_inj] at h3
    exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) h3

end Unit

section Sep

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [CharZero Ω] [Algebra L Ω] {l : ℕ} [Fact l.Prime]

theorem exists_sep [Normal ℚ L] {A : ValuationSubring Ω} {w : Plc L} (h : IsPlaceOver A w)
    (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (g : G ℚ Ω) (hg : g ∈ Dec (F := ℚ) A) (x : L)
    (hx : g (algebraMap L Ω x) ≠ algebraMap L Ω x) :
    ∃ (b : 𝓞 L) (τ₁ τ₂ : Emb l w), τ₁.1 (algebraMap L (w.adicCompletion L) (b : L)) ≠
      τ₂.1 (algebraMap L (w.adicCompletion L) (b : L)) := by
  obtain ⟨-, -, ⟨τ₀⟩, -, -⟩ := norm_data hl
  let g' : L ≃ₐ[ℚ] L := g.restrictNormal L
  have hg' : ∀ y : L, algebraMap L Ω (g' y) = g (algebraMap L Ω y) := fun y => g.restrictNormal_commutes L y
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 L, g' (b : L) ≠ (b : L) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (K := L) x
    apply hx
    have e1 : g' (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a := hcon a
    have e2 : g' (algebraMap (𝓞 L) L c) = algebraMap (𝓞 L) L c := hcon c
    rw [← hg', map_div₀, e1, e2]
  let c : L →+* Qbar l := (τ₀.1.comp (algebraMap L (w.adicCompletion L))).comp (g' : L →+* L)
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding L l c
  have huw : u = w := by
    refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
    let a' : 𝓞 L := ⟨g' a, (RingOfIntegers.isIntegral_coe a).map g'⟩
    have e1 : ‖c a‖ < 1 ↔ a' ∈ w.asIdeal := emb_lt_iff τ₀ a'
    have e0 : a ∈ u.asIdeal ↔ u.valuation L (a : L) < 1 := (u.valuation_lt_one_iff_mem a).symm
    rw [e0, hu, e1, ← h a', ← h a]
    change A.valuation (algebraMap L Ω (g' a)) < 1 ↔ _
    rw [hg']
    exact valuation_apply_lt_one_iff hg _
  subst huw
  obtain ⟨j, hj, hjc⟩ := GlobalTheory.exists_continuous_extension_adicCompletion L l c u hu
  refine ⟨b, τ₀, ⟨j, hj⟩, fun e => hb ?_⟩
  have e2 : j (algebraMap L (u.adicCompletion L) (b : L)) = c (b : L) := DFunLike.congr_fun hjc _
  have e3 : τ₀.1 (algebraMap L (u.adicCompletion L) (b : L)) = c (b : L) := e.trans e2
  exact ((τ₀.1.comp (algebraMap L (u.adicCompletion L))).injective e3).symm

end Sep

end UpperTheory.V.J.Wu
end
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

section SlopeTestRemainingChoices

open IsDedekindDomain GlobalTheory.LocLanglands GlobalTheory.WeilDeligne UpperTheory.V.W

private theorem free_of {K : Type} [Field K] (α β : Fin 3 → Kˣ) (T : Kˣ) (hT : ∀ m : ℕ, 0 < m → T ^ m ≠ 1)
    (hβ : ∀ i, ∃ N : ℕ, 0 < N ∧ β i ^ N = 1) (heq : ∀ i : Fin 3, α i * β i = T ^ (-((i : ℕ) : ℤ))) :
    Pr.FreeRatios α := by
  intro i j hij m hm hαm
  obtain ⟨Ni, hNi, hbi⟩ := hβ i
  obtain ⟨Nj, hNj, hbj⟩ := hβ j
  have key : ∀ k : Fin 3, ∀ n : ℕ, β k ^ n = 1 → α k ^ n = T ^ (-((k : ℕ) : ℤ) * (n : ℤ)) := by
    intro k n hn
    have hk : α k = T ^ (-((k : ℕ) : ℤ)) * (β k)⁻¹ := eq_mul_inv_of_mul_eq (heq k)
    rw [hk, mul_pow, inv_pow, hn, inv_one, mul_one, ← zpow_natCast, ← zpow_mul]
  have hM : α i ^ (m * (Ni * Nj)) = α j ^ (m * (Ni * Nj)) := by
    rw [pow_mul (α i), pow_mul (α j), hαm]
  rw [key i _ (by rw [show m * (Ni * Nj) = Ni * (m * Nj) by ring, pow_mul, hbi, one_pow]),
    key j _ (by rw [show m * (Ni * Nj) = Nj * (m * Ni) by ring, pow_mul, hbj, one_pow])] at hM
  have hfin : IsOfFinOrder T := by
    rw [isOfFinOrder_iff_zpow_eq_one]
    refine ⟨-((i : ℕ) : ℤ) * ((m * (Ni * Nj) : ℕ) : ℤ) - -((j : ℕ) : ℤ) * ((m * (Ni * Nj) : ℕ) : ℤ), ?_, ?_⟩
    · intro h0
      apply hij
      have hMpos : (0 : ℤ) < ((m * (Ni * Nj) : ℕ) : ℤ) := by positivity
      have hz : (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) * ((m * (Ni * Nj) : ℕ) : ℤ) = 0 := by linarith
      rcases mul_eq_zero.1 hz with h | h
      · exact Fin.ext (by omega)
      · omega
    · rw [zpow_sub, hM, mul_inv_cancel]
  obtain ⟨n, hn, hTn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  exact hT n hn hTn

private theorem prod_wt {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [NumberField F] {w : Plc F} (τ₀ : Emb l w)
    (y : (w.adicCompletion F)ˣ) (hP : ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) = 1) (hh : Emb l w → ℤ) (j : ℤ)
    (h0 : hh τ₀ = 2 * j) (h1 : ∀ τ, τ ≠ τ₀ → hh τ = j) :
    ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion F) ^ (-hh τ) = τ₀.1 (y : w.adicCompletion F) ^ (-j) := by
  classical
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  letI := Fintype.ofFinite (Emb l w)
  have hy : ∀ τ : Emb l w, τ.1 (y : w.adicCompletion F) ≠ 0 := fun τ =>
    (map_ne_zero τ.1).2 y.ne_zero
  have e : ∀ τ : Emb l w, τ.1 (y : w.adicCompletion F) ^ (-hh τ) = τ.1 (y : w.adicCompletion F) ^ (-j) *
      (if τ = τ₀ then τ₀.1 (y : w.adicCompletion F) ^ (-j) else 1) := fun τ => by
    by_cases hτ : τ = τ₀
    · subst hτ
      rw [if_pos rfl, h0, ← zpow_add₀ (hy τ)]
      congr 1
      ring
    · rw [if_neg hτ, h1 τ hτ, mul_one]
  rw [finprod_eq_prod_of_fintype] at hP ⊢
  simp only [e]
  rw [Finset.prod_mul_distrib, Finset.prod_zpow, hP, one_zpow, one_mul, Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
private theorem art_elt (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (y : (w.adicCompletion L)ˣ)
    (hv : Valued.v (y : w.adicCompletion L) = 1) (hP : ∏ᶠ τ : Emb l w, τ.1 (y : w.adicCompletion L) = 1) :
    ∃ (σ : Ine (F := L) A) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧ a (ineIncl h σ) = y ∧
      cycBar L Ω l (σ : G L Ω) = 1 := by
  obtain ⟨a, ha⟩ := UpperTheory.V.Loc.laArtin hG h
  have hv' : ValuativeRel.valuation (w.adicCompletion L) (y : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := .ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 hv
  obtain ⟨σ, hσ⟩ := (GlobalTheory.PsType.ineIncl_onto_units L Ω A w h a ha).1 y hv'
  refine ⟨σ, a, ha, hσ, ?_⟩
  have hc := (UpperTheory.V.Loc.laCyc hG h hl).2 a ha σ
  simp only [hσ, neg_neg, zpow_one, hP, MonoidHom.one_apply, mul_one] at hc
  ext
  exact hc

private theorem place_free (hG : GlobalTheory.Published.GlobalArtinReciprocity) {L Ω : Type} [Field L] [NumberField L] [Field Ω]
    [CharZero Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc L}
    (h : IsPlaceOver A w) (hl : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (τ₀ : Emb l w) (b : 𝓞 L) (τ₁ τ₂ : Emb l w)
    (hne : τ₁.1 (algebraMap L (w.adicCompletion L) (b : L)) ≠ τ₂.1 (algebraMap L (w.adicCompletion L) (b : L)))
    (ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ) (ph : Fin 3 → Ine (F := L) A →* (Qbar l)ˣ) (hh : Fin 3 → Emb l w → ℤ)
    (h0 : ∀ j : Fin 3, hh j τ₀ = 2 * ((j : ℕ) : ℤ)) (h1 : ∀ (j : Fin 3) (τ : Emb l w), τ ≠ τ₀ → hh j τ = ((j : ℕ) : ℤ))
    (hp : ∀ j, IsWtPart h (ψ j) (hh j) (ph j)) :
    ∃ g : Dec (F := L) A, cycBar L Ω l (g : G L Ω) = 1 ∧ Pr.FreeRatios fun i => ψ i g := by
  obtain ⟨y, hyv, hyP, hyT⟩ := UpperTheory.V.J.Wu.exists_unit hl b τ₁ τ₂ hne
  obtain ⟨σ, a, ha, hσ, hcyc⟩ := art_elt hG h hl y hyv hyP
  refine ⟨Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ), hcyc, ?_⟩
  have hz : τ₀.1 (y : w.adicCompletion L) ≠ 0 := (map_ne_zero τ₀.1).2 y.ne_zero
  haveI : CompactSpace (Ine (F := L) A) :=
    isCompact_iff_compactSpace.1 (ReciprocityTheory.Gal.isClosed_Ine A).isCompact
  apply free_of (fun i => ψ i (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ)))
    (fun i => ph i σ) (Units.mk0 _ hz)
  · intro m hm h1
    apply hyT τ₀ m hm
    have h2 := congrArg Units.val h1
    simpa using h2
  · intro i
    haveI := Subgroup.quotient_finite_of_isOpen _ (hp i).1
    refine ⟨(ph i).ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_⟩
    rw [← map_pow]
    exact (ph i).mem_ker.1 (Subgroup.pow_index_mem _ σ)
  · intro i
    ext
    have hw := (hp i).2 a ha σ
    rw [hσ, prod_wt τ₀ y hyP (hh i) ((i : ℕ) : ℤ) (h0 i) (h1 i)] at hw
    simpa using hw

private theorem mem_G' {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} (V : s.Lev) (v : Vl l L) (g : Dec (F := L) (s.A v))
    (hc : cycBar L Ω l (g : G L Ω) = 1) : V.frame.φ v g ∈ V.frame.G' := by
  rw [UpperTheory.V.W.GFrame.G', MonoidHom.mem_ker]
  change V.ε ((toGS Ω V.S') (resP L Ω (g : G L Ω))) = 1
  have h1 : V.ε ((toGS Ω V.S') (resP L Ω (g : G L Ω))) = cycZ L Ω l (g : G L Ω) := by
    rw [← MonoidHom.comp_apply, V.hε]
    rfl
  rw [h1]
  have hv := congrArg Units.val hc
  simp only [GlobalTheory.GalOfCusp.cycBar, MonoidHom.comp_apply, Units.coe_map, Units.val_one] at hv
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  apply Units.ext
  apply hinj
  rw [Units.val_one, map_one]
  exact hv

end SlopeTestRemainingChoices

theorem UpperTheory.V.J.wtEx :
    GlobalTheory.Published.GlobalArtinReciprocity → WtEx := by
  intro hG Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hlink L _ _ _ _ _ Φ k c₁ _ f ka R hlarge hka
  classical
  refine ⟨fun v j τ => if τ = Classical.choice ⟨τ⟩ then 2 * ((j : ℕ) : ℤ) else ((j : ℕ) : ℤ), ?_, ?_⟩
  · intro v τ a b hab
    have hab' : (a : ℕ) < b := hab
    dsimp only
    split_ifs <;> omega
  · intro x hx v
    change UpperTheory.V.W.Vl l L at v
    obtain ⟨ph, hp, -⟩ := hx.2 v
    haveI := k.ab
    have hlw : ((l : ℕ) : 𝓞 L) ∈ (R.s.w v.1).asIdeal := by
      apply (R.s.hw v.1 _).1
      have hA := (R.s.hA v.1 _).2 v.2
      simpa only [map_natCast] using hA
    have hbig : 5 < Φ.dv (R.K.e v) := R.big.2 (R.K.e v)
    rw [k.dv (R.K.e v)] at hbig
    obtain ⟨g, hgD, hgU⟩ : ∃ g ∈ Dec (F := ℚ) (k.pl (R.K.e v)), g ∉ upl Ω L := by
      by_contra hcon
      push_neg at hcon
      have h1 := Subgroup.relIndex_eq_one.2 hcon
      omega
    have hgD' : g ∈ Dec (F := ℚ) (R.s.A v.1) := by
      rw [R.A_pl v]
      exact hgD
    obtain ⟨y, -, hgy⟩ : ∃ y ∈ maximalRealSubfield L, g (algebraMap L Ω y) ≠ algebraMap L Ω y := by
      by_contra hcon
      push_neg at hcon
      exact hgU hcon
    obtain ⟨b, τ₁, τ₂, hne⟩ := UpperTheory.V.J.Wu.exists_sep (R.s.hw v.1) hlw g hgD' y hgy
    obtain ⟨g', hc, hfree⟩ := place_free hG (R.s.hw v.1) hlw (Classical.choice ⟨τ₁⟩) b τ₁ τ₂ hne (x.psi v) ph
      (fun j τ => if τ = Classical.choice ⟨τ⟩ then 2 * ((j : ℕ) : ℤ) else ((j : ℕ) : ℤ))
      (fun j => if_pos rfl) (fun j τ hτ => if_neg hτ) hp
    exact ⟨g', mem_G' R.V v g' hc, hfree⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.DenseOf
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private lemma dim_succ_le {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime] (h : P < Q) :
    ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨r, hrQ, hrP⟩ := SetLike.exists_of_lt h
  have hne : Ideal.Quotient.mk P r ≠ 0 := fun h0 => hrP (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hnzd : Ideal.Quotient.mk P r ∈ nonZeroDivisors (A ⧸ P) := mem_nonZeroDivisors_of_ne_zero hne
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk P r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have : Ideal.Quotient.factor h.le (Ideal.Quotient.mk P r) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hrQ
    rw [map_mul, this, mul_zero]
  have hs : Function.Surjective
      (Ideal.Quotient.lift (Ideal.span {Ideal.Quotient.mk P r}) (Ideal.Quotient.factor h.le) hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective h.le)
  have h2 := ringKrullDim_le_of_surjective _ hs
  exact (add_le_add_left h2 1).trans h1

private lemma exists_sep {A : Type} [CommRing A] [IsNoetherianRing A] {J Z₀ : Ideal A}
    (h₀ : Z₀ ∈ J.minimalPrimes) :
    ∃ e, e ∉ Z₀ ∧ ∀ Z₁ ∈ J.minimalPrimes, Z₁ ≠ Z₀ → e ∈ Z₁ := by
  classical
  have hfin := J.finite_minimalPrimes_of_isNoetherianRing A
  set s := hfin.toFinset.erase Z₀ with hs
  have hp : Z₀.IsPrime := h₀.1.1
  have hnot : ¬ s.inf id ≤ Z₀ := by
    intro hle
    obtain ⟨W, hW, hWle⟩ := (Ideal.IsPrime.inf_le' hp).mp hle
    have hW' := Finset.mem_erase.mp hW
    have hWm : W ∈ J.minimalPrimes := hfin.mem_toFinset.mp hW'.2
    exact hW'.1 (le_antisymm hWle (h₀.2 hWm.1 hWle) |>.symm ▸ rfl)
  obtain ⟨e, he, heZ⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨e, heZ, fun Z₁ h₁ hne => ?_⟩
  have : Z₁ ∈ s := Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr h₁⟩
  exact (Finset.inf_le (f := id) this) he

theorem UpperTheory.V.J.denseOf :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (B₀ B : Type) [CommRing B₀] [IsNoetherianRing B₀] [Algebra c.O B₀] [CommRing B] [Algebra c.O B]
        (φ : B₀ →ₐ[c.O] B) (J : Ideal B₀) (D : ℕ) (Gd : (B₀ →ₐ[c.O] Qbar l) → Prop), Function.Surjective φ →
        (∀ Z ∈ J.minimalPrimes, ringKrullDim (B₀ ⧸ Z) = (D : WithBot ℕ∞)) →
        (∀ b : B₀, (∀ x : B₀ →ₐ[c.O] Qbar l, J ≤ RingHom.ker x → Gd x → x b = 0) → b ∈ J) →
        ∀ Z : Ideal B, Z.IsPrime → J.map φ ≤ Z → ringKrullDim (B ⧸ Z) ≤ (D : WithBot ℕ∞) ∧
          (ringKrullDim (B ⧸ Z) = (D : WithBot ℕ∞) → ∀ b ∉ Z, ∃ y : B →ₐ[c.O] Qbar l, Z ≤ RingHom.ker y ∧ Gd (y.comp φ) ∧ y b ≠ 0) := by
  intro l _ c B₀ B _ _ _ _ _ φ J D Gd hφ hdim hdense Z hZ hJZ
  have hJZ' : J ≤ Z.comap φ := Ideal.map_le_iff_le_comap.mp hJZ
  haveI hZ' : (Z.comap φ).IsPrime := Ideal.comap_isPrime φ Z
  obtain ⟨Z₀, hZ₀, hZ₀le⟩ := Ideal.exists_minimalPrimes_le hJZ'
  haveI hp₀ : Z₀.IsPrime := hZ₀.1.1
  have hψ : Function.Surjective ((Ideal.Quotient.mk Z).comp (φ : B₀ →+* B)) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk Z).comp (φ : B₀ →+* B)) = Z.comap φ := by
    ext a
    exact RingHom.mem_ker.trans Ideal.Quotient.eq_zero_iff_mem
  have hde : ringKrullDim (B ⧸ Z) = ringKrullDim (B₀ ⧸ Z.comap φ) := by
    rw [← hker]
    exact (ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hψ)).symm
  have hle : ringKrullDim (B ⧸ Z) ≤ (D : WithBot ℕ∞) := by
    rw [hde, ← hdim Z₀ hZ₀]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ₀le) (Ideal.Quotient.factor_surjective hZ₀le)
  refine ⟨hle, fun hD b hb => ?_⟩
  have hZeq : Z₀ = Z.comap φ := by
    by_contra hne
    have hlt : Z₀ < Z.comap φ := lt_of_le_of_ne hZ₀le hne
    have h1 := dim_succ_le hlt
    rw [← hde, hD, hdim Z₀ hZ₀] at h1
    have h2 : ((D : WithBot ℕ∞) + 1) = ((D + 1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl
    rw [h2] at h1
    have h3 : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ (D : WithBot ℕ∞) := h1
    have h4 : D + 1 ≤ D := by exact_mod_cast h3
    omega
  obtain ⟨b', rfl⟩ := hφ b
  have hb' : b' ∉ Z₀ := by rw [hZeq]; exact hb
  obtain ⟨e, he, hesep⟩ := exists_sep hZ₀
  have hbe : b' * e ∉ J := fun hm =>
    (hp₀.mem_or_mem (hZ₀.1.2 hm)).elim hb' he
  have hx : ∃ x : B₀ →ₐ[c.O] Qbar l, J ≤ RingHom.ker x ∧ Gd x ∧ x (b' * e) ≠ 0 := by
    by_contra hno
    refine hbe (hdense _ fun x h1 h2 => ?_)
    by_contra h3
    exact hno ⟨x, h1, h2, h3⟩
  obtain ⟨x, hJx, hGx, hxbe⟩ := hx
  have hxb : x b' ≠ 0 := fun h0 => hxbe (by rw [map_mul, h0, zero_mul])
  have hxe : x e ≠ 0 := fun h0 => hxbe (by rw [map_mul, h0, mul_zero])
  haveI hkp : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  obtain ⟨Z₁, hZ₁, hZ₁le⟩ := Ideal.exists_minimalPrimes_le hJx
  have hZ₁eq : Z₁ = Z₀ := by
    by_contra hne
    exact hxe (hZ₁le (hesep Z₁ hZ₁ hne))
  have hZx : Z.comap φ ≤ RingHom.ker x := by rw [← hZeq, ← hZ₁eq]; exact hZ₁le
  have hkφ : RingHom.ker φ ≤ RingHom.ker x := fun a ha =>
    hZx (by
      have : φ a = 0 := ha
      show φ a ∈ Z
      rw [this]; exact Z.zero_mem)
  let y : B →ₐ[c.O] Qbar l := (Ideal.Quotient.liftₐ (RingHom.ker φ) x (fun a ha => hkφ ha)).comp
    (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom
  have hy : ∀ a, y (φ a) = x a := by
    intro a
    have e1 : (Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a) = Ideal.Quotient.mk _ a :=
      (AlgEquiv.symm_apply_eq _).2 (Ideal.quotientKerAlgEquivOfSurjective_mk hφ a).symm
    show Ideal.Quotient.liftₐ (RingHom.ker φ) x (fun a ha => hkφ ha) ((Ideal.quotientKerAlgEquivOfSurjective hφ).symm (φ a)) = x a
    rw [e1]
    rfl
  refine ⟨y, fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := hφ z
    show y (φ a) = 0
    rw [hy]
    exact hZx hz
  · have : y.comp φ = x := AlgHom.ext hy
    rwa [this]
  · rw [hy]; exact hxb
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th

namespace UpperTheory.Gal.projectedFormsSystemPart

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}

@[reducible] def setS (R : CReal k c₁ f 3 ka) (S : Fr.Space c₁.O (Φ.ext f) 3) : CReal k c₁ f 3 ka := { R with S := S }

set_option synthInstance.maxHeartbeats 200000 in
private theorem psi_eq (R : CReal k c₁ f 3 ka) {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ) (ξ : R.S.A →ₐ[c₁.O] Qbar l) (v) :
    W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) ((ξ.comp R.S.inc).comp φ) v = R.K.twψ (ptRep R.S ξ) v :=
  funext fun i => (TwLink.IsPhi.maps R.K hφ ξ).2 v i

end

end UpperTheory.Gal.projectedFormsSystemPart
