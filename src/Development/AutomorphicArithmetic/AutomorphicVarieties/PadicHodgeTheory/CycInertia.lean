module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankLocalFieldEqCardDecompositionGroup

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.locRoots
section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.locOnto
section -- merged from Development.AutomorphicArithmetic.FrobeniusLocalisation.LocStab
open NumberField IsDedekindDomain
open scoped Pointwise

namespace UpperTheory.HF.LocStab

open Polynomial

variable {E : Type} [Field E] [NumberField E]

theorem exists_compare (v : HeightOneSpectrum (𝓞 E)) (a b : 𝓞 E) :
    ∃ d t : 𝓞 E, d ∉ v.asIdeal ∧ (d * b = t * a ∨ d * a = t * b) := by
  let A := Localization.AtPrime v.asIdeal
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) v.ne_bot A
  have hinj : Function.Injective (algebraMap (𝓞 E) A) :=
    IsLocalization.injective A v.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨z, hz⟩ := ValuationRing.cond (algebraMap (𝓞 E) A a) (algebraMap (𝓞 E) A b)
  obtain ⟨⟨t, d⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl z
  refine ⟨d, t, d.2, ?_⟩
  have hs := IsLocalization.mk'_spec A t d
  rcases hz with hz | hz
  · left
    apply hinj
    simp only [map_mul]
    rw [← hz, ← hs]
    ring
  · right
    apply hinj
    simp only [map_mul]
    rw [← hz, ← hs]
    ring

variable {l : ℕ} [Fact l.Prime]

theorem norm_int_le (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 := by
  have hx : IsIntegral ℤ (c (x : E)) := by
    have h : IsIntegral ℤ (x : E) := x.2
    exact h.map (c.toIntAlgHom)
  have h : c (x : E) ∈ (NormedField.valuation (K := PadicAlgCl l)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral
      hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_unit (c : E →+* PadicAlgCl l) (v : HeightOneSpectrum (𝓞 E))
    (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) {d : 𝓞 E} (hd : d ∉ v.asIdeal) :
    ‖c (d : E)‖ = 1 :=
  le_antisymm (norm_int_le c d) (not_lt.1 fun h => hd ((hc d).2 h))

theorem lt_one_of_lt_one (c c' : E →+* PadicAlgCl l) (v : HeightOneSpectrum (𝓞 E))
    (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hc' : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c' (x : E)‖ < 1) (x : E) (hx : ‖c x‖ < 1) :
    ‖c' x‖ < 1 := by
  by_cases hx0 : x = 0
  · simp [hx0]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
  have hb0 : (b : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbE : ((b : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hb0
  have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hx0
    change ((a : 𝓞 E) : E) / ((b : 𝓞 E) : E) = 0
    simp [h]
  obtain ⟨d, t, hd, h | h⟩ := exists_compare v a b
  · exfalso
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      simp [this]
    have hE : ((d : 𝓞 E) : E) * (b : E) = (t : E) * (a : E) := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h
    have htE : ((t : 𝓞 E) : E) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hE
      exact (mul_ne_zero hdE hbE) hE
    have hxe : (algebraMap (𝓞 E) E a) / (algebraMap (𝓞 E) E b) = (d : E) / (t : E) := by
      change ((a : 𝓞 E) : E) / ((b : 𝓞 E) : E) = _
      field_simp
      linear_combination -hE
    rw [hxe, map_div₀, norm_div, norm_unit c v hc hd] at hx
    have ht := norm_int_le c t
    have ht0 : 0 < ‖c (t : E)‖ := norm_pos_iff.2 (by simpa using htE)
    rw [div_lt_one ht0] at hx
    linarith
  · have hdE : ((d : 𝓞 E) : E) ≠ 0 := by
      intro h0
      apply hd
      have : d = 0 := by exact_mod_cast h0
      simp [this]
    have hE : ((d : 𝓞 E) : E) * (a : E) = (t : E) * (b : E) := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h
    have hxe : (algebraMap (𝓞 E) E a) / (algebraMap (𝓞 E) E b) = (t : E) / (d : E) := by
      change ((a : 𝓞 E) : E) / ((b : 𝓞 E) : E) = _
      field_simp
      linear_combination hE
    rw [hxe] at hx ⊢
    rw [map_div₀, norm_div, norm_unit c v hc hd, div_one] at hx
    rw [map_div₀, norm_div, norm_unit c' v hc' hd, div_one]
    exact (hc' t).1 ((hc t).2 hx)

theorem approx (β γ : PadicAlgCl l) (f : ℚ_[l][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℚ[X], ‖aeval β G - aeval β f‖ < ε ∧ ‖aeval γ G - aeval γ f‖ < ε := by
  induction f using Polynomial.induction_on' generalizing ε with
  | add p q hp hq =>
    obtain ⟨G, h1, h2⟩ := hp (half_pos hε)
    obtain ⟨H, h3, h4⟩ := hq (half_pos hε)
    refine ⟨G + H, ?_, ?_⟩
    · simp only [map_add (f := _)]
      rw [add_sub_add_comm]
      exact (norm_add_le _ _).trans_lt (by linarith)
    · simp only [map_add (f := _)]
      rw [add_sub_add_comm]
      exact (norm_add_le _ _).trans_lt (by linarith)
  | monomial n a =>
    set M : ℝ := ‖β‖ ^ n + ‖γ‖ ^ n + 1 with hM
    have hMpos : 0 < M := by positivity
    obtain ⟨r, hr⟩ := Padic.rat_dense l a (div_pos hε hMpos)
    have key : ∀ δ : PadicAlgCl l, ‖δ‖ ^ n ≤ M → ‖aeval δ (monomial n r : ℚ[X]) - aeval δ (monomial n a : ℚ_[l][X])‖ < ε := by
      intro δ hδ
      have e1 : aeval δ (monomial n r : ℚ[X]) = algebraMap ℚ_[l] (PadicAlgCl l) (r : ℚ_[l]) * δ ^ n := by
        rw [aeval_monomial]
        simp
      have e2 : aeval δ (monomial n a : ℚ_[l][X]) = algebraMap ℚ_[l] (PadicAlgCl l) a * δ ^ n := by
        rw [aeval_monomial]
      rw [e1, e2, ← sub_mul, ← map_sub, norm_mul, norm_pow, PadicAlgCl.norm_extends, norm_sub_rev]
      calc ‖a - (r : ℚ_[l])‖ * ‖δ‖ ^ n ≤ ‖a - (r : ℚ_[l])‖ * M := by gcongr
        _ < ε / M * M := by gcongr
        _ = ε := by field_simp
    refine ⟨monomial n r, key β ?_, key γ ?_⟩
    · have := pow_nonneg (norm_nonneg γ) n
      linarith
    · have := pow_nonneg (norm_nonneg β) n
      linarith

theorem adjoin_eq_top {α : E} (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    Algebra.adjoin ℚ {α} = ⊤ := by
  have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) α)
  rw [← h, hα, IntermediateField.top_toSubalgebra]

theorem ringHom_ext {α : E} (hα : IntermediateField.adjoin ℚ {α} = ⊤) {B : Type} [Field B]
    [CharZero B] (f g : E →+* B) (h : f α = g α) : f = g := by
  have := AlgHom.ext_of_adjoin_eq_top (adjoin_eq_top hα) (φ₁ := f.toRatAlgHom) (φ₂ := g.toRatAlgHom)
    (by rintro _ rfl; exact h)
  ext x
  exact DFunLike.congr_fun this x

theorem norm_natCast_pow (c : E →+* PadicAlgCl l) (m : ℕ) :
    ‖c ((l : E) ^ m)‖ = ((l : ℝ)⁻¹) ^ m := by
  rw [map_pow, map_natCast, norm_pow]
  congr 1
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem root_of_stab (c : E →+* PadicAlgCl l) (α : E) (s : E ≃ₐ[ℚ] E)
    (v : HeightOneSpectrum (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hs : s • v.asIdeal = v.asIdeal) :
    aeval (c (s α)) (minpoly ℚ_[l] (c α)) = 0 := _root_.GlobalTheory.LocStab.root_of_stab c α s v hc hs

theorem stab_of_root (c : E →+* PadicAlgCl l) {α : E}
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) (s : E ≃ₐ[ℚ] E)
    (v : HeightOneSpectrum (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1)
    (hroot : aeval (c (s α)) (minpoly ℚ_[l] (c α)) = 0) :
    s • v.asIdeal = v.asIdeal := by
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (K := ℚ_[l]) (L := PadicAlgCl l)
    (Algebra.IsAlgebraic.isAlgebraic (c α)) hroot
  have hcomp : ((σ : PadicAlgCl l →+* PadicAlgCl l).comp c) = c.comp (s : E →+* E) :=
    ringHom_ext hα _ _ hσ
  have hn : ∀ x : E, ‖c (s x)‖ = ‖c x‖ := fun x => by
    have h := DFunLike.congr_fun hcomp x
    change σ (c x) = c (s x) at h
    rw [← h]
    exact (spectralNorm_eq_of_equiv σ (c x)).symm
  have hmem : ∀ x : 𝓞 E, s • x ∈ v.asIdeal ↔ x ∈ v.asIdeal := fun x => by
    rw [hc, hc]
    exact iff_of_eq (congrArg (· < (1 : ℝ)) (hn x))
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← hmem (s⁻¹ • y), smul_inv_smul]

theorem adjoin_range_eq (c : E →+* PadicAlgCl l) {α : E}
    (hα : IntermediateField.adjoin ℚ {α} = ⊤) :
    IntermediateField.adjoin ℚ_[l] (Set.range c) = IntermediateField.adjoin ℚ_[l] {c α} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    have hle : Algebra.adjoin ℚ {α} ≤
        (((IntermediateField.adjoin ℚ_[l] {c α}).toSubalgebra.restrictScalars ℚ).comap
          c.toRatAlgHom) := by
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[l] (c α)
    have hx : x ∈ Algebra.adjoin ℚ {α} := by
      rw [adjoin_eq_top hα]
      exact Algebra.mem_top
    exact hle hx
  · exact IntermediateField.adjoin.mono _ _ _ (by rintro _ rfl; exact ⟨α, rfl⟩)

theorem exists_aut_of_root (c : E →+* PadicAlgCl l) [IsGalois ℚ E] (α : E)
    {r : PadicAlgCl l} (hr : aeval r (minpoly ℚ_[l] (c α)) = 0) :
    ∃ s : E ≃ₐ[ℚ] E, c (s α) = r := by
  have hmin : minpoly ℚ (c α) = minpoly ℚ α :=
    minpoly.algHom_eq c.toRatAlgHom c.injective α
  have hdvd := minpoly.dvd_map_of_isScalarTower ℚ ℚ_[l] (c α)
  have hr' : aeval r (minpoly ℚ α) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    have : aeval r (map (algebraMap ℚ ℚ_[l]) (minpoly ℚ (c α))) = 0 := by
      rw [hq, map_mul, hr, zero_mul]
    rwa [aeval_map_algebraMap, hmin] at this
  have hsplit : (map (algebraMap ℚ E) (minpoly ℚ α)).Splits := Normal.splits inferInstance α
  have hne : minpoly ℚ α ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral α)
  have hmem : r ∈ (minpoly ℚ α).rootSet (PadicAlgCl l) := mem_rootSet.2 ⟨hne, hr'⟩
  rw [← hsplit.image_rootSet c.toRatAlgHom] at hmem
  obtain ⟨e, he, rfl⟩ := hmem
  obtain ⟨s, hs⟩ := minpoly.exists_algEquiv_of_root' (K := ℚ) (L := E)
    (Algebra.IsAlgebraic.isAlgebraic α) (mem_rootSet.1 he).2
  exact ⟨s, by rw [hs]; rfl⟩

theorem finrank_adjoin_range_eq_card_stabilizer :
    ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l)
      [IsGalois ℚ E] (v : HeightOneSpectrum (𝓞 E)),
      (∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1) →
      Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range c)) =
        Nat.card (MulAction.stabilizer (E ≃ₐ[ℚ] E) v.asIdeal) := _root_.GlobalTheory.LocStab.finrank_adjoin_range_eq_card_stabilizer

end UpperTheory.HF.LocStab
end

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.loc_onto :
    ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (J : L →+* PadicAlgCl l), ∃ P : Ideal (𝓞 L), P.IsPrime ∧ P.LiesOver (span {(l : ℤ)}) ∧ (∀ x : 𝓞 L, x ∈ P ↔ ‖J (x : L)‖ < 1) ∧ (∀ τ : L ≃ₐ[ℚ] L, τ ∈ MulAction.stabilizer _ P ↔ ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : L, σ (J x) = J (τ x)) ∧ (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ τ : L ≃ₐ[ℚ] L, ∀ x : L, σ (J x) = J (τ x)) ∧ Module.finrank ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range J)) = Nat.card (MulAction.stabilizer (L ≃ₐ[ℚ] L) P) := by
  intro l _ L _ _ _ J
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hl : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← PadicAlgCl.valuation_coe, PadicAlgCl.valuation_p l]
    have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  let I : Ideal (𝓞 L) :=
    { carrier := {x : 𝓞 L | ‖J (x : L)‖ < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        show ‖J ((a : L) + (b : L))‖ < 1
        rw [map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        show ‖J ((c : L) * (x : L))‖ < 1
        rw [map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (LocStab.norm_int_le J c)) hx }
  have hmem : ∀ x : 𝓞 L, x ∈ I ↔ ‖J (x : L)‖ < 1 := fun x => Iff.rfl
  have hIp : I.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, hmem]
      simp
    · intro a b hab
      rw [hmem] at hab
      rw [hmem, hmem]
      have hab' : ‖J (a : L)‖ * ‖J (b : L)‖ < 1 := by
        rw [← norm_mul, ← map_mul]
        exact hab
      by_contra h
      push_neg at h
      nlinarith [h.1, h.2]
  have hlI : ((l : ℤ) : 𝓞 L) ∈ I := by
    rw [hmem]
    simpa using hl
  have hIne : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlI
    have hne : ((l : ℤ) : 𝓞 L) ≠ 0 := by
      simp [(Fact.out : l.Prime).ne_zero]
    exact hne hlI
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨I, hIp, hIne⟩
  have hlo : I.LiesOver (Ideal.span {(l : ℤ)}) := by
    constructor
    have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible
        (Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).irreducible
    refine hmax.eq_of_le (Ideal.comap_ne_top _ hIp.ne_top) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 L) (l : ℤ) ∈ I
    rw [eq_intCast]
    exact hlI
  refine ⟨I, hIp, hlo, hmem, ?_, ?_, ?_⟩
  · intro τ
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hτ
      have hr := LocStab.root_of_stab J α τ v hmem hτ
      have hint := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) (J α)).isIntegral
      have hmin : minpoly ℚ_[l] (J (τ α)) = minpoly ℚ_[l] (J α) :=
        (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hr (minpoly.monic hint)).symm
      obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[l]) (E := PadicAlgCl l)).mp hmin
      refine ⟨σ, fun x => ?_⟩
      have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
        (J.comp (τ : L →+* L)) (by simpa [AlgEquiv.smul_def] using hσ)
      exact RingHom.congr_fun hext x
    · rintro ⟨σ, hσ⟩
      apply LocStab.stab_of_root J hα τ v hmem
      rw [← hσ α]
      simp [Polynomial.aeval_algEquiv]
  · intro σ
    obtain ⟨s, hs⟩ := LocStab.exists_aut_of_root J α (r := σ (J α)) (by simp [Polynomial.aeval_algEquiv])
    refine ⟨s, fun x => ?_⟩
    have hext := LocStab.ringHom_ext hα ((σ : PadicAlgCl l →+* PadicAlgCl l).comp J)
      (J.comp (s : L →+* L)) (by simpa using hs.symm)
    exact RingHom.congr_fun hext x
  · exact LocStab.finrank_adjoin_range_eq_card_stabilizer l L J v hmem
end

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

section
open Formalism.HC.Der Formalism.TwoAdicCyclotomicDecomposition

private theorem stab_iff (N : ℕ) [NeZero N] (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime]
    [Q.LiesOver (span {(l : ℤ)})] (u : (ZMod N)ˣ) :
    tauN N u ∈ MulAction.stabilizer _ Q ↔ ∃ k : ℕ, (u : ZMod N).val ≡ l ^ k [MOD ordCompl[l] N] := by
  set M := ordCompl[l] N with hM
  have hMN : M ∣ N := Nat.ordCompl_dvd N l
  have hlM : l.Coprime M := Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)
  obtain ⟨u0, hu0⟩ := exists_unit_modEq (N := N) hMN l hlM
  have hF : IsArithFrobAt ℤ (tauN N u0) Q := tauN_frob N l Q u0 hu0
  have hu0' : ((ZMod.unitsMap hMN u0 : (ZMod M)ˣ) : ZMod M) = (l : ZMod M) :=
    (val_modEq_iff hMN u0 l).mp hu0
  constructor
  · intro hs
    obtain ⟨k, ρ, hρ, hρeq⟩ := Decomp.stab_eq_inertia_mul l Q (tauN N u0) (tauN N u) hF hs
    obtain ⟨w, rfl⟩ := (tauN N).surjective ρ
    refine ⟨k, ?_⟩
    have hw1 : ZMod.unitsMap hMN w = 1 :=
      (val_modEq_one_iff hMN w).mp ((tauN_inertia_iff N l Q w).mp hρ)
    have huw : u = w * u0 ^ k := (tauN N).injective (by rw [map_mul, map_pow]; exact hρeq)
    rw [val_modEq_iff hMN, huw, map_mul, map_pow, hw1, one_mul, Units.val_pow_eq_pow_val, hu0',
      Nat.cast_pow]
  · rintro ⟨k, hk⟩
    have hw1 : ZMod.unitsMap hMN (u * (u0 ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, mul_inv_eq_one]
      apply Units.ext
      rw [(val_modEq_iff hMN u _).mp hk, Units.val_pow_eq_pow_val, hu0', Nat.cast_pow]
    have hwin := (tauN_inertia_iff N l Q (u * (u0 ^ k)⁻¹)).mpr ((val_modEq_one_iff hMN _).mpr hw1)
    have hwst := Decomp.mem_stab_of _ Q (smul_mem_of_inertia _ Q hwin)
    have hFst := IsArithFrobAt.mem_stabilizer hF
    have hu : u = (u * (u0 ^ k)⁻¹) * u0 ^ k := by rw [inv_mul_cancel_right]
    rw [hu, map_mul, map_pow]
    exact Subgroup.mul_mem _ hwst (Subgroup.pow_mem _ hFst k)

private theorem act_of (N : ℕ) [NeZero N] {K : Type*} [Field K] (J : Cond.Cyc N →+* K) (σ : K →+* K) (u : (ZMod N)ˣ)
    (h : ∀ x, σ (J x) = J (tauN N u x)) (x : K) (hx : x ^ N = 1) : σ x = x ^ (u : ZMod N).val := by
  have hζ := (zO_prim N).map_of_injective (f := algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N))
    (FaithfulSMul.algebraMap_injective _ _)
  have hJ := hζ.map_of_injective J.injective
  obtain ⟨i, -, rfl⟩ := hJ.eq_pow_of_pow_eq_one hx
  have hg : IsCyclotomicExtension.Rat.galEquivZMod N (Cond.Cyc N) (tauN N u) = u :=
    MulEquiv.apply_symm_apply _ _
  have hτ : tauN N u (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) =
      (algebraMap (𝓞 (Cond.Cyc N)) (Cond.Cyc N) (zO N)) ^ (u : ZMod N).val := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N (Cond.Cyc N) (tauN N u) hζ.pow_eq_one,
      hg]
  rw [map_pow, h, hτ, map_pow]
  ring

end

theorem UpperTheory.HF.loc_roots :
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → (∀ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∃ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] ∧ ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val) ∧ ∀ (u : (ZMod M)ˣ) (j : ℕ), (u : ZMod M).val ≡ l ^ j [MOD ordCompl[l] M] → ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), ∀ x : PadicAlgCl l, x ^ M = 1 → σ x = x ^ (u : ZMod M).val := by
  intro l _ M hM
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI := Formalism.HC.Der.cyc_isGalois M
  let J : Cond.Cyc M →+* PadicAlgCl l := (IsAlgClosed.lift : Cond.Cyc M →ₐ[ℚ] PadicAlgCl l).toRingHom
  obtain ⟨P, hPp, hPlo, -, hstab, hsurj, -⟩ := UpperTheory.HF.loc_onto l (Cond.Cyc M) J
  haveI := hPp
  haveI := hPlo
  constructor
  · intro σ
    obtain ⟨τ, hτ⟩ := hsurj σ
    obtain ⟨u, rfl⟩ := (Formalism.HC.Der.tauN M).surjective τ
    have hst : Formalism.HC.Der.tauN M u ∈ MulAction.stabilizer _ P := (hstab _).mpr ⟨σ, hτ⟩
    obtain ⟨k, hk⟩ := (stab_iff M l P u).mp hst
    exact ⟨u, k, hk, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hτ x hx⟩
  · intro u j hj
    obtain ⟨σ, hσ⟩ := (hstab (Formalism.HC.Der.tauN M u)).mp ((stab_iff M l P u).mpr ⟨j, hj⟩)
    exact ⟨σ, fun x hx => act_of M J (σ : PadicAlgCl l →+* PadicAlgCl l) u hσ x hx⟩
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem UpperTheory.V.Loc.ci_closed (l : ℕ) [Fact l.Prime] (x y : PadicAlgCl l) :
    IsClosed {σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l | σ x = y} := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hx
  have hU := IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ_[l] {x})
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro σ hσ
  have hc : Continuous fun τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l => σ⁻¹ * τ := by fun_prop
  have h1 := (hU.preimage hc).mem_nhds (x := σ) (by simp)
  refine Filter.mem_of_superset h1 fun τ hτ h => hσ ?_
  have h2 : (σ⁻¹ * τ) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x (IntermediateField.mem_adjoin_simple_self _ _)
  have h3 : τ x = y := h
  have h4 : σ ((σ⁻¹ * τ) x) = τ x := by
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  show σ x = y
  rw [← h3, ← h4, h2]

private theorem UpperTheory.V.Loc.ci_dvd_sub_iff (l : ℕ) [Fact l.Prime] (r : ℕ) (x y : ℤ_[l]) :
    (l : ℤ_[l]) ^ r ∣ x - y ↔ PadicInt.toZModPow r x = PadicInt.toZModPow r y := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]

private theorem UpperTheory.V.Loc.ci_pow_congr {K : Type*} [Monoid K] {x : K} {M a b : ℕ} (hx : x ^ M = 1)
    (h : a ≡ b [MOD M]) : x ^ a = x ^ b := by
  rw [pow_eq_pow_mod a hx, pow_eq_pow_mod b hx, h]

private theorem UpperTheory.V.Loc.ci_crt (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (M : ℕ) (hM : M ≠ 0) :
    ∃ c : ℕ, c.Coprime M ∧ c ≡ 1 [MOD ordCompl[l] M] ∧
      ∀ k ≤ M.factorization l, (c : ZMod (l ^ k)) = PadicInt.toZModPow k (a : ℤ_[l]) := by
  have hp : l.Prime := Fact.out
  set v := M.factorization l with hv
  have hcop : Nat.Coprime (ordCompl[l] M) (l ^ v) := (Nat.coprime_ordCompl hp hM).symm.pow_right _
  haveI : NeZero (l ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨c, h1, h2⟩ := Nat.chineseRemainder hcop 1 (PadicInt.toZModPow v (a : ℤ_[l])).val
  have hc : ((c : ℕ) : ZMod (l ^ v)) = PadicInt.toZModPow v (a : ℤ_[l]) := by
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]
  have hcoP : c.Coprime (l ^ v) := by
    rw [← ZMod.isUnit_iff_coprime, hc]
    exact (Units.isUnit a).map _
  have hcoN : c.Coprime (ordCompl[l] M) := by
    unfold Nat.Coprime
    rw [h1.gcd_eq, Nat.gcd_one_left]
  refine ⟨c, ?_, h1, fun k hk => ?_⟩
  · have := Nat.Coprime.mul_right hcoP hcoN
    rwa [hv, Nat.ordProj_mul_ordCompl_eq_self] at this
  · have hd : (l : ℤ_[l]) ^ v ∣ (c : ℤ_[l]) - (a : ℤ_[l]) := by
      rw [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast, hc]
    have := (pow_dvd_pow _ hk).trans hd
    rwa [UpperTheory.V.Loc.ci_dvd_sub_iff, map_natCast] at this

private theorem UpperTheory.V.Loc.ci_fin (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) (n : ℕ) :
    ∃ σ : (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l),
      (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val := by
  have hp : l.Prime := Fact.out
  obtain ⟨M, hM⟩ : ∃ M, M = n.factorial * l ^ n := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero n.factorial_ne_zero (pow_ne_zero _ hp.ne_zero)
  have hv : n ≤ M.factorization l :=
    (hp.pow_dvd_iff_le_factorization hM0).1 (by rw [hM]; exact Dvd.intro_left _ rfl)
  obtain ⟨c, hcM, hc1, hc2⟩ := UpperTheory.V.Loc.ci_crt l a M hM0
  have hval : ∀ (N : ℕ) (h : c.Coprime N), ((ZMod.unitOfCoprime c h : (ZMod N)ˣ) : ZMod N).val ≡ c [MOD N] := by
    intro N h
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  obtain ⟨σ, hσ⟩ := (UpperTheory.HF.loc_roots l M (Nat.pos_of_ne_zero hM0)).2 (ZMod.unitOfCoprime c hcM) 0
    (by rw [pow_zero]; exact ((hval M hcM).of_dvd (Nat.ordCompl_dvd _ _)).trans hc1)
  have hσc : ∀ d, d ∣ M → ∀ x : PadicAlgCl l, x ^ d = 1 → σ x = x ^ c := by
    intro d ⟨e, he⟩ x hx
    have hxM : x ^ M = 1 := by rw [he, pow_mul, hx, one_pow]
    rw [hσ x hxM]
    exact UpperTheory.V.Loc.ci_pow_congr hxM (hval M hcM)
  refine ⟨σ, fun m hm hm0 hlm x hx => ?_, fun k hk x hx => ?_⟩
  · have hmM : m ∣ M := by
      rw [hM]
      exact (Nat.dvd_factorial hm0 hm).mul_right _
    have hm' : m ∣ ordCompl[l] M := Nat.dvd_ordCompl_of_dvd_not_dvd hmM hlm
    rw [hσc m hmM x hx, UpperTheory.V.Loc.ci_pow_congr hx (hc1.of_dvd hm'), pow_one]
  · have hkM : l ^ k ∣ M := by
      rw [hM]
      exact (pow_dvd_pow _ hk).mul_left _
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    rw [hσc _ hkM x hx]
    refine UpperTheory.V.Loc.ci_pow_congr hx ?_
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
    exact hc2 k (le_trans hk hv)

private theorem UpperTheory.V.Loc.ci_surj (l : ℕ) [Fact l.Prime] (a : ℤ_[l]ˣ) : ∃ g ∈ Iq l, cyc l l g = a := by
  have hp : l.Prime := Fact.out
  let S : ℕ → Set (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) := fun n =>
    {σ | (∀ m ≤ n, 0 < m → ¬ l ∣ m → ∀ x : PadicAlgCl l, x ^ m = 1 → σ x = x) ∧
      ∀ k ≤ n, ∀ x : PadicAlgCl l, x ^ l ^ k = 1 → σ x = x ^ (PadicInt.toZModPow k (a : ℤ_[l])).val}
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    simp only [S, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ => UpperTheory.V.Loc.ci_closed l _ _
    · exact isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
        UpperTheory.V.Loc.ci_closed l _ _
  haveI : IsGalois ℚ_[l] (PadicAlgCl l) := {}
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
    (fun n σ hσ => ⟨fun m hm => hσ.1 m (hm.trans n.le_succ), fun k hk => hσ.2 k (hk.trans n.le_succ)⟩)
    (fun n => UpperTheory.V.Loc.ci_fin l a n) (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_, ?_⟩
  · unfold MaximalUnramifiedExtension at hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm0, hlm, hx⟩ := hx
      exact (hσ m).1 m le_rfl hm0 hlm x hx
    | algebraMap r => exact σ.commutes r
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  · haveI (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl l) (l ^ i) := by
      haveI : NeZero (l ^ i) := ⟨pow_ne_zero _ hp.ne_zero⟩
      infer_instance
    refine Units.ext (PadicInt.ext_of_toZModPow.1 fun k => ?_)
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
    obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ k)
    have h1 := cyclotomicCharacter.spec l (n := k)
      (MulSemiringAction.toRingAut (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (PadicAlgCl l) σ) η hη.pow_eq_one
    have h2 := (hσ k).2 k le_rfl η hη.pow_eq_one
    have h3 := h1.symm.trans h2
    exact ZMod.val_injective _ (hη.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h3)

private theorem UpperTheory.V.Loc.ci_inf (l : ℕ) [Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit (((l + 1 : ℕ)) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  refine ⟨hu.unit, fun h => ?_⟩
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have h2 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, hu.unit_spec, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one,
    Nat.pow_eq_one] at h2
  have := hp.one_lt
  omega

theorem UpperTheory.V.Loc.cycInertia :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l]ˣ, ∃ g ∈ Iq l, cyc l l g = u) ∧ ∀ U : Subgroup (GQ l), IsOpen (U : Set (GQ l)) → IsOpen (((U ⊓ Iq l).map (cyc l l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) ∧ ∃ s ∈ U ⊓ Iq l, ¬ IsOfFinOrder (cyc l l s) := by
  intro l _
  refine ⟨UpperTheory.V.Loc.ci_surj l, fun U hU => ?_⟩
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : Finite (GQ l ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : Continuous (cyc l l) := cyclotomicCharacter.continuous l ℚ_[l] (Om l)
  constructor
  · have hs : Function.Surjective ((cyc l l).comp (Iq l).subtype) := fun u => by
      obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
      exact ⟨⟨g, hg⟩, h⟩
    have he : (U ⊓ Iq l).map (cyc l l) = (U.subgroupOf (Iq l)).map ((cyc l l).comp (Iq l).subtype) := by
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    haveI : ((U ⊓ Iq l).map (cyc l l)).FiniteIndex := ⟨by
      rw [he]
      exact ne_zero_of_dvd_ne_zero Subgroup.FiniteIndex.index_ne_zero (Subgroup.index_map_dvd _ hs)⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    rw [Subgroup.coe_map, Subgroup.coe_inf]
    exact (((U.isClosed_of_isOpen hU).inter
      (InfiniteGalois.fixingSubgroup_isClosed (MaximalUnramifiedExtension l))).isCompact.image hc).isClosed
  · obtain ⟨u, hu⟩ := UpperTheory.V.Loc.ci_inf l
    obtain ⟨g, hg, h⟩ := UpperTheory.V.Loc.ci_surj l u
    obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
      (Subgroup.FiniteIndex.index_ne_zero (H := U)) g
    refine ⟨g ^ n, ⟨hgn, pow_mem hg n⟩, fun hf => hu ?_⟩
    rw [map_pow, h] at hf
    exact hf.of_pow hn.ne'
