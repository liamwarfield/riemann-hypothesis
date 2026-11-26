module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNorm
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_quot_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    Nat.card (𝓞 D.host.E ⧸ P'.asIdeal) = Nat.card (𝓞 D.host.E ⧸ P.asIdeal) := by
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)
  have hle : P.asIdeal.map σ ≤ P'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : σ c = c' := RingOfIntegers.ext h2.symm
    show σ c ∈ P'.asIdeal
    rw [e]; exact h1
  have hmax : (P.asIdeal.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ (hp := P.isMaximal)
  have e : P'.asIdeal = P.asIdeal.map σ := (hmax.eq_of_le P'.isPrime.ne_top hle).symm
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal P'.asIdeal σ e).toEquiv).symm

theorem twist_ram_prime_dvd_Qn : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  classical
  intro D T Lc sc G μ₀ hL i j t w hxi hnu

  have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro hS
    have hv := (Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1
    have hE := hv.2.2.2 (w.under (𝓞 D.host.F)) w rfl
    have hexp := (hE.2 (Finset.notMem_empty _) 0).1 ((Formalism.L2.Host.HChar.unrAt_iff _ _).1 hnu)
    rw [Model.expIn_condF, if_pos hS, condExp] at hexp
    split_ifs at hexp <;> omega

  obtain ⟨PP, hPP, hw⟩ : ∃ PP ∈ Lc.Q t, w = PP ∨ Formalism.IndefR.Lev.IsConjPl PP w := by
    rcases (hL.Q_ram t w).1 hxi with h | ⟨PP, h, hc⟩
    · exact ⟨w, h, Or.inl rfl⟩
    · exact ⟨PP, h, Or.inr hc⟩
  have hunder : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = w.under (𝓞 D.host.F) := by
    rcases hw with rfl | hc
    · rfl
    · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
  have hW0 : PP ∉ G.pl.W0 := by
    intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    apply hS0
    rw [← hunder, G.pl.under_w hv]
    exact hv
  have hloc : PP ∈ GlobalTheory.FunObj.locPl G t := Finset.mem_union_right _ hPP
  have htw : PP ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  obtain ⟨⟨q, hq, hcard, -, -⟩, -⟩ := hL.Q_pl t PP hPP
  have hnorm : Ideal.absNorm PP.asIdeal = q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hcard]
  refine ⟨q, hq, ?_, ?_, PP, hloc, hnorm⟩
  · rcases hw with rfl | hc
    · exact hcard
    · rw [card_quot_of_isConjPl hc]; exact hcard
  · rw [← hnorm]
    exact Finset.dvd_prod_of_mem _ htw

end GlobalTheory.SqTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNormStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_only_ramified_place_prime_residue_dvd_norm : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  first | exact @GlobalTheory.SqTop.twist_ram_prime_dvd_Qn | exact GlobalTheory.SqTop.twist_ram_prime_dvd_Qn | (intros; apply GlobalTheory.SqTop.twist_ram_prime_dvd_Qn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwist
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

noncomputable section

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem pow_apply_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (x : Ideles E) : ((ξ.1 x : ℂˣ) : ℂ) ^ N = 1 := by
  have h1 : ((ξ ^ N : HChar E).1 x) = (ξ.1 x) ^ N := by
    rw [SubgroupClass.coe_pow, MonoidHom.pow_apply]
  rw [← Units.val_pow_eq_pow_val, ← h1, h]
  rfl

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (h : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (x : Eˣ) :
    ((ξ.locK w x : ℂˣ) : ℂ) ^ N = 1 :=
  pow_apply_eq_one h _

theorem isUnitary_of_orderDvd {ξ : HChar E} {N : ℕ} (hN : 0 < N) (h : ξ.OrderDvd N) : IsUnitary ξ := fun x =>
  Complex.norm_eq_one_of_pow_eq_one (pow_apply_eq_one h x) hN.ne'

theorem expAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.UnrAt w) (hξ : ExpAt ξ w a) :
    ExpAt (χ * ξ) w a := by
  intro k
  have hk : χ.LevelLe w k := hχ.levelLe k
  refine ⟨fun hx => (hξ k).1 ?_, fun hn => hk.mul ((hξ k).2 hn)⟩
  have := hk.inv.mul hx
  rwa [inv_mul_cancel_left] at this

theorem psiAt_natMul (w : HeightOneSpectrum (𝓞 E)) (t : w.adicCompletion E) (k : ℕ) :
    psiAt w ((k : w.adicCompletion E) * t) = psiAt w t ^ k := by
  induction k with
  | zero => simpa using psiAt_eq_one (w := w) (t := 0) (by simp)
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, psiAt_add, ih, pow_succ]

theorem gaussSumAt_unr_mul {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.UnrAt w) {a : ℕ} (ha : a ≠ 0) (c : Eˣ) :
    gaussSumAt (χ * ξ) w a c = gaussSumAt ξ w a c := by
  unfold gaussSumAt
  congr 1
  funext y
  have hy := out_notMem w ha y
  have hy1 : w.valuation E ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) = 1 :=
    (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have hz0 : ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a) : 𝓞 E) : E) ≠ 0 := fun h => by
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  rw [gaussTerm, gaussTerm, dite_eq_right hz0, dite_eq_right hz0]
  have h1 : χ.locK w (Units.mk0 _ hz0) = 1 := by
    refine hχ _ ?_
    show Valued.v (((atFin w (Units.mk0 _ hz0)) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    simp only [atFin, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Units.val_mk0]
    have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
    rw [hval, hy1]
  have e : (χ * ξ).locK w (Units.mk0 _ hz0) = χ.locK w (Units.mk0 _ hz0) * ξ.locK w (Units.mk0 _ hz0) := rfl
  rw [e, h1, one_mul]

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

variable {E : Type} [Field E] [NumberField E]

theorem exists_gaussSumAt_dvd {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {q N : ℕ} (hq : q.Prime) (hqw : Ideal.absNorm w.asIdeal = q) (hN : 0 < N) (hξN : ξ.OrderDvd N) (hξ : ExpAt ξ w 1)
    (hξK : ∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) (hqK : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) :
    ∃ g : 𝓞 K, σ (g : K) = gaussSumAt ξ w 1 (unif w ^ (1 + diffExp w)) ∧ g ∣ (q : 𝓞 K) := by
  classical
  set c : Eˣ := unif w ^ (1 + diffExp w) with hc
  haveI : Fintype (𝓞 E ⧸ w.asIdeal ^ 1)ˣ := Fintype.ofFinite _
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hqv : w.valuation E ((q : 𝓞 E) : E) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have h := valuation_sub_le (w := w) (a := 1) (y := (q : 𝓞 E)) (y' := 0)
      (by rw [sub_zero, pow_one, ← hqw]; exact Ideal.absNorm_mem _)
    simpa using h
  have hterm : ∀ y : (𝓞 E ⧸ w.asIdeal ^ 1)ˣ, ∃ x : K,
      σ x = gaussTerm ξ w c ((Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1) : 𝓞 E) : E) ∧ x ^ (N * q) = 1 := by
    intro y
    have hy := out_notMem w one_ne_zero y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ 1)
    have hy1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by
      rw [h, map_zero] at hy1
      exact zero_ne_one hy1
    rw [gaussTerm, dite_eq_right hz0]
    obtain ⟨x1, hx1⟩ := hξK (Units.mk0 _ hz0)⁻¹
    have hp : psiAt w (algebraMap E (w.adicCompletion E) ((z : E) / c)) ^ q = 1 := by
      rw [← psiAt_natMul]
      apply psiAt_eq_one
      have e : ((q : ℕ) : w.adicCompletion E) * algebraMap E (w.adicCompletion E) ((z : E) / c) =
          algebraMap E (w.adicCompletion E) (((q : 𝓞 E) : E) * ((z : E) / c)) := by simp
      rw [e, hval, map_mul, map_div₀, hy1, hc, valuation_unif_pow, one_div, ← div_eq_mul_inv,
        div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
      convert hqv using 2
      push_cast
      ring
    obtain ⟨x2, hx2⟩ := hqK _ hp
    have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
    have hx2q : x2 ^ q = 1 := σ.injective (by rw [map_pow, hx2, hp, map_one])
    refine ⟨x1 * x2, by rw [map_mul, hx1, hx2, map_inv], ?_⟩
    rw [mul_pow, pow_mul, hx1N, one_pow, one_mul, mul_comm N q, pow_mul, hx2q, one_pow]
  choose X hX using hterm
  have hpos : 0 < N * q := Nat.mul_pos hN hq.pos
  have hXi : ∀ y, IsIntegral ℤ (X y) := fun y => IsIntegral.of_pow hpos (by rw [(hX y).2]; exact isIntegral_one)
  have hXi' : ∀ y, IsIntegral ℤ (X y)⁻¹ := fun y =>
    IsIntegral.of_pow hpos (by rw [inv_pow, (hX y).2, inv_one]; exact isIntegral_one)
  have hnorm : ∀ y, ‖σ (X y)‖ = 1 := fun y =>
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, (hX y).2, map_one]) hpos.ne'
  have hgi : IsIntegral ℤ (∑ y, X y) := IsIntegral.sum _ fun y _ => hXi y
  have hgi' : IsIntegral ℤ (∑ y, (X y)⁻¹) := IsIntegral.sum _ fun y _ => hXi' y
  have hσg : σ (∑ y, X y) = gaussSumAt ξ w 1 c := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, gaussSumAt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun y _ => (hX y).1
  have hσg' : σ (∑ y, (X y)⁻¹) = starRingEnd ℂ (gaussSumAt ξ w 1 c) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hσg, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [map_inv₀, Complex.inv_eq_conj (hnorm y)]
  have hu : IsUnitary ξ := isUnitary_of_orderDvd hN hξN
  have hG := GlobalTheory.GaussMod.gaussSumAt_normSq ξ w 1 c one_ne_zero hξ hu (valuation_unif_pow w _)
  have hprod : (∑ y, X y) * (∑ y, (X y)⁻¹) = (q : K) := σ.injective (by
    rw [map_mul, hσg, hσg', Complex.mul_conj, Complex.normSq_eq_norm_sq, hG, hqw, map_natCast]
    push_cast
    ring)
  refine ⟨⟨_, hgi⟩, hσg, ⟨⟨_, hgi'⟩, RingOfIntegers.ext ?_⟩⟩
  have e : ((q : 𝓞 K) : K) = (q : K) := by simp
  rw [e, ← hprod]
  rfl

end GlobalTheory.TameTwistEps

namespace GlobalTheory.TameTwistEps

theorem locEps_tame_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  intro E _ _ K _ _ _ σ χ ξ w q m N s hq hcard hqm hN hξN hχ hξ hξK hqK hs
  have hqw : Ideal.absNorm w.asIdeal = q := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hcard
  refine ⟨expAt_unr_mul hχ hξ, ?_⟩
  obtain ⟨gG, hgG, hdvd⟩ := exists_gaussSumAt_dvd σ hq hqw hN hξN hξ hξK hqK
  obtain ⟨x1, hx1⟩ := hξK (unif w ^ (1 + diffExp w))
  have hx1N : x1 ^ N = 1 := σ.injective (by rw [map_pow, hx1, locK_pow_eq_one hξN, map_one])
  have hx1i : IsIntegral ℤ x1 := IsIntegral.of_pow hN (by rw [hx1N]; exact isIntegral_one)
  set a1 : 𝓞 K := ⟨x1, hx1i⟩ with ha1d
  have ha1 : IsUnit a1 := by
    have e : ((a1 : 𝓞 K) : K) = x1 := rfl
    exact IsUnit.of_pow_eq_one (RingOfIntegers.ext (by push_cast; exact (congrArg (· ^ N) e).trans hx1N)) hN.ne'
  have hqm' : (q : 𝓞 K) ∣ (m : 𝓞 K) := Nat.cast_dvd_cast hqm
  refine ⟨x1 * (q : K) ^ (-s).toNat * (gG : K), ?_, ?_⟩
  · have h1 : GlobalTheory.Square.IsAwayUnit m x1 := GlobalTheory.Square.IsAwayUnit.of_dvd (a := a1) (k := 0) (by simpa using ha1.dvd)
    have h2 : GlobalTheory.Square.IsAwayUnit m ((q : K) ^ (-s).toNat) := by
      have := GlobalTheory.Square.IsAwayUnit.of_dvd (K := K) (m := m) (a := (q : 𝓞 K) ^ (-s).toNat) (pow_dvd_pow_of_dvd hqm' _)
      simpa using this
    have h3 : GlobalTheory.Square.IsAwayUnit m (gG : K) := GlobalTheory.Square.IsAwayUnit.of_dvd (k := 1) (by rw [pow_one]; exact hdvd.trans hqm')
    exact (h1.mul h2).mul h3
  · have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hj : (((-s).toNat : ℕ) : ℂ) = -(s : ℂ) := by
      have : (((-s).toNat : ℕ) : ℤ) = -s := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    have e1 : ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((1 + diffExp w : ℕ) : ℂ)) =
        ((q : ℕ) : ℂ) ^ (-(s : ℂ) * ((0 + diffExp w : ℕ) : ℂ)) * (q : ℂ) ^ ((-s).toNat) := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, hj]
      congr 1
      push_cast
      ring
    have e2 : (χ * ξ).locK w (unif w ^ (1 + diffExp w)) =
        χ.val w * χ.locK w (unif w ^ (0 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) := by
      show χ.locK w (unif w ^ (1 + diffExp w)) * ξ.locK w (unif w ^ (1 + diffExp w)) = _
      rw [pow_add, pow_one, map_mul, zero_add]
      rfl
    rw [locEps, locEps, if_neg one_ne_zero, if_pos rfl, gaussSumAt_unr_mul hχ one_ne_zero, hqw, e1, e2, map_mul, map_mul,
      hx1, hgG, map_pow σ, map_natCast σ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

end GlobalTheory.TameTwistEps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEpsilonFactorTameFiniteOrderTwistStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localEpsilonFactor_tame_finiteOrder_twist : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q m N : ℕ) (s : ℤ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → q ∣ m → 0 < N → ξ.OrderDvd N → χ.UnrAt w → ExpAt ξ w 1 → (∀ x : Eˣ, ((ξ.locK w x : ℂˣ) : ℂ) ∈ Set.range σ) → (∀ z : ℂ, z ^ q = 1 → z ∈ Set.range σ) → s ≤ 0 → ExpAt (χ * ξ) w 1 ∧ ∃ g : K, GlobalTheory.Square.IsAwayUnit m g ∧ locEps (χ * ξ) w 1 (s : ℂ) = σ g * ((χ.val w : ℂˣ) : ℂ) * locEps χ w 0 (s : ℂ) := by
  first | exact @GlobalTheory.TameTwistEps.locEps_tame_twist | exact GlobalTheory.TameTwistEps.locEps_tame_twist | (intros; apply GlobalTheory.TameTwistEps.locEps_tame_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameChar
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
open Formalism.L2.Host (unif atFin unif_spec IsUnitAt)

namespace GlobalTheory.TameTwist

theorem sum_mul_eq_of_concentrated {U : Type} [CommGroup U] [Fintype U] (H : Subgroup U) (f g : U → ℂ)
    (hg : ∀ u, ∀ h ∈ H, g (u * h) = g u)
    (huniq : ∀ u v : U, (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)) →
      (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (v * k * h) = μ * f (v * k)) → u * v⁻¹ ∈ H) :
    ∃ u₀ : U, ∑ u, f u * g u = g u₀ * ∑ u, f u := by
  classical
  let Bad : U → Prop := fun u => ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)
  have hzero : ∀ u, Bad u → ∑ k : H, f (u * k) = 0 := by
    rintro u ⟨h, hh, μ, hμ, hf⟩
    have e : ∑ k : H, f (u * k) = μ * ∑ k : H, f (u * k) := by
      rw [Finset.mul_sum]
      calc ∑ k : H, f (u * k) = ∑ k : H, f (u * ((k * ⟨h, hh⟩ : H) : U)) :=
            (Fintype.sum_equiv (Equiv.mulRight (⟨h, hh⟩ : H)) _ _ (fun k => rfl)).symm
        _ = ∑ k : H, μ * f (u * k) := Finset.sum_congr rfl fun k _ => by
            rw [Subgroup.coe_mul, ← mul_assoc]
            exact hf k k.2
    have h2 : (1 - μ) * ∑ k : H, f (u * k) = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hμ))
  have main : ∀ u₀ : U, (∀ u, ¬ Bad u → g u = g u₀) → ∑ u, f u * g u = g u₀ * ∑ u, f u := by
    intro u₀ hu₀
    have key : ∀ u, ∑ k : H, f (u * k) * (g (u * k) - g u₀) = 0 := by
      intro u
      have hgk : ∀ k : H, g (u * k) = g u := fun k => hg u k k.2
      simp_rw [hgk, ← Finset.sum_mul]
      by_cases hu : Bad u
      · rw [hzero u hu, zero_mul]
      · rw [hu₀ u hu, sub_self, mul_zero]
    have e : ∀ k : H, ∑ u, f (u * k) * (g (u * k) - g u₀) = ∑ u, f u * (g u - g u₀) := fun k =>
      Fintype.sum_equiv (Equiv.mulRight (k : U)) _ _ (fun u => rfl)
    have h2 : (Fintype.card H : ℂ) * ∑ u, f u * (g u - g u₀) = 0 := by
      calc (Fintype.card H : ℂ) * ∑ u, f u * (g u - g u₀) = ∑ k : H, ∑ u, f u * (g u - g u₀) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ∑ k : H, ∑ u, f (u * k) * (g (u * k) - g u₀) := by simp_rw [e]
        _ = ∑ u, ∑ k : H, f (u * k) * (g (u * k) - g u₀) := Finset.sum_comm
        _ = 0 := by simp_rw [key, Finset.sum_const_zero]
    have h3 : ∑ u, f u * (g u - g u₀) = 0 :=
      (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have h4 : ∑ u, f u * g u - g u₀ * ∑ u, f u = ∑ u, f u * (g u - g u₀) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [← sub_eq_zero, h4, h3]
  by_cases hex : ∃ u₀, ¬ Bad u₀
  · obtain ⟨u₀, hu₀⟩ := hex
    refine ⟨u₀, main u₀ fun u hu => ?_⟩
    have h1 : u₀ * (u₀⁻¹ * u) = u := mul_inv_cancel_left u₀ u
    have h2 : u₀⁻¹ * u ∈ H := by
      have := huniq u u₀ hu hu₀
      rwa [mul_comm] at this
    rw [← hg u₀ _ h2, h1]
  · push_neg at hex
    exact ⟨1, main 1 fun u hu => absurd (hex u) hu⟩

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

variable {E : Type} [Field E] [NumberField E]

theorem locK_eq_of_levelLe {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {m : ℕ} (hξ : ξ.LevelLe w m) {a b : Eˣ}
    (ha : w.valuation E (a : E) = 1) (hb : w.valuation E (b : E) = 1)
    (hd : w.valuation E ((a : E) - b) ≤ WithZero.exp (-(m : ℤ))) : ξ.locK w a = ξ.locK w b := by
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have e : ((atFin w (a * b⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      algebraMap E (w.adicCompletion E) ((a : E) / b) := by
    simp [atFin, div_eq_mul_inv]
  have h1 : ξ.loc w (atFin w (a * b⁻¹)) = 1 := by
    refine hξ _ ?_ ?_
    · rw [IsUnitAt, e, hval, map_div₀, ha, hb, div_one]
    · rw [e, ← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, hval, div_sub_one b.ne_zero, map_div₀, hb, div_one]
      exact hd
  have h2 : ξ.locK w (a * b⁻¹) = 1 := h1
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2


open Classical in
def twInv (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (y : E) : ℂ :=
  if h : y = 0 then 0 else (((ξ.locK w (Units.mk0 y h))⁻¹ : ℂˣ) : ℂ)

theorem gaussTerm_mul (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (c : Eˣ) (y : E) :
    gaussTerm (χ * ξ) w c y = gaussTerm χ w c y * twInv ξ w y := by
  have hm : ∀ x, (χ * ξ).locK w x = χ.locK w x * ξ.locK w x := fun x => rfl
  unfold gaussTerm twInv
  split_ifs with h
  · simp
  · rw [hm, mul_inv, Units.val_mul]
    ring

theorem gaussTerm_mul_one_add (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (c : Eˣ) {r : E} (hr : r ≠ 0) {z : E} (e : Eˣ)
    (he : (e : E) = 1 + z) :
    gaussTerm χ w c (r * (1 + z)) =
      gaussTerm χ w c r * ((((χ.locK w e)⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) (r * z / c))) := by
  have h1 : r * (1 + z) ≠ 0 := by rw [← he]; exact mul_ne_zero hr e.ne_zero
  have hu : Units.mk0 _ h1 = Units.mk0 r hr * e := by ext; simp [he]
  have hψ : r * (1 + z) / c = r / c + r * z / c := by ring
  rw [gaussTerm, gaussTerm, dif_neg h1, dif_neg hr, hu, map_mul, hψ, map_add (f := _), psiAt_add]
  simp only [mul_inv, Units.val_mul]
  ring

theorem psiAt_mul_congr {w : HeightOneSpectrum (𝓞 E)} {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((2 + diffExp w : ℕ) : ℤ))) {r r' z : 𝓞 E} (h : r - r' ∈ w.asIdeal)
    (hz : z ∈ w.asIdeal) :
    psiAt w (algebraMap E (w.adicCompletion E) ((r : E) * z / c)) =
      psiAt w (algebraMap E (w.adicCompletion E) ((r' : E) * z / c)) := by
  have e : (r : E) * z / c = (r' : E) * z / c + (((r - r') * z : 𝓞 E) : E) / c := by push_cast; ring
  have hm : (r - r') * z - 0 ∈ w.asIdeal ^ 2 := by rw [sub_zero, pow_two]; exact Ideal.mul_mem_mul h hz
  have hv := valuation_sub_le (E := E) hm
  rw [e, map_add (f := _), psiAt_add, psiAt_eq_one (t := algebraMap E _ ((((r - r') * z : 𝓞 E) : E) / c)), mul_one]
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  rw [hval, map_div₀, hc,
    div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
  rw [show ((0 : 𝓞 E) : E) = 0 from rfl, sub_zero] at hv
  convert hv using 2
  push_cast
  ring

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

variable {E : Type} [Field E] [NumberField E]

theorem mem_of_psiAt_eq_one {w : HeightOneSpectrum (𝓞 E)} {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((2 + diffExp w : ℕ) : ℤ))) {d : 𝓞 E}
    (h : ∀ z : 𝓞 E, z ∈ w.asIdeal → psiAt w (algebraMap E (w.adicCompletion E) ((d : E) * z / c)) = 1) :
    d ∈ w.asIdeal := by
  by_contra hd
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hval : ∀ x : E, Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x := fun x =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x
  have hd1 : w.valuation E (d : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hd
  have hπ1 : w.valuation E (π : E) = WithZero.exp (-1) := by
    rw [← hπ, ← w.valuation_of_algebraMap (K := E)]
  have hπP : π ∈ w.asIdeal := by
    rw [← w.intValuation_lt_one_iff_mem, hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  set t := algebraMap E (w.adicCompletion E) ((d : E) * π / c) with ht_def
  have ht : Valued.v t = WithZero.exp ((1 + diffExp w : ℕ) : ℤ) := by
    rw [ht_def, hval, map_div₀, map_mul, hd1, hπ1, hc, one_mul, ← WithZero.exp_sub]
    congr 1
    push_cast
    ring
  have hnot : ¬ ∀ r ∈ w.adicCompletionIntegers E, psiAt w (t * r) = 1 := by
    rw [psiAt_conductor, ht, WithZero.exp_le_exp]
    push_cast
    omega
  push_neg at hnot
  obtain ⟨r, hr, hψ⟩ := hnot
  obtain ⟨r₀, hr₀⟩ := Formalism.UG.P.glint_exists_approx w ⟨r, hr⟩
  apply hψ
  have hr₀' : Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) ≤ WithZero.exp (-1) := by
    have h1 : Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) < 1 := hr₀
    generalize Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) = x at h1 ⊢
    by_cases hx : x = 0
    · rw [hx]; exact zero_le'
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have e : t * r = algebraMap E (w.adicCompletion E) ((d : E) * ((π * r₀ : 𝓞 E) : E) / c) +
      t * (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀) := by
    rw [ht_def, IsScalarTower.algebraMap_apply (𝓞 E) E (w.adicCompletion E) r₀,
      show (d : E) * ((π * r₀ : 𝓞 E) : E) / c = ((d : E) * π / c) * algebraMap (𝓞 E) E r₀ by
        rw [show algebraMap (𝓞 E) E r₀ = (r₀ : E) from rfl]; push_cast; ring, map_mul]
    ring
  rw [e, psiAt_add, h _ (Ideal.mul_mem_right _ _ hπP), one_mul]
  apply psiAt_eq_one
  rw [map_mul, ht]
  calc WithZero.exp ((1 + diffExp w : ℕ) : ℤ) * Valued.v (r - algebraMap (𝓞 E) (w.adicCompletion E) r₀)
      ≤ WithZero.exp ((1 + diffExp w : ℕ) : ℤ) * WithZero.exp (-1) := by gcongr
    _ = WithZero.exp (diffExp w : ℤ) := by rw [← WithZero.exp_add]; congr 1; push_cast; ring

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

variable {E : Type} [Field E] [NumberField E]

theorem gaussSumAt_mul_tame {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (hχ : χ.LevelLe w 2) (hξ : ξ.TameAt w) {c : Eˣ}
    (hc : w.valuation E (c : E) = WithZero.exp (-((2 + diffExp w : ℕ) : ℤ))) :
    ∃ x₀ : Eˣ, gaussSumAt (χ * ξ) w 2 c = (((ξ.locK w x₀)⁻¹ : ℂˣ) : ℂ) * gaussSumAt χ w 2 c := by
  classical
  have := w.isMaximal
  have := Fintype.ofFinite (𝓞 E ⧸ w.asIdeal ^ 2)ˣ
  let rep : 𝓞 E ⧸ w.asIdeal ^ 2 → 𝓞 E := fun x => Quotient.out x
  let φ : 𝓞 E ⧸ w.asIdeal ^ 2 →+* 𝓞 E ⧸ w.asIdeal := Ideal.Quotient.factor (Ideal.pow_le_self two_ne_zero)
  let H : Subgroup (𝓞 E ⧸ w.asIdeal ^ 2)ˣ := (Units.map φ.toMonoidHom).ker
  have hrep2 : ∀ x, Ideal.Quotient.mk (w.asIdeal ^ 2) (rep x) = x := fun x => Ideal.Quotient.mk_out x
  have hrep : ∀ x, Ideal.Quotient.mk w.asIdeal (rep x) = φ x := fun x => by
    conv_rhs => rw [← hrep2 x]
    rfl
  have hnm : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, rep u ∉ w.asIdeal := fun u => out_notMem w two_ne_zero u
  have hv1 : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, w.valuation E (rep u : E) = 1 := fun u =>
    (w.valuation_eq_one_iff_notMem (K := E)).2 (hnm u)
  have hne : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, (rep u : E) ≠ 0 := fun u h => by
    have := hv1 u
    rw [h, map_zero] at this
    exact zero_ne_one this

  have hmemH : ∀ u v : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, u * v⁻¹ ∈ H ↔ rep u - rep v ∈ w.asIdeal := by
    intro u v
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, ← Ideal.Quotient.eq, hrep, hrep, Units.ext_iff]
    rfl
  have hH' : ∀ u k : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ, k ∈ H → rep (u * k : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ) - rep u ∈ w.asIdeal := by
    intro u k hk
    rw [← hmemH, mul_comm u k, mul_inv_cancel_right]
    exact hk
  let f : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ → ℂ := fun u => gaussTerm χ w c (rep u)
  let g : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ → ℂ := fun u => twInv ξ w (rep u)
  have hg : ∀ u, ∀ k ∈ H, g (u * k) = g u := by
    intro u k hk
    show twInv ξ w (rep ↑(u * k)) = twInv ξ w (rep ↑u)
    rw [twInv, twInv, dif_neg (hne (u * k)), dif_neg (hne u)]
    have hd := valuation_sub_le (E := E) (w := w) (a := 1) (y := rep ↑(u * k)) (y' := rep ↑u)
      (by rw [pow_one]; exact hH' u k hk)
    have hξ1 : ξ.LevelLe w 1 := hξ
    have hd' : w.valuation E (((Units.mk0 _ (hne (u * k)) : Eˣ) : E) - ((Units.mk0 _ (hne u) : Eˣ) : E)) ≤
        WithZero.exp (-((1 : ℕ) : ℤ)) := by
      rw [Units.val_mk0, Units.val_mk0]; exact hd
    have ha : w.valuation E ((Units.mk0 _ (hne (u * k)) : Eˣ) : E) = 1 := by rw [Units.val_mk0]; exact hv1 (u * k)
    have hb : w.valuation E ((Units.mk0 _ (hne u) : Eˣ) : E) = 1 := by rw [Units.val_mk0]; exact hv1 u
    rw [locK_eq_of_levelLe hξ1 ha hb hd']

  have hmult : ∀ (u' h : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ) (z : 𝓞 E) (e : Eˣ), (h : 𝓞 E ⧸ w.asIdeal ^ 2) = Ideal.Quotient.mk _ (1 + z) →
      (e : E) = 1 + z → z ∈ w.asIdeal →
      f (u' * h) = f u' * ((((χ.locK w e)⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) ((rep u' : E) * z / c))) := by
    intro u' h z e hh he hz
    have h1 : (1 + z) ∉ w.asIdeal := fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa using w.asIdeal.sub_mem h1 hz))
    have h2 : rep u' * (1 + z) ∉ w.asIdeal := fun h2 => (w.isPrime.mem_or_mem h2).elim (hnm u') h1
    have h3 : rep (u' * h : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ) - rep u' * (1 + z) ∈ w.asIdeal ^ 2 := by
      rw [← Ideal.Quotient.eq, hrep2, map_mul, hrep2, ← hh, Units.val_mul]
    simp only [f]
    rw [gaussTerm_congr hχ hc (hnm _) h2 h3,
      show ((rep u' * (1 + z) : 𝓞 E) : E) = (rep u' : E) * (1 + (z : E)) by push_cast; ring]
    exact gaussTerm_mul_one_add χ w c (hne u') e (by rw [he])

  have huniq : ∀ u v : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ,
      (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)) →
      (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (v * k * h) = μ * f (v * k)) → u * v⁻¹ ∈ H := by
    intro u v hu hv
    rw [hmemH]
    refine mem_of_psiAt_eq_one hc fun z hz => ?_
    have h1 : (1 + z) ∉ w.asIdeal := fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
      simpa using w.asIdeal.sub_mem h1 hz))
    have he0 : ((1 + z : 𝓞 E) : E) ≠ 0 := fun h0 => h1 (by
      have : (1 + z : 𝓞 E) = 0 := Subtype.ext h0
      rw [this]; exact w.asIdeal.zero_mem)
    let e : Eˣ := Units.mk0 _ he0
    have he : (e : E) = 1 + (z : E) := by simp [e]
    obtain ⟨h, hh⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem w.asIdeal (n := 2) h1
    have hhH : h ∈ H := by
      rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one]
      show φ h = 1
      rw [hh]
      show Ideal.Quotient.mk w.asIdeal (1 + z) = 1
      rw [map_add (f := _), map_one, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero]

    have key : ∀ u : (𝓞 E ⧸ w.asIdeal ^ 2)ˣ,
        (¬ ∃ h ∈ H, ∃ μ : ℂ, μ ≠ 1 ∧ ∀ k ∈ H, f (u * k * h) = μ * f (u * k)) →
        psiAt w (algebraMap E (w.adicCompletion E) ((rep u : E) * z / c)) = ((χ.locK w e : ℂˣ) : ℂ) := by
      intro u hu
      by_contra hne'
      refine hu ⟨h, hhH, (((χ.locK w e)⁻¹ : ℂˣ) : ℂ) * psiAt w (algebraMap E (w.adicCompletion E) ((rep u : E) * z / c)),
        ?_, fun k hk => ?_⟩
      · intro h1
        apply hne'
        rw [Units.val_inv_eq_inv_val, inv_mul_eq_one₀ (χ.locK w e).ne_zero] at h1
        exact h1.symm
      · rw [hmult (u * k) h z e hh he hz, psiAt_mul_congr hc (hH' u k hk) hz, mul_comm]
    have ev := key v hv
    have eu := key u hu
    have e2 : ((rep u : E) * z / c) = (rep v : E) * z / c + (((rep u - rep v : 𝓞 E) : E) * z / c) := by
      push_cast; ring
    rw [e2, map_add (f := _), psiAt_add, ev] at eu
    have := (χ.locK w e).ne_zero
    exact (mul_eq_left₀ this).1 eu
  obtain ⟨u₀, hu₀⟩ := sum_mul_eq_of_concentrated H f g hg huniq
  refine ⟨Units.mk0 _ (hne u₀), ?_⟩
  rw [gaussSumAt, gaussSumAt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp_rw [gaussTerm_mul]
  have hg0 : g u₀ = (((ξ.locK w (Units.mk0 _ (hne u₀)))⁻¹ : ℂˣ) : ℂ) := by
    simp only [g, twInv, dif_neg (hne u₀)]
  rw [← hg0]
  exact hu₀

end GlobalTheory.TameTwist

namespace GlobalTheory.TameTwist

theorem locEps_mul_tame : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) (s : ℂ),
    q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → (q : 𝓞 E) ∉ w.asIdeal ^ 2 → ExpAt χ w 2 → ξ.TameAt w →
      ExpAt (χ * ξ) w 2 ∧ ∃ y : Eˣ, locEps (χ * ξ) w 2 s = ((ξ.locK w y : ℂˣ) : ℂ) * locEps χ w 2 s := by
  intro E _ _ χ ξ w q s _ _ _ hχ hξ
  have mono : ∀ {θ : HChar E} {m m' : ℕ}, m ≤ m' → θ.LevelLe w m → θ.LevelLe w m' := fun hm h x hx hd =>
    h x hx (hd.trans (WithZero.exp_le_exp.2 (by omega)))
  have hξ1 : ξ.LevelLe w 1 := hξ
  have hmul : ∀ {θ θ' : HChar E} {m : ℕ}, θ.LevelLe w m → θ'.LevelLe w m → (θ * θ').LevelLe w m :=
    fun {θ θ' m} h h' x hx hd => by
      change θ.loc w x * θ'.loc w x = 1
      rw [h x hx hd, h' x hx hd, one_mul]
  have hχ2 : χ.LevelLe w 2 := (hχ 2).2 le_rfl
  refine ⟨fun m => ⟨fun h => ?_, fun hm => hmul ((hχ m).2 hm) (mono (by omega) hξ1)⟩, ?_⟩
  · by_contra hm
    have h1 : (χ * ξ).LevelLe w 1 := mono (by omega) h
    have h2 : χ.LevelLe w 1 := by
      have h3 : (χ * ξ * ξ⁻¹).LevelLe w 1 :=
        hmul h1 (fun x hx hd => by
          change (ξ.loc w x)⁻¹ = 1
          rw [hξ1 x hx hd, inv_one])
      rwa [mul_inv_cancel_right] at h3
    exact absurd ((hχ 1).1 h2) (by omega)
  · obtain ⟨x₀, hx₀⟩ := gaussSumAt_mul_tame hχ2 hξ (valuation_unif_pow w (2 + diffExp w))
    refine ⟨unif w ^ (2 + diffExp w) * x₀⁻¹, ?_⟩
    rw [locEps, locEps, if_neg two_ne_zero, if_neg two_ne_zero, hx₀]
    have hm : ∀ x, (χ * ξ).locK w x = χ.locK w x * ξ.locK w x := fun x => rfl
    rw [hm, map_mul, map_inv]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end GlobalTheory.TameTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateLocalEpsilonFactorMulTameCharStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateLocalEpsilonFactor_mul_tameChar : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) (s : ℂ), q.Prime → Nat.card (𝓞 E ⧸ w.asIdeal) = q → (q : 𝓞 E) ∉ w.asIdeal ^ 2 → ExpAt χ w 2 → ξ.TameAt w → ExpAt (χ * ξ) w 2 ∧ ∃ y : Eˣ, locEps (χ * ξ) w 2 s = ((ξ.locK w y : ℂˣ) : ℂ) * locEps χ w 2 s := by
  first | exact @GlobalTheory.TameTwist.locEps_mul_tame | exact GlobalTheory.TameTwist.locEps_mul_tame | (intros; apply GlobalTheory.TameTwist.locEps_mul_tame <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeEps

namespace GlobalTheory.ReflVal

variable {E : Type} [Field E] [NumberField E]

theorem reflect_of_finEps (hFE : GlobalTheory.Published.HeckeTateFunctionalEquation) [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (hφ : IsCMType φ) {m : I → ℤ} (hm0 : ∃ i, m i ≠ 0) {χ χ₀ : HChar E} (hu : IsUnitary χ)
    (hu₀ : IsUnitary χ₀) (hi : HasInf χ φ m) (hi₀ : HasInf χ₀ φ m) (ht : TrivOnF χ) (ht₀ : TrivOnF χ₀)
    {a a₀ : HeightOneSpectrum (𝓞 E) →₀ ℕ} (ha : ∀ w, ExpAt χ w (a w)) (ha₀ : ∀ w, ExpAt χ₀ w (a₀ w)) {Λ Λ₀ : ℂ → ℂ}
    (hΛ : IsHeckeL χ Λ) (hΛ₀ : IsHeckeL χ₀ Λ₀) {s e : ℂ} (hs : ∀ (i : I) (k : ℕ), s + ((|m i| : ℤ) : ℂ) ≠ -k)
    (hs' : ∀ (i : I) (k : ℕ), 1 - s + ((|m i| : ℤ) : ℂ) ≠ -k) (he : finEps χ a s = e * finEps χ₀ a₀ s) :
    Λ s * Λ₀ (1 - s) = e * (Λ (1 - s) * Λ₀ s) := by
  have hcm := hFE.cm
  have h1 := hcm E I φ m χ a Λ Λ hφ hu hi hm0 ha hΛ (GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ Λ ht hΛ) s hs hs'
  have h0 := hcm E I φ m χ₀ a₀ Λ₀ Λ₀ hφ hu₀ hi₀ hm0 ha₀ hΛ₀ (GlobalTheory.T.isPrimitiveHeckeLFunction_inv_of_trivialOnMaxReal E χ₀ Λ₀ ht₀ hΛ₀) s hs hs'
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hL : LInf m s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ => mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Complex.Gamma_ne_zero (hs i))
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [he] at h1
  refine mul_left_cancel₀ hL ?_
  linear_combination Λ₀ (1 - s) * h1 - e * Λ (1 - s) * h0

end GlobalTheory.ReflVal

namespace GlobalTheory.ReflVal

variable {E : Type} [Field E] [NumberField E]

theorem finEps_eq_of_local {K : Type} [Field K] (σ : K →+* ℂ) (P : K → Prop) (h1 : P 1)
    (hmul : ∀ x y, P x → P y → P (x * y)) (χ χ₀ : HChar E) (a a₀ : HeightOneSpectrum (𝓞 E) →₀ ℕ) (s : ℂ)
    (c : HeightOneSpectrum (𝓞 E) → ℂ) (hcf : (Function.mulSupport c).Finite) (hc : ∏ᶠ w, c w = 1)
    (h : ∀ w, ∃ g, P g ∧ locEps χ w (a w) s = σ g * c w * locEps χ₀ w (a₀ w) s) :
    ∃ g, P g ∧ finEps χ a s = σ g * finEps χ₀ a₀ s := by
  classical
  choose g hg he using h
  set S := (finite_mulSupport_locEps χ a s).toFinset ∪ (finite_mulSupport_locEps χ₀ a₀ s).toFinset ∪ hcf.toFinset
  have hS1 : Function.mulSupport (fun w => locEps χ w (a w) s) ⊆ S := fun w hw => by simp [S, hw]
  have hS2 : Function.mulSupport (fun w => locEps χ₀ w (a₀ w) s) ⊆ S := fun w hw => by simp [S, hw]
  have hS3 : Function.mulSupport c ⊆ S := fun w hw => by simp [S, hw]
  have hP : ∀ T : Finset (HeightOneSpectrum (𝓞 E)), P (∏ w ∈ T, g w) := fun T => by
    induction T using Finset.induction_on with
    | empty => simpa using h1
    | insert x T hx ih => rw [Finset.prod_insert hx]; exact hmul _ _ (hg x) ih
  refine ⟨∏ w ∈ S, g w, hP S, ?_⟩
  rw [finEps, finEps, finprod_eq_prod_of_mulSupport_subset _ hS1, finprod_eq_prod_of_mulSupport_subset _ hS2,
    finprod_eq_prod_of_mulSupport_subset _ hS3] at *
  rw [Finset.prod_congr rfl fun w _ => he w, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hc, mul_one, map_prod]

theorem exists_finsupp_expAt (χ : HChar E) : ∃ a : HeightOneSpectrum (𝓞 E) →₀ ℕ, ∀ w, ExpAt χ w (a w) := by
  classical
  have h := GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hE : ∀ w, ExpAt χ w (Nat.find (h w)) := fun w m =>
    ⟨fun hm => Nat.find_min' (h w) hm, fun hm x hx hx' => Nat.find_spec (h w) x hx (hx'.trans (by
      rw [WithZero.exp_le_exp]; omega))⟩
  have hsub : Function.support (fun w => Nat.find (h w)) ⊆ {v | ¬ χ.UnrAt v} := fun w hw hu =>
    hw ((hE w).unique ((expAt_zero_iff χ w).2 hu))
  exact ⟨Finsupp.ofSupportFinite _ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).subset hsub), fun w => hE w⟩

theorem expAt_mul_of_unrAt {χ ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : ξ.UnrAt w) {n : ℕ} (hn : ExpAt χ w n) :
    ExpAt (χ * ξ) w n := fun m => by
  rw [← hn m]
  constructor
  · intro h' x hx hx'
    have := h' x hx hx'
    change χ.loc w x * ξ.loc w x = 1 at this
    rwa [h x hx, mul_one] at this
  · intro h' x hx hx'
    change χ.loc w x * ξ.loc w x = 1
    rw [h' x hx hx', h x hx, one_mul]

theorem expAt_one_of_tame {ξ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (ht : ξ.TameAt w) (hr : ¬ ξ.UnrAt w) :
    ExpAt ξ w 1 := fun m => by
  constructor
  · intro h
    by_contra c
    obtain rfl : m = 0 := by omega
    exact hr ((ξ.unrAt_iff w).2 h)
  · intro hm x hx hx'
    exact ht x hx (hx'.trans (by rw [WithZero.exp_le_exp]; omega))

end GlobalTheory.ReflVal

namespace GlobalTheory.ReflVal

open Formalism.L2.Host (unif atFin)

theorem locEps_mul_of_unrAt : ∀ (E : Type) [Field E] [NumberField E] (χ ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (s : ℂ), ξ.UnrAt w → locEps (χ * ξ) w a s = ((ξ.locK w (unif w ^ (a + diffExp w)) : ℂˣ) : ℂ) * locEps χ w a s := by
  intro E _ _ χ ξ w a s hU
  have hloc : ∀ x : Eˣ, (χ * ξ).locK w x = χ.locK w x * ξ.locK w x := fun x => rfl
  have hG : a ≠ 0 → gaussSumAt (χ * ξ) w a (unif w ^ (a + diffExp w)) = gaussSumAt χ w a (unif w ^ (a + diffExp w)) := by
    intro ha
    unfold gaussSumAt
    congr 1
    funext y
    have hy := out_notMem w ha y
    set z : 𝓞 E := Quotient.out (y : 𝓞 E ⧸ w.asIdeal ^ a)
    have hz1 : w.valuation E (z : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
    have hz0 : (z : E) ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
    unfold gaussTerm
    rw [dite_eq_right hz0, dite_eq_right hz0, hloc]
    have h1 : ξ.locK w (Units.mk0 _ hz0) = 1 := hU _ (by
      show Valued.v (((z : E) : w.adicCompletion E)) = 1
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hz1])
    rw [h1, mul_one]
  unfold locEps
  split_ifs with ha
  · rw [hloc, Units.val_mul]; ring
  · rw [hloc, Units.val_mul, hG ha]; ring

end GlobalTheory.ReflVal

namespace GlobalTheory.ReflVal

open Formalism.L2.Host (unif atFin)

variable {E : Type} [Field E] [NumberField E]

theorem locK_pow_eq_one {ξ : HChar E} {N : ℕ} (hf : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (y : Eˣ) :
    ((ξ.locK w y : ℂˣ) : ℂ) ^ N = 1 := by
  have h : (ξ ^ N).locK w y = 1 := by rw [show ξ ^ N = 1 from hf]; rfl
  have h2 : (ξ ^ N).locK w y = ξ.locK w y ^ N := by
    show (ξ.1 ^ N) _ = _
    rw [MonoidHom.pow_apply]; rfl
  rw [← Units.val_pow_eq_pow_val, ← h2, h, Units.val_one]

theorem isAwayUnit_of_locK {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {ξ : HChar E} {N : ℕ}
    (hN : 0 < N) (hf : ξ.OrderDvd N) (w : HeightOneSpectrum (𝓞 E)) (y : Eˣ) {g : K} (hg : σ g = ((ξ.locK w y : ℂˣ) : ℂ))
    {m : ℕ} (hm : 0 < m) : GlobalTheory.Square.IsAwayUnit m g := by
  refine (GlobalTheory.Square.isAwayUnit_closure K m hm).1 g N hN (σ.injective ?_)
  rw [map_pow, hg, locK_pow_eq_one hf, map_one]

end GlobalTheory.ReflVal

namespace GlobalTheory.SqTop

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.ReflVal
open Formalism.L2.Host (unif atFin)

theorem refl_square (hFE : GlobalTheory.Published.HeckeTateFunctionalEquation) {D : D7} {T : Type} {Lc : LevCh D T}
    {sc : GlobalTheory.ChiGrid.Consts} [IsCMField D.host.E] (hφ : IsCMType (cmPhi D)) {μ₀ : T} (hL : Lc.Is μ₀)
    (G : GridData Lc sc) (hb : IsBaseCond (condF G.pl)) (hc : CharsIn G D.what₂.embLL)
    (hr : ∀ t, ∀ w ∈ locPl G t, RootsIn D.what₂.embLL (Ideal.absNorm w.asIdeal ^ depthAt G w))
    (i j : Fin D.R.m) (t : T) {Λ Λ₀ : ℂ → ℂ} (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀)
    (s : ℤ) (hs1 : 1 - (e0 D i j : ℤ) ≤ s) (hs0 : s ≤ 0) :
    ∃ Ep : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) Ep ∧
      Λ s * Λ₀ ((1 - s : ℤ) : ℂ) = D.what₂.embLL Ep * (Λ ((1 - s : ℤ) : ℂ) * Λ₀ s) := by
  classical
  set ξ := Lc.xiH t with hξ
  set ν₀ := nuH G μ₀ i j with hν₀
  have e : nuH G t i j = ν₀ * ξ := by
    simp only [ν₀, ξ, nuH, hL.xi_base, mul_one]
    exact mul_div_right_comm _ _ _
  have hv := GlobalTheory.FunObj.SqNum.Model.isValChar_nu hL G i j (Nat.zero_le (halfRank D i j))
  obtain ⟨N, hN, hf⟩ := hL.xi_fin t
  have hu : IsUnitary (nuH G t i j) := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G t i j hL)
  have hm : HasInf (nuH G t i j) (cmPhi D) (fun τ => ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) := by
    intro k
    rw [e, Formalism.L2.Host.HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one ξ hN hf k, mul_one]
    exact hv.1.2.2.1 k
  have ht : TrivOnF (nuH G t i j) := by rw [e]; exact hv.1.2.1.mul (hL.xi_triv t)
  obtain ⟨a, ha⟩ := exists_finsupp_expAt (nuH G t i j)
  obtain ⟨a₀, ha₀⟩ := exists_finsupp_expAt ν₀
  have hbig : ∀ τ, (e0 D i j : ℤ) < ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) := fun τ => by
    have a0 := (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le (halfRank D i j))).1
    have a1 := GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ (le_refl (halfRank D i j))
    have a2 : e0 D i j ≤ halfRank D i j := by unfold e0 halfRank botBig botSmall; omega
    omega
  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.E) := inferInstance
    obtain ⟨τ, -⟩ := hφ w.embedding
    exact ⟨τ⟩
  have hm0 : ∃ τ, ((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ) ≠ 0 := ⟨τ₀, by have := hbig τ₀; omega⟩
  have hs : ∀ τ (k : ℕ), (s : ℂ) + ((|((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| : ℤ) : ℂ) ≠ -k := by
    intro τ k h
    have h2 : ((s + |((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| + k : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination h
    have h3 := Int.cast_eq_zero.1 h2
    have := hbig τ
    rw [abs_of_nonneg (by omega)] at h3
    omega
  have hs' : ∀ τ (k : ℕ), 1 - (s : ℂ) + ((|((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| : ℤ) : ℂ) ≠ -k := by
    intro τ k h
    have h2 : ((1 - s + |((kap D sc.cGap i j 0 τ : ℕ) : ℤ) + ((0 : ℕ) : ℤ)| + k : ℤ) : ℂ) = 0 := by
      push_cast; linear_combination h
    have h3 := Int.cast_eq_zero.1 h2
    have := hbig τ
    rw [abs_of_nonneg (by omega)] at h3
    omega
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ =>
    Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  let c : HeightOneSpectrum (𝓞 D.host.E) → ℂ := fun w => ∏ᶠ (_ : ¬ ξ.UnrAt w ∧ ν₀.UnrAt w), ((ν₀.val w : ℂˣ) : ℂ)
  have hc1 : ∀ w, ξ.UnrAt w → c w = 1 := fun w h => by
    simp only [c]; rw [finprod_eq_if, ite_eq_right (fun h' => h'.1 h)]
  have hcf : (Function.mulSupport c).Finite :=
    (GlobalTheory.Mem.UnrAe.finite_ramified ξ).subset fun w hw h => hw (hc1 w h)
  have hcprod : ∏ᶠ w, c w = 1 := GlobalTheory.T.finprod_nu_values_twist_only_ramified_eq_one G hL i j t
  have hloc : ∀ w, ∃ g, GlobalTheory.Square.IsAwayUnit (Qn G t) g ∧
      locEps (nuH G t i j) w (a w) (s : ℂ) = D.what₂.embLL g * c w * locEps ν₀ w (a₀ w) (s : ℂ) := by
    intro w
    have hxi : ∀ y : D.host.Eˣ, ((ξ.locK w y : ℂˣ) : ℂ) ∈ Set.range D.what₂.embLL := fun y => hc.xi t w (atFin w y)
    by_cases hU : ξ.UnrAt w
    · have hE := expAt_mul_of_unrAt hU (ha₀ w)
      rw [← e] at hE
      rw [(ha w).unique hE, e, locEps_mul_of_unrAt _ ν₀ ξ w _ _ hU, hc1 w hU]
      obtain ⟨g, hg⟩ := hxi (unif w ^ (a₀ w + diffExp w))
      exact ⟨g, isAwayUnit_of_locK D.what₂.embLL hN hf w _ hg hQn, by rw [hg, mul_one]⟩
    by_cases hU0 : ν₀.UnrAt w
    · obtain ⟨q, hq, hcard, hqQ, w', hw', hw'N⟩ := GlobalTheory.T.twist_only_ramified_place_prime_residue_dvd_norm G hL i j t w hU hU0
      have h1 := expAt_one_of_tame (hL.xi_tame t w) hU
      have hroot : ∀ z : ℂ, z ^ q = 1 → z ∈ Set.range D.what₂.embLL := fun z hz => by
        refine hr t w' hw' z ?_
        have hd : 1 ≤ depthAt G w' := le_max_right _ _
        rw [hw'N, ← Nat.sub_add_cancel hd, pow_succ, pow_mul', hz, one_pow]
      obtain ⟨hE, g, hg, hge⟩ := GlobalTheory.T.localEpsilonFactor_tame_finiteOrder_twist _ _ D.what₂.embLL ν₀ ξ w q (Qn G t) N s hq hcard hqQ hN hf hU0 h1 hxi hroot hs0
      rw [← e] at hE
      have h0 : ExpAt ν₀ w 0 := (expAt_zero_iff ν₀ w).2 hU0
      rw [(ha w).unique hE, (ha₀ w).unique h0, e, hge]
      have hcw : c w = ((ν₀.val w : ℂˣ) : ℂ) := by
        simp only [c]; rw [finprod_eq_if, ite_eq_left ⟨hU, hU0⟩]
      exact ⟨g, hg, by rw [hcw]⟩
    · obtain ⟨q, hq, hcard, hsq, h2⟩ := GlobalTheory.T.twist_and_nu_ramified_place_degree_one_exponent_two G hL hb i j t w hU hU0
      obtain ⟨hE, y, hy⟩ := GlobalTheory.T.tateLocalEpsilonFactor_mul_tameChar _ ν₀ ξ w q (s : ℂ) hq hcard hsq h2 (hL.xi_tame t w)
      rw [← e] at hE
      rw [(ha w).unique hE, (ha₀ w).unique h2, e, hy]
      have hcw : c w = 1 := by simp only [c]; rw [finprod_eq_if, ite_eq_right (fun h' => hU0 h'.2)]
      obtain ⟨g, hg⟩ := hxi y
      exact ⟨g, isAwayUnit_of_locK D.what₂.embLL hN hf w y hg hQn, by rw [hcw, hg, mul_one]⟩
  obtain ⟨g, hg, hge⟩ := finEps_eq_of_local D.what₂.embLL (GlobalTheory.Square.IsAwayUnit (Qn G t))
    (GlobalTheory.Square.IsAwayUnit.one _) (fun x y hx hy => hx.mul hy) (nuH G t i j) ν₀ a a₀ (s : ℂ) c hcf hcprod hloc
  refine ⟨g, hg, ?_⟩
  have := reflect_of_finEps hFE hφ hm0 hu hv.1.1 hm hv.1.2.2.1 ht hv.1.2.1 ha ha₀ hΛ hΛ₀ hs hs' hge
  push_cast
  exact this

theorem refl_of_functionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation → FieldDat → LNe → Refl := by
  intro hFE hFD _
  obtain ⟨CF0, h⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h'⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hCM, -, hFd, hb, -⟩ := h' C hC D large₂ he hx hR T Lc μ₀ hL G
  obtain ⟨-, -, -, -, -, -, hφ, -⟩ := hFd
  intro W S hN i j t Λ Λ₀ hΛ hΛ₀ s hs1 hs0
  exact refl_square hFE hφ hL G hb hN.chars hN.roots i j t hΛ hΛ₀ s hs1 hs0

end GlobalTheory.SqTop

end
