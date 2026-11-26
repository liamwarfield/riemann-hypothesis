module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
noncomputable section

namespace GlobalTheory.NL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace LevPt

open PowerSeries

theorem simple_zero {L : Type} [Field L] (f : PowerSeries L) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f ≠ 0) : ∃ w : PowerSeries L, IsUnit w ∧ f = X * w := by
  obtain ⟨w, rfl⟩ := X_dvd_iff.mpr h0
  refine ⟨w, ?_, rfl⟩
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  simpa using h1

theorem coeff_one_pow_of_deriv {L : Type} [Field L] (U : PowerSeries L)
    (hU : derivative U = U) (m : ℕ) : coeff 1 (U ^ m) = (m : L) * constantCoeff U ^ m := by
  have h : derivative (U ^ m) = (m : PowerSeries L) * U ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, ih, hU]
      push_cast
      simp only [smul_eq_mul]
      ring
  have h2 := congrArg (coeff 0) h
  rw [coeff_derivative] at h2
  simpa using h2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φA_one_add : W.φA (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add (f := _), map_one, W.φA_π]
  funext i
  have := W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, Pi.pow_apply, letπ, LocWach.q]
  linear_combination this

theorem φA_pow_one_add (k : ℕ) : (W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, φA_one_add, map_pow, ih, ← pow_mul, ← pow_succ]

theorem X_eq : W.X = (1 + letπ) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [← φA_pow_one_add W, map_add (f := _), map_one, LocWach.X]
  ring

theorem q_eq : W.q = ∑ k ∈ Finset.range PD.p, (1 + letπ : LetA O n) ^ k := by
  funext i
  have h := W.q₀_def
  have h2 := geom_sum_mul (1 + X : PowerSeries O) PD.p
  have h3 : X * (W.q₀ - ∑ k ∈ Finset.range PD.p, (1 + X : PowerSeries O) ^ k) = 0 := by
    linear_combination h - h2
  have h4 : W.q₀ - ∑ k ∈ Finset.range PD.p, (1 + X : PowerSeries O) ^ k = 0 := by
    ext m
    have := congrArg (coeff (m + 1)) h3
    rw [coeff_succ_X_mul] at this
    simpa using this
  simp only [LocWach.q, Finset.sum_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ]
  exact sub_eq_zero.mp h4

theorem Q_eq : W.Q = ∑ k ∈ Finset.range PD.p, ((1 + letπ : LetA O n) ^ (PD.p ^ (W.s - 1))) ^ k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LocWach.Q, q_eq, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_pow, φA_pow_one_add]

theorem lev_letE (i : ZMod n) (ζ : LL) : W.lev i ζ (letE i) = 1 := by
  have h := W.lev_letter i ζ (1 - letE i) (by simp [letE])
  rw [map_sub, map_one] at h
  exact (sub_eq_zero.mp h).symm

theorem lev_values [CharZero LL] (i : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ letπ = C (ζ - 1) + X * w) ∧
    (ζ ^ (PD.p ^ (W.s - 1)) = 1 → (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.X = X * w) ∧
      IsUnit (W.lev i ζ W.Q)) ∧
    (IsPrimitiveRoot ζ (PD.p ^ W.s) → (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.Q = X * w) ∧
      IsUnit (W.lev i ζ W.X)) ∧
    (constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (PD.p ^ (W.s - 1)) = 1) ∧
    (constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (PD.p ^ W.s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  have hp : PD.p.Prime := PD.hp
  haveI : Fact PD.p.Prime := ⟨hp⟩
  obtain ⟨E, hE0, hE1, hE⟩ := W.lev_π i ζ hζ
  obtain ⟨j, hj⟩ := hζ
  have hζ0 : ζ ≠ 0 := hj.ne_zero (pow_ne_zero _ hp.ne_zero)
  set U : PowerSeries LL := C ζ * E with hUdef
  have hU0 : constantCoeff U = ζ := by simp [hUdef, hE0]
  have hU1 : derivative U = U := by
    rw [hUdef, Derivation.leibniz, hE1, derivative_C]
    simp
  have hlevU : W.lev i ζ (1 + letπ) = U := by rw [map_add (f := _), map_one, hE]
  have hc1 : ∀ m : ℕ, m ≠ 0 → coeff 1 (U ^ m - 1) ≠ 0 := by
    intro m hm
    rw [map_sub, coeff_one_pow_of_deriv U hU1, hU0, coeff_one]
    simp [hm, hζ0]
  have hc0 : ∀ m : ℕ, constantCoeff (U ^ m - 1) = ζ ^ m - 1 := by
    intro m
    simp [hU0]
  obtain ⟨r, hr⟩ : ∃ r, W.s = r + 1 := ⟨W.s - 1, by have := W.s_pos; omega⟩
  have hX : W.lev i ζ W.X = U ^ (PD.p ^ r) - 1 := by
    rw [X_eq, map_sub, map_one, map_pow, hlevU, hr, Nat.add_sub_cancel]
  have hQ : W.lev i ζ W.Q = ∑ k ∈ Finset.range PD.p, (U ^ (PD.p ^ r)) ^ k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Q_eq, map_sum, hr, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, map_pow, hlevU]
  have hXQ : W.lev i ζ W.Q * W.lev i ζ W.X = U ^ (PD.p ^ (r + 1)) - 1 := by
    rw [hX, hQ, geom_sum_mul, ← pow_mul, ← pow_succ]
  have hQ0 : constantCoeff (W.lev i ζ W.Q) = ∑ k ∈ Finset.range PD.p, (ζ ^ (PD.p ^ r)) ^ k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQ, map_sum]
    simp [hU0]
  have hprim : IsPrimitiveRoot ζ (PD.p ^ (r + 1)) ↔
      ζ ^ (PD.p ^ (r + 1)) = 1 ∧ ¬ ζ ^ (PD.p ^ r) = 1 := by
    constructor
    · intro h
      refine ⟨h.pow_eq_one, h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hp.ne_zero) ?_⟩
      exact Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self r)
    · rintro ⟨h1, h2⟩
      rw [← orderOf_eq_prime_pow h2 h1]
      exact IsPrimitiveRoot.orderOf _
  have hQone : ζ ^ (PD.p ^ r) = 1 → constantCoeff (W.lev i ζ W.Q) ≠ 0 := by
    intro h
    rw [hQ0, h]
    simp [hp.ne_zero]
  have hX0 : constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (PD.p ^ r) = 1 := by
    rw [hX, hc0, sub_eq_zero]
  have hQiff : constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (PD.p ^ (r + 1)) := by
    have hc := congrArg constantCoeff hXQ
    rw [map_mul, hc0] at hc
    rw [hprim]
    constructor
    · intro h
      rw [h, zero_mul] at hc
      exact ⟨(sub_eq_zero.mp hc.symm), fun h' => hQone h' h⟩
    · rintro ⟨h1, h2⟩
      rw [h1, sub_self] at hc
      exact (mul_eq_zero.mp hc).resolve_right (fun h => h2 (hX0.mp h))
  rw [hr, Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_, hX0, hQiff, ?_⟩
  · obtain ⟨w, hw, hw'⟩ := simple_zero (U - C ζ) (by simp [hU0]) (by
      have := hc1 1 one_ne_zero
      rw [pow_one, map_sub, coeff_one] at this
      rw [map_sub, coeff_C]
      simpa using this)
    refine ⟨w, hw, ?_⟩
    rw [map_sub, map_one]
    linear_combination hE + hw'
  · intro h
    refine ⟨simple_zero _ (hX0.mpr h) (by rw [hX]; exact hc1 _ (pow_ne_zero _ hp.ne_zero)), ?_⟩
    rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hQone h
  · intro h
    have hXu : IsUnit (W.lev i ζ W.X) := by
      rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
      exact fun h' => (hprim.mp h).2 (hX0.mp h')
    refine ⟨?_, hXu⟩
    obtain ⟨w, hw, hw'⟩ := simple_zero (U ^ (PD.p ^ (r + 1)) - 1)
      (by rw [hc0, h.pow_eq_one, sub_self]) (hc1 _ (pow_ne_zero _ hp.ne_zero))
    obtain ⟨u, hu⟩ := hXu
    refine ⟨w * ↑u⁻¹, hw.mul (Units.isUnit _), ?_⟩
    rw [← mul_assoc, ← hw', ← hXQ, ← hu, Units.mul_inv_cancel_right]
  · intro h
    apply hc1 (PD.p ^ (r + 1)) (pow_ne_zero _ hp.ne_zero)
    rw [← hXQ, h, zero_mul, map_zero]

theorem exists_nonunit {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (ζ : ↥LL.1)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) :
    ∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨j, hj⟩ := hζ
  have hint : IsIntegral ℤ_[l] ζ := (hj.isIntegral (pow_pos hp.pos j)).tower_top
  let x : ↥(OL LL) := ⟨ζ - 1, (OL LL).sub_mem hint (OL LL).one_mem⟩
  refine ⟨x, fun hx => ?_, rfl⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp x 1 j
  have h1 : (x + 1) ^ (l ^ j) = 1 := by
    apply Subtype.ext
    simp [x, hj.pow_eq_one]
  have hl : IsUnit ((l : ℕ) : ↥(OL LL)) := by
    have h2 : IsUnit (x ^ (l ^ j)) := hx.pow _
    refine isUnit_of_dvd_unit ?_ h2
    rw [h1, one_pow] at hr
    exact ⟨-(x * r), by linear_combination -hr⟩
  obtain ⟨y, hy⟩ := hl.exists_right_inv
  have hy' : (l : ↥LL.1) * (y : ↥LL.1) = 1 := by
    have := congrArg (fun z : ↥(OL LL) => (z : ↥LL.1)) hy
    simpa using this
  have hv := congrArg (P.v LL) hy'
  rw [AddValuation.map_mul, P.v_l, AddValuation.map_one] at hv
  have h0 : 0 ≤ P.v LL y := (P.v_O LL y).mpr y.2
  have : (1 : WithTop ℚ) ≤ 1 + P.v LL y := le_add_of_nonneg_right h0
  rw [hv] at this
  exact absurd this (by norm_num)

end LevPt


set_option maxHeartbeats 1000000 in
theorem lev_at_root_of_unity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → (∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 ∧ ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ letπ = PowerSeries.C (x : ↥LL.1) + PowerSeries.X * w) ∧ W.lev i ζ (letE i) = 1 ∧ (ζ ^ (l ^ (s - 1)) = 1 → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.X = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.Q)) ∧ (IsPrimitiveRoot ζ (l ^ s) → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.X)) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (l ^ (s - 1)) = 1) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (l ^ s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  intro D HW l _ K s LL h W i ζ hζ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ j) := by rw [hp]; exact hζ
  obtain ⟨H1, H2⟩ := LevPt.lev_values W i ζ hζ'
  simp only [hp, hs] at H2
  obtain ⟨x, hx, hx'⟩ := LevPt.exists_nonunit (D.loc l) LL ζ hζ
  refine ⟨⟨x, hx, hx', ?_⟩, LevPt.lev_letE W i ζ, H2⟩
  rw [hx']
  exact H1

end GlobalTheory.NL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnityStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLevel_expansion_at_root_of_unity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → (∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 ∧ ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ letπ = PowerSeries.C (x : ↥LL.1) + PowerSeries.X * w) ∧ W.lev i ζ (letE i) = 1 ∧ (ζ ^ (l ^ (s - 1)) = 1 → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.X = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.Q)) ∧ (IsPrimitiveRoot ζ (l ^ s) → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.X)) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (l ^ (s - 1)) = 1) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (l ^ s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  first | exact @GlobalTheory.NL.lev_at_root_of_unity | exact GlobalTheory.NL.lev_at_root_of_unity | (intros; apply GlobalTheory.NL.lev_at_root_of_unity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.Points

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut (F : IntermediateField ℚ_[l] (Om l)) (f : ↥F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : ↥F, g (x : Om l) = f x := by
  refine ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (AlgHom.normal_bijective _ _ _ _), fun x => ?_⟩
  exact f.liftNormal_commutes (Om l) x

theorem exists_restr {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) (hF : F ≤ Ks K s) :
    ∃ τ : ↥F →ₐ[ℚ_[l]] ↥LL.1, ∀ x : ↥F, (τ x : Om l) = g (x : Om l) :=
  ⟨(g.toAlgHom.comp F.val).codRestrict LL.1.toSubalgebra
    (fun x => h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨x, hF x.2⟩), fun _ => rfl⟩

theorem zeta_pow (P : LocPrime l) (m : ℕ) : P.ζQ m ^ l ^ m = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zeta_pow_one (P : LocPrime l) (m : ℕ) : P.ζQ (m + 1) ^ l ^ m = P.ζQ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zeta_prim (P : LocPrime l) (s : ℕ) (hs : 1 ≤ s) : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hnot : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [zeta_pow_one]; exact P.ζQ_one
  rw [← orderOf_eq_prime_pow hnot (zeta_pow P (m + 1))]
  exact IsPrimitiveRoot.orderOf _

theorem zeta_mem (P : LocPrime l) (K : FinExt l) (s : ℕ) : P.ζQ s ∈ Ks K s :=
  (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ (zeta_pow P s))

theorem unramifiedSubfield_le_cyclotomicExt (K : FinExt l) (s : ℕ) : K0 K ≤ Ks K s := le_sup_left

theorem card_emb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (F : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥F] (hF : F ≤ Ks K s) :
    Nat.card (↥F →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥F := by
  have hb : Function.Bijective (fun f : ↥F →ₐ[ℚ_[l]] ↥LL.1 => LL.1.val.comp f) := by
    constructor
    · intro f f' hf
      exact AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hf x)
    · intro f
      obtain ⟨g, hg⟩ := exists_aut F f
      obtain ⟨τ, hτ⟩ := exists_restr h g F hF
      exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (hg x)⟩
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card]
  exact AlgHom.card ℚ_[l] ↥F (Om l)

variable {P : LocPrime l} (H : LocHW l P) {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem pt_of_aut (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : GQ l)
    (h0 : ∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1))
    (hζ : g (P.ζQ s) = ζ) (hτ : ∀ x : ↥K.1, g (x : Om l) = τ x) : Pt H h i ζ τ := by
  obtain ⟨τs, hτs⟩ := exists_restr h g (Ks K s) le_rfl
  refine ⟨τs, ⟨fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩, fun x y hxy => Subtype.ext ?_⟩
  · rw [hτs, hxy, h0]
  · rw [hτs, hy, hζ]
  · rw [hτs, hxy, hτ]

theorem aut_of_pt (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    ∃ g : GQ l, (∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1)) ∧
      g (P.ζQ s) = ζ ∧ ∀ x : ↥K.1, g (x : Om l) = τ x := by
  obtain ⟨τs, ⟨h1, h2⟩, h3⟩ := hp
  obtain ⟨g, hg⟩ := exists_aut (Ks K s) (LL.1.val.comp τs)
  refine ⟨g, fun c => ?_, ?_, fun x => ?_⟩
  · rw [← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]
    exact hg ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩
  · rw [← h2 ⟨_, zeta_mem P K s⟩ rfl]
    exact hg ⟨_, zeta_mem P K s⟩
  · rw [h3 x ⟨x, h.2.2.1 x.2⟩ rfl]
    exact hg ⟨x, h.2.2.1 x.2⟩

theorem exists_pt (i : Let K) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) : ∃ τ, Pt H h i ζ τ := by
  obtain ⟨g₀, hg₀⟩ := exists_aut (K0 K) (LL.1.val.comp ((H.W K s LL h).emb i))
  have h1 : IsPrimitiveRoot (g₀.symm (ζ : Om l)) (l ^ s) :=
    (hζ.map_of_injective (f := LL.1.val) LL.1.val.toRingHom.injective).map_of_injective g₀.symm.injective
  have hconj : IsConjRoot ↥(K0 K) (g₀.symm (ζ : Om l)) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ h1,
      GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ (zeta_prim P s h.1)]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  obtain ⟨τ, hτ⟩ := exists_restr h ((σ.restrictScalars ℚ_[l]).trans g₀) K.1 h.2.2.1
  refine ⟨τ, pt_of_aut H h i ζ τ ((σ.restrictScalars ℚ_[l]).trans g₀) (fun c => ?_) ?_
    (fun x => (hτ x).symm)⟩
  · have : σ (c : Om l) = c := σ.commutes c
    change g₀ (σ (c : Om l)) = _
    rw [this]
    exact hg₀ c
  · change g₀ (σ (P.ζQ s)) = _
    rw [hσ, AlgEquiv.apply_symm_apply]

theorem pt_props (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    IsPrimitiveRoot ζ (l ^ s) ∧
      τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = (H.W K s LL h).emb i ∧
      ∃ ι, Comp H h i ζ τ ι := by
  obtain ⟨g, h0, hζ, hτ⟩ := aut_of_pt H h i ζ τ hp
  refine ⟨?_, ?_, (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp
    (g.symm.toAlgHom.comp LL.1.val), fun c => ?_, ?_, fun c => ?_⟩
  · have h1 := (zeta_prim P s h.1).map_of_injective g.injective
    rw [hζ] at h1
    exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) h1 LL.1.val.toRingHom.injective
  · refine AlgHom.ext fun c => Subtype.ext ?_
    rw [← h0 c]
    exact (hτ _).symm
  · change algebraMap (Om l) P.R.BdR (g.symm (((H.W K s LL h).emb i c : ↥LL.1) : Om l)) = _
    rw [← h0 c, AlgEquiv.symm_apply_apply]
    rfl
  · change algebraMap (Om l) P.R.BdR (g.symm (ζ : Om l)) = _
    rw [← hζ, AlgEquiv.symm_apply_apply]
  · change algebraMap (Om l) P.R.BdR (g.symm ((τ c : ↥LL.1) : Om l)) = _
    rw [← hτ c, AlgEquiv.symm_apply_apply]
    rfl

theorem exists_pt_over (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ∃ (i : Let K) (ζ : ↥LL.1), Pt H h i ζ τ := by
  obtain ⟨g, hg⟩ := exists_aut K.1 (LL.1.val.comp τ)
  obtain ⟨i, hi⟩ := (H.W K s LL h).emb_bij.2 (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  refine ⟨i, ⟨g (P.ζQ s), h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨_, zeta_mem P K s⟩⟩,
    pt_of_aut H h i _ τ g (fun c => ?_) rfl hg⟩
  rw [hi]
  exact hg (algebraMap ↥(K0 K) ↥K.1 c)

theorem points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ τ, Pt (HW l) h i ζ τ) ∧ (∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → IsPrimitiveRoot ζ (l ^ s) ∧ τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i ∧ ∃ ι, Comp (HW l) h i ζ τ ι) ∧ (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ (i : Let K) (ζ : ↥LL.1), Pt (HW l) h i ζ τ) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) := by
  intro D HW l _ K s LL h
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  exact ⟨exists_pt (HW l) h, pt_props (HW l) h, exists_pt_over (HW l) h,
    card_emb h K.1 h.2.2.1, card_emb h (K0 K) (unramifiedSubfield_le_cyclotomicExt K s)⟩

end GlobalTheory.NL.Points
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZero
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem ModTh.abc_Nχ_of_range {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (e : ℤ) (h1 : -1 ≤ e) (h2 : e < Dt.t) :
    ABC (F.D (chr (M.ω ^ (-e)))) Dt.w Dt.wst (M.Nχ e) := by
  refine ⟨fun i => (M.χ_lat e h1 h2 i).1, fun i => ?_, fun i => (M.χ_lat e h1 h2 i).2.1⟩
  have ht : (1 : ℤ) ≤ Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have a := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
  have b := Dt.range i (Dt.w i + Dt.t - 1) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))
  rw [(M.χ_lat e h1 h2 i).2.2.1]
  exact ⟨sh_le_sh_of_le (by omega) _, sh_le_sh_of_le (by unfold TopData.wst; omega) _⟩

theorem ModTh.hom_chr_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  intro k G _ _ l n _ _ _ R F r Dt M T1 T2 T3 e h1 h2 A₁ j p hj hinj hp
  by_contra hne
  have hsurj : Function.Surjective p := by
    obtain ⟨x, hx⟩ : ∃ x, p x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    have hx0 : p x 0 ≠ 0 := fun h => hx (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    intro y
    refine ⟨(y 0 / p x 0) • x, funext fun i => ?_⟩
    rw [Subsingleton.elim i 0, map_smul, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hx0]
  have hT := GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model
  have hsub := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hinj M.std_model
  have hq := ModTh.model_push_of_surjective F M A₁ (chr (M.ω ^ (-e))) p _ hp hsurj hsub
  have hN := GlobalTheory.T.obj_and_abc_of_model F M _ _ hq
  have hχ := M.abc_Nχ_of_range e h1 h2
  have hs : sen ((F.D (chr (M.ω ^ (-e)))).γ 0) (M.Nχ e 0) (e : k) ≠ 0 := by
    rw [(M.χ_lat e h1 h2 0).2.2.2]
    classical
    unfold resCount
    rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro h
    exact h e (Multiset.mem_singleton_self e) (by simp)
  obtain ⟨a, ha, hsa⟩ := GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D (chr (M.ω ^ (-e)))) Dt _ _ hN.2 hχ 0 (e : k) hs
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ (chr (M.ω ^ (-e))) j p Dt.w Dt.wst M.Nstd hT.1 hj hinj hp hsurj hT.2 0
    ((e : k) + a)
  have hstd : resCount (Dt.U 0) (Dt.w 0) ((e : k) + a) ≠ 0 := by
    rw [← M.std_sen]
    omega
  classical
  unfold resCount at hstd
  rw [Ne, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hstd
  push Not at hstd
  obtain ⟨u, hu, hu'⟩ := hstd
  rw [abs_le] at ha
  refine (GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt T1 T2 T3 0).2.1 u hu (Dt.w 0 + e + a) (by omega) (by omega) ?_
  push_cast at hu' ⊢
  linear_combination hu'

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZeroStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_to_characterLine_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  first | exact @GlobalTheory.Models.ModTh.hom_chr_eq_zero | exact GlobalTheory.Models.ModTh.hom_chr_eq_zero | (intros; apply GlobalTheory.Models.ModTh.hom_chr_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResidues
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResidues
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResidues
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_sen_mem : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M A N hN i x hx
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F B A₁ A j p Dt.w Dt.wst Nb (M.base_obj B Nb hB) hj hji hp hps
    (M.base_abc B Nb hB) i x
  obtain ⟨μ, -, hs⟩ := M.base_sen B Nb hB
  rw [hs i x] at hle
  have h0 : resCount (Dt.Ut i) (Dt.w i) x ≠ 0 := by
    intro h
    rw [h] at hle
    apply hx
    simpa using hle
  unfold resCount at h0
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.1 (Nat.pos_of_ne_zero h0)
  classical
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelSenWeightMemWeightResiduesStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_senWeight_mem_weight_residues : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.Ut i, ((u - Dt.w i : ℤ) : k) = x := by
  first | exact @GlobalTheory.Models.model_sen_mem | exact GlobalTheory.Models.model_sen_mem | (intros; apply GlobalTheory.Models.model_sen_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResidues
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem exists_of_resCount_ne_zero_sq {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k}
    (h : resCount U w x ≠ 0) : ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  rw [Ne, Multiset.card_eq_zero] at h
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero h
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem ModTh.sen_model_subquot_mem_U : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A₁ A j p N hj hji hp hps hN i x hx
  have hT := GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model
  have hm1 := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ M.T j M.Nstd hj hji M.std_model
  have hm := ModTh.model_push_of_surjective F M A₁ A p _ hp hps hm1
  have habc0 := (GlobalTheory.T.obj_and_abc_of_model F M A _ hm).2
  have habc := (GlobalTheory.T.obj_and_abc_of_model F M A N hN).2
  obtain ⟨c, hc, hs⟩ := GlobalTheory.T.senWeights_close_of_height_gamma_conditions (F.D A) Dt _ N habc0 habc i x hx
  have hle := GlobalTheory.T.senMultiplicity_subquotient_lattice_le F M.T A₁ A j p Dt.w Dt.wst M.Nstd hT.1 hj hji hp hps hT.2 i (x + c)
  have hs' : sen ((F.D M.T).γ i) (M.Nstd i) (x + c) ≠ 0 := fun h0 => hs (by
    rw [h0] at hle; exact Nat.le_zero.mp hle)
  rw [M.std_sen] at hs'
  obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne_zero_sq hs'
  obtain ⟨u', hu', hux'⟩ := GlobalTheory.T.model_senWeight_mem_weight_residues F M A N hN i x hx
  rcases Multiset.mem_add.mp hu' with hU | hB
  · exact ⟨u', hU, hux'⟩
  · exfalso
    obtain ⟨hb1, hb2⟩ := mem_block.mp hB
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    refine (GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i).2.1 u hu (u' + c) (by omega) (by omega) ?_
    rw [← hux'] at hux
    push_cast at hux ⊢
    linear_combination hux

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResiduesStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senWeight_subquotient_model_mem_residues : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  first | exact @GlobalTheory.Models.ModTh.sen_model_subquot_mem_U | exact GlobalTheory.Models.ModTh.sen_model_subquot_mem_U | (intros; apply GlobalTheory.Models.ModTh.sen_model_subquot_mem_U <;> assumption)
end
end
