module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorShift

variable {K : Type} [Field K] [CharZero K]

theorem iterate_leibniz_ps (D : Derivation K K⟦X⟧ K⟦X⟧) (a b : K⟦X⟧) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : K⟦X⟧) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : K⟦X⟧) = (n.choose ij.1 : K⟦X⟧) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

theorem iterate_derivative_zero (n : ℕ) : (⇑(PowerSeries.derivative (R := K)))^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, map_zero, ih]

def shiftFun (f : K⟦X⟧) : K⟦X⟧⟦X⟧ :=
  PowerSeries.mk fun i => ((i.factorial : K)⁻¹) • (⇑(PowerSeries.derivative (R := K)))^[i] f

theorem coeff_shiftFun (f : K⟦X⟧) (i : ℕ) :
    coeff i (shiftFun f) = ((i.factorial : K)⁻¹) • (⇑(PowerSeries.derivative (R := K)))^[i] f :=
  coeff_mk _ _

theorem iterate_derivative_add (n : ℕ) (f g : K⟦X⟧) :
    (⇑(PowerSeries.derivative (R := K)))^[n] (f + g) =
      (⇑(PowerSeries.derivative (R := K)))^[n] f + (⇑(PowerSeries.derivative (R := K)))^[n] g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_add (f := _), ih]

def shift : K⟦X⟧ →+* K⟦X⟧⟦X⟧ where
  toFun := shiftFun
  map_one' := by
    ext i : 1
    rw [coeff_shiftFun, coeff_one]
    rcases i with _ | i
    · simp
    · rw [Function.iterate_succ_apply, Derivation.map_one_eq_zero, iterate_derivative_zero]
      simp
  map_mul' f g := by
    ext i : 1
    rw [coeff_mul, coeff_shiftFun, iterate_leibniz_ps, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [coeff_shiftFun, coeff_shiftFun]
    subst hij
    have hc : ((ij.1 + ij.2).choose ij.1 : K⟦X⟧) =
        C (((ij.1 + ij.2).factorial : K) / ((ij.1.factorial : K) * (ij.2.factorial : K))) := by
      rw [← Nat.cast_add_choose, map_natCast]
    have h0 : ((ij.1 + ij.2).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : (ij.1.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (ij.2.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : ((ij.1 + ij.2).factorial : K)⁻¹ * (((ij.1 + ij.2).factorial : K) /
        ((ij.1.factorial : K) * (ij.2.factorial : K))) = (ij.1.factorial : K)⁻¹ * (ij.2.factorial : K)⁻¹ := by
      field_simp
    rw [hc, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← map_mul, hk, map_mul]
    ring
  map_zero' := by
    ext i : 1
    rw [coeff_shiftFun, iterate_derivative_zero, smul_zero, map_zero]
  map_add' f g := by
    ext i : 1
    rw [coeff_shiftFun, map_add (f := _), coeff_shiftFun, coeff_shiftFun, iterate_derivative_add, smul_add]

theorem coeff_shift (f : K⟦X⟧) (i : ℕ) :
    coeff i (shift f) = ((i.factorial : K)⁻¹) • (⇑(PowerSeries.derivative (R := K)))^[i] f :=
  coeff_shiftFun f i

theorem shift_C (c : K) : shift (C c) = C (C c : K⟦X⟧) := by
  ext i : 1
  rw [coeff_shift, coeff_C]
  rcases i with _ | i
  · simp
  · rw [Function.iterate_succ_apply, PowerSeries.derivative_C, iterate_derivative_zero]
    simp

theorem shift_X : shift (X : K⟦X⟧) = C (X : K⟦X⟧) + X := by
  ext i : 1
  rw [coeff_shift, map_add (f := _), coeff_C, coeff_X]
  rcases i with _ | _ | i
  · simp
  · simp
  · rw [Function.iterate_succ_apply, PowerSeries.derivative_X, Function.iterate_succ_apply,
      Derivation.map_one_eq_zero, iterate_derivative_zero]
    simp

end GlobalTheory.TaylorShift

namespace GlobalTheory.TaylorShift

section Frob

attribute [-instance] PowerSeries.algebraPowerSeries MvPowerSeries.algebraMvPowerSeries

variable {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime]

def frobW : K⟦X⟧⟦X⟧ := (C (X : K⟦X⟧) + X) ^ l - C ((X : K⟦X⟧) ^ l)

theorem constantCoeff_frobW : constantCoeff (frobW (K := K) l) = 0 := by
  simp [frobW]

def frob2 : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧ :=
  (PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' (constantCoeff_frobW (K := K) l))).toRingHom.comp
    (PowerSeries.map (frob K l).toRingHom)

theorem frobeniusTwoVariablePowerSeries_C (f : K⟦X⟧) : frob2 l (C f) = C (frob K l f) := by
  simp only [frob2, RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have := (PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' (constantCoeff_frobW (K := K) l))).commutes
    (frob K l f)
  exact this

theorem frobeniusTwoVariablePowerSeries_X : frob2 l (X : K⟦X⟧⟦X⟧) = frobW l := by
  simp only [frob2, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact PowerSeries.substAlgHom_X _

end Frob

end GlobalTheory.TaylorShift

namespace GlobalTheory.TaylorShift

section Unique

variable {K : Type} [Field K]

def Small (N : ℕ) (y : K⟦X⟧⟦X⟧) : Prop := ∀ i n, i + n < N → coeff n (coeff i y) = 0

theorem small_mul {a b : ℕ} {y z : K⟦X⟧⟦X⟧} (hy : Small a y) (hz : Small b z) :
    Small (a + b) (y * z) := by
  intro i n h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
  by_cases h1 : p.1 + q.1 < a
  · rw [hy _ _ h1, zero_mul]
  · rw [hz _ _ (by omega), mul_zero]

theorem small_mono {a b : ℕ} {y : K⟦X⟧⟦X⟧} (hy : Small a y) (hab : b ≤ a) : Small b y :=
  fun i n h => hy i n (by omega)

theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable : Small 1 (C (X : K⟦X⟧) + X : K⟦X⟧⟦X⟧) := by
  intro i n h
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ n = 0 := by omega
  simp

theorem small_pow_mul (N : ℕ) (z : K⟦X⟧⟦X⟧) : Small N ((C (X : K⟦X⟧) + X) ^ N * z) := by
  induction N with
  | zero => intro i n h; omega
  | succ N ih =>
    rw [pow_succ', mul_assoc, add_comm N 1]
    exact small_mul twoVariableSeriesVanishesBelowDegree_one_shiftVariable ih

theorem eq_zero_of_small {y : K⟦X⟧⟦X⟧} (h : ∀ N, Small N y) : y = 0 := by
  ext i n
  rw [h (i + n + 1) i n (by omega), map_zero, map_zero]

theorem ringHom_eq_of (α β : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (hC : ∀ c : K, α (C c) = β (C c)) (hX : α X = β X)
    (m : ℕ) (hm : 1 ≤ m) (hs : α X = (C (X : K⟦X⟧) + X) ^ m) : α = β := by
  have hpoly : ∀ p : Polynomial K, α (p : K⟦X⟧) = β (p : K⟦X⟧) := by
    have := Polynomial.ringHom_ext (f := α.comp (Polynomial.coeToPowerSeries.ringHom))
      (g := β.comp (Polynomial.coeToPowerSeries.ringHom)) (fun a => by simpa using hC a) (by simpa using hX)
    intro p
    exact RingHom.congr_fun this p
  ext1 f
  apply sub_eq_zero.mp
  apply eq_zero_of_small
  intro N
  obtain ⟨g, hg⟩ : X ^ N ∣ f - (trunc N f : K⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro k hk
    simp [coeff_trunc, hk]
  have hf : f = (trunc N f : K⟦X⟧) + X ^ N * g := by rw [← hg]; ring
  rw [hf, map_add (f := _), map_add (f := _), hpoly, map_mul, map_mul, map_pow, map_pow, ← hX, hs, add_sub_add_left_eq_sub,
    ← mul_sub, ← pow_mul]
  exact small_mono (small_pow_mul _ _) (Nat.le_mul_of_pos_left N hm)

end Unique

theorem shift_frob_exists : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K],
    ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧),
      (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) ∧
      (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧
      (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  intro l _ K _ _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  refine ⟨shift, frob2 l, fun f i => ?_, frobeniusTwoVariablePowerSeries_C l, fun f => ?_⟩
  · have h0 : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [coeff_shift, smul_eq_C_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ h0, map_one, one_mul]
  · have key : (frob2 l).comp shift = shift.comp (frob K l).toRingHom := by
      refine ringHom_eq_of _ _ (fun c => ?_) ?_ l hl ?_
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, shift_C, frobeniusTwoVariablePowerSeries_C, frob_C]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, shift_X, frob_X, map_pow,
          map_add, frobeniusTwoVariablePowerSeries_C, frobeniusTwoVariablePowerSeries_X, frobW, frob_X]
        ring
      · simp only [RingHom.comp_apply, shift_X, map_add (f := _), frobeniusTwoVariablePowerSeries_C, frobeniusTwoVariablePowerSeries_X, frobW, frob_X]
        ring
    exact RingHom.congr_fun key f

end GlobalTheory.TaylorShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatibleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K], ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) ∧ (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧ (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  first | exact @GlobalTheory.TaylorShift.shift_frob_exists | exact GlobalTheory.TaylorShift.shift_frob_exists | (intros; apply GlobalTheory.TaylorShift.shift_frob_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituent
noncomputable section

namespace GlobalTheory.BlockDensity

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V]

def spanAlg (ρ : Representation K Γ V) : Subalgebra K (Module.End K V) :=
  (Submodule.span K (Set.range ρ)).toSubalgebra (Submodule.subset_span ⟨1, map_one ρ⟩) (by
    intro a b ha hb
    have : Submodule.span K (Set.range ρ) * Submodule.span K (Set.range ρ) ≤
        Submodule.span K (Set.range ρ) := by
      rw [Submodule.span_mul_span]
      apply Submodule.span_mono
      rintro _ ⟨_, ⟨g, rfl⟩, _, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, map_mul ρ g h⟩
    exact this (Submodule.mul_mem_mul ha hb))

private theorem apply_mem_of_mem_span_of_invariant {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (W : Submodule F U)
    (hS : ∀ T ∈ S, ∀ w ∈ W, T w ∈ W) {T : Module.End F U} (hT : T ∈ Submodule.span F S) :
    ∀ w ∈ W, T w ∈ W := by
  induction hT using Submodule.span_induction with
  | mem T h => exact hS T h
  | zero => intro w _; simp
  | add T T' _ _ h h' => intro w hw; simpa using W.add_mem (h w hw) (h' w hw)
  | smul c T _ h => intro w hw; simpa using W.smul_mem c (h w hw)

theorem _root_.GlobalTheory.BlockDensity.stable_span (ρ : Representation K Γ V) (W : Submodule K V)
    (hs : _root_.Formalism.MainNotions.N.Stable ρ W) :
    ∀ t ∈ Submodule.span K (Set.range ρ), ∀ v ∈ W, t v ∈ W := by
  intro t ht
  refine apply_mem_of_mem_span_of_invariant (Set.range ρ) W ?_ ht
  rintro _ ⟨g, rfl⟩
  exact hs g

def toSub (ρ : Representation K Γ V) (W : Submodule K V) (hs : Stable ρ W) : Submodule (spanAlg ρ) V where
  carrier := W
  add_mem' := W.add_mem
  zero_mem' := W.zero_mem
  smul_mem' := fun c _ hv => stable_span ρ W hs c.1 c.2 _ hv

private theorem exists_end_apply_eq_of_ne_zero {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] {w : U} (hw : w ≠ 0) (u : U) : ∃ T : Module.End F U, T w = u := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual F U, φ w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw ((Module.forall_dual_apply_eq_zero_iff F w).mp h)
  exact ⟨(φ w)⁻¹ • φ.smulRight u, by simp [smul_smul, inv_mul_cancel₀ hφ]⟩

private theorem invariant_trivial_of_span_endomorphisms_full {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (hS : Submodule.span F S = ⊤) (W : Submodule F U)
    (hW : ∀ T ∈ S, ∀ w ∈ W, T w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  rcases eq_or_ne W ⊥ with h | h
  · exact Or.inl h
  right
  obtain ⟨w, hwW, hw⟩ := (Submodule.ne_bot_iff W).mp h
  rw [Submodule.eq_top_iff']
  intro u
  obtain ⟨T, rfl⟩ := exists_end_apply_eq_of_ne_zero (F := F) hw u
  exact apply_mem_of_mem_span_of_invariant S W hW (by rw [hS]; exact Submodule.mem_top) w hwW

private theorem commute_of_mem_span_of_forall_commute {F U : Type} [Field F] [AddCommGroup U]
    [Module F U] (S : Set (Module.End F U)) (ψ : Module.End F U)
    (hS : ∀ T ∈ S, T * ψ = ψ * T) {T : Module.End F U} (hT : T ∈ Submodule.span F S) :
    T * ψ = ψ * T := by
  induction hT using Submodule.span_induction with
  | mem T h => exact hS T h
  | zero => simp
  | add T T' _ _ h h' => rw [add_mul, mul_add, h, h']
  | smul c T _ h => rw [smul_mul_assoc, mul_smul_comm, h]

theorem _root_.GlobalTheory.BlockDensity.density : ∀ {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K Γ V) (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K V)
    (hs : ∀ j, _root_.Formalism.MainNotions.N.Stable ρ (Vs j)), DirectSum.IsInternal Vs →
    (∀ j, Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) →
    (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[K] Vs j',
      ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v)) →
    ∀ f : V →ₗ[K] V, (∀ j, ∀ v ∈ Vs j, f v ∈ Vs j) → f ∈ Submodule.span K (Set.range ρ) := by
  intro K Γ V _ _ _ _ _ ρ ι _ _ Vs hs hint hfull hdistinct f hf
  let p : ∀ k, V →ₗ[K] Vs k := fun k => (DirectSum.component K ι (fun i => Vs i) k).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap Vs) hint).symm.toLinearMap
  have hp_self : ∀ i (y : V) (hy : y ∈ Vs i), p i y = ⟨y, hy⟩ := fun i y hy =>
    hint.ofBijective_coeLinearMap_of_mem hy
  have hp_ne : ∀ i k, i ≠ k → ∀ y ∈ Vs i, p k y = 0 := fun i k hik y hy =>
    hint.ofBijective_coeLinearMap_of_mem_ne hik hy
  have htop : ∀ y : V, y ∈ ⨆ i, Vs i := fun y => by
    rw [hint.submodule_iSup_eq_top]; exact Submodule.mem_top
  have hsum : ∀ y : V, ∑ k, (p k y : V) = y := by
    intro y
    refine Submodule.iSup_induction Vs (motive := fun y => ∑ k, (p k y : V) = y) (htop y)
      ?_ (by simp) ?_
    · intro i y hy
      rw [Finset.sum_eq_single i]
      · rw [hp_self i y hy]
      · intro k _ hk
        rw [hp_ne i k (Ne.symm hk) y hy]
        rfl
      · simp
    · intro x y hx hy
      simp only [map_add (f := _), Submodule.coe_add, Finset.sum_add_distrib, hx, hy]
  have hp_rho : ∀ k g y, p k (ρ g y) = (ρ g).restrict (hs k g) (p k y) := by
    intro k g y
    refine Submodule.iSup_induction Vs
      (motive := fun y => p k (ρ g y) = (ρ g).restrict (hs k g) (p k y)) (htop y) ?_ (by simp) ?_
    · intro i y hy
      by_cases hik : i = k
      · subst hik
        rw [hp_self i _ (hs i g y hy), hp_self i y hy]
        rfl
      · rw [hp_ne i k hik _ (hs i g y hy), hp_ne i k hik y hy, map_zero]
    · intro x y hx hy
      simp only [map_add (f := _), hx, hy]
  have hcomm : ∀ φ : Module.End (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V, ∀ v, f (φ v) = φ (f v) := by
    intro φ
    have hφρ : ∀ g v, φ (ρ g v) = ρ g (φ v) := fun g v =>
      φ.map_smul (⟨ρ g, Submodule.subset_span ⟨g, rfl⟩⟩ : _root_.GlobalTheory.BlockDensity.spanAlg ρ) v
    let ψ : ∀ j k, Vs j →ₗ[K] Vs k := fun j k =>
      (p k).comp ((φ.restrictScalars K).comp (Vs j).subtype)
    have hψ : ∀ j k g x, ψ j k ((ρ g).restrict (hs j g) x) = (ρ g).restrict (hs k g) (ψ j k x) := by
      intro j k g x
      show p k (φ (ρ g x)) = _
      rw [hφρ, hp_rho]
      rfl
    have hzero : ∀ j k, j ≠ k → ψ j k = 0 := by
      intro j k hjk
      by_contra hne
      have hker := invariant_trivial_of_span_endomorphisms_full _ (hfull j) (LinearMap.ker (ψ j k)) (by
        rintro _ ⟨g, rfl⟩ w hw
        rw [LinearMap.mem_ker] at hw ⊢
        rw [hψ, hw, map_zero])
      have hran := invariant_trivial_of_span_endomorphisms_full _ (hfull k) (LinearMap.range (ψ j k)) (by
        rintro _ ⟨g, rfl⟩ _ ⟨x, rfl⟩
        exact ⟨(ρ g).restrict (hs j g) x, hψ j k g x⟩)
      rcases hker with hker | hker
      · rcases hran with hran | hran
        · exact hne (LinearMap.range_eq_bot.mp hran)
        · exact hdistinct j k hjk (LinearEquiv.ofBijective (ψ j k)
            ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hran⟩) fun g v => hψ j k g v
      · exact hne (LinearMap.ker_eq_top.mp hker)
    have hφv : ∀ j v (hv : v ∈ Vs j), φ v = (ψ j j ⟨v, hv⟩ : V) := by
      intro j v hv
      rw [← hsum (φ v), Finset.sum_eq_single j]
      · rfl
      · intro k _ hkj
        show ((ψ j k ⟨v, hv⟩ : Vs k) : V) = 0
        rw [hzero j k (Ne.symm hkj)]
        rfl
      · simp
    have hcj : ∀ j, f.restrict (hf j) * ψ j j = ψ j j * f.restrict (hf j) := by
      intro j
      refine commute_of_mem_span_of_forall_commute _ (ψ j j) ?_ (by rw [hfull j]; exact Submodule.mem_top)
      rintro _ ⟨g, rfl⟩
      ext x
      exact congrArg Subtype.val (hψ j j g x).symm
    intro v
    refine Submodule.iSup_induction Vs (motive := fun v => f (φ v) = φ (f v)) (htop v) ?_
      (by simp) ?_
    · intro j v hv
      rw [hφv j v hv, hφv j (f v) (hf j v hv)]
      exact congrArg Subtype.val (LinearMap.congr_fun (hcj j) ⟨v, hv⟩)
    · intro x y hx hy
      simp only [map_add (f := _), hx, hy]
  have hlift : ∀ j (E : Module.End K (Vs j)), ∃ a ∈ Submodule.span K (Set.range ρ),
      ∀ x : Vs j, a x = E x := by
    intro j E
    have hE : E ∈ Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) := by
      rw [hfull j]; exact Submodule.mem_top
    induction hE using Submodule.span_induction with
    | mem E h =>
      obtain ⟨g, rfl⟩ := h
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, fun x => rfl⟩
    | zero => exact ⟨0, zero_mem _, fun x => by simp⟩
    | add E E' _ _ h h' =>
      obtain ⟨a, ha, hax⟩ := h
      obtain ⟨b, hb, hbx⟩ := h'
      exact ⟨a + b, add_mem ha hb, fun x => by simp [hax, hbx]⟩
    | smul c E _ h =>
      obtain ⟨a, ha, hax⟩ := h
      exact ⟨c • a, Submodule.smul_mem _ c ha, fun x => by simp [hax]⟩
  haveI : IsSemisimpleModule (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V := by
    rw [← sSup_simples_eq_top_iff_isSemisimpleModule, eq_top_iff]
    intro v _
    refine Submodule.iSup_induction Vs (motive := fun v => v ∈ sSup {m : Submodule
      (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V | IsSimpleModule (_root_.GlobalTheory.BlockDensity.spanAlg ρ) m})
      (htop v) ?_ (zero_mem _) (fun _ _ => add_mem)
    intro j v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · exact zero_mem _
    have hvT : v ∈ _root_.GlobalTheory.BlockDensity.toSub ρ (Vs j) (hs j) := hv
    refine Submodule.mem_sSup_of_mem ?_ hvT
    rw [Set.mem_setOf_eq, isSimpleModule_iff_isAtom]
    refine ⟨fun h => hv0 ((Submodule.mem_bot _).mp (h ▸ hvT)), fun N hN => ?_⟩
    by_contra hN0
    obtain ⟨w, hwN, hw0⟩ := (Submodule.ne_bot_iff N).mp hN0
    apply hN.2
    intro u hu
    have hwj : w ∈ Vs j := hN.le hwN
    obtain ⟨E, hE⟩ := exists_end_apply_eq_of_ne_zero (F := K)
      (show (⟨w, hwj⟩ : Vs j) ≠ 0 from fun h => hw0 (congrArg Subtype.val h)) (⟨u, hu⟩ : Vs j)
    obtain ⟨a, ha, hax⟩ := hlift j E
    have hu' : u = (⟨a, ha⟩ : _root_.GlobalTheory.BlockDensity.spanAlg ρ) • w := by
      show u = a w
      rw [hax ⟨w, hwj⟩, hE]
    rw [hu']
    exact N.smul_mem _ hwN
  let f' : Module.End (Module.End (_root_.GlobalTheory.BlockDensity.spanAlg ρ) V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => hcomm φ v }
  classical
  obtain ⟨r, hr⟩ := jacobson_density f' (Finset.univ.image (Module.finBasis K V))
  have hfr : f = (r : Module.End K V) := (Module.finBasis K V).ext fun i =>
    hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [hfr]
  exact r.2

end GlobalTheory.BlockDensity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepresentationDensityOfIsInternalConstituentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_representation_density_of_isInternal_constituents : ∀ {K Γ V : Type} [Field K] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V) (ι : Type) [Fintype ι] [DecidableEq ι] (Vs : ι → Submodule K V) (hs : ∀ j, Stable ρ (Vs j)), DirectSum.IsInternal Vs → (∀ j, Submodule.span K (Set.range fun g => (ρ g).restrict (hs j g)) = ⊤) → (∀ j j', j ≠ j' → ∀ e : Vs j ≃ₗ[K] Vs j', ¬ ∀ g v, e ((ρ g).restrict (hs j g) v) = (ρ g).restrict (hs j' g) (e v)) → ∀ f : V →ₗ[K] V, (∀ j, ∀ v ∈ Vs j, f v ∈ Vs j) → f ∈ Submodule.span K (Set.range ρ) := by
  first | exact @GlobalTheory.BlockDensity.density | exact GlobalTheory.BlockDensity.density | (intros; apply GlobalTheory.BlockDensity.density <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_eq_l_mul_of_natCast {A : Type} [CommRing A] (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    {m k : ℕ} (hm : m ≠ 0) (hv : padicValNat l m < padicValNat l k) {y z : A}
    (h : (m : A) * y = (k : A) * z) : ∃ w, y = l * w := by
  have hp := hl.out
  have hk : k ≠ 0 := by
    rintro rfl
    simp [Nat.padicValNat_def] at hv
  have htf' : ∀ (j : ℕ) (x : A), (l : A) ^ j * x = 0 → x = 0 := fun j => by
    induction j with
    | zero => simp
    | succ j ih => exact fun x hx => htf x (ih _ (by linear_combination hx))
  rw [Nat.padicValNat_def, Nat.padicValNat_def, ← Nat.factorization_def m hp, ← Nat.factorization_def k hp] at hv
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m l
  have hk' := Nat.ordProj_mul_ordCompl_eq_self k l
  have hcop := Nat.coprime_ordCompl hp hm
  generalize m / l ^ m.factorization l = m' at hm' hcop
  generalize k / l ^ k.factorization l = k' at hk'
  generalize m.factorization l = a at hm' hv
  generalize k.factorization l = b at hk' hv
  subst hm' hk'
  push_cast at h
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have huv' : (u : A) * l + (v : A) * m' = 1 := by
    have := congrArg (Int.cast : ℤ → A) huv
    push_cast at this
    exact this
  have e : (l : A) ^ b = (l : A) ^ a * ((l : A) ^ (b - a - 1) * l) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have h1 : (m' : A) * y = (l : A) ^ (b - a - 1) * l * k' * z := by
    apply sub_eq_zero.1
    apply htf' a
    rw [e] at h
    linear_combination h
  exact ⟨u * y + v * (l : A) ^ (b - a - 1) * k' * z, by linear_combination (-y) * huv' + (v : A) * h1⟩

theorem cong_add {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a + b) = (a + b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out a b
  exact ⟨w + w' - a * b * r, by rw [map_add (f := _), hw, hw', hr]; ring⟩

theorem cong_mul {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a * b) = (a * b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  exact ⟨a ^ l * w' + w * b ^ l + (l : A) * w * w', by rw [map_mul, hw, hw']; ring⟩

theorem frobC_ainfToAcris (b : Ainf l) :
    frobC l (ainfToAcris l b) = ainfToAcris l (WittVector.frobenius b) := by
  rw [← GlobalTheory.RingBasics.φA_apply]
  exact (GlobalTheory.CrisMaps.phiA_extends l).alg b

theorem cong_ainf (b : Ainf l) :
    ∃ w, frobC l (ainfToAcris l b) = ainfToAcris l b ^ l + (l : Per.Acris l) * w := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add b
  exact ⟨ainfToAcris l c, by rw [frobC_ainfToAcris, hc, map_add (f := _), map_pow, map_mul, map_natCast]⟩

theorem frob_mem_of_theta {x : Ainf l} (hx : Per.θ l x = 0) :
    ∃ u, ainfToAcris l (WittVector.frobenius x) = (l : Per.Acris l) * u := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add x
  obtain ⟨d, hd⟩ := exists_dpow hx l
  have hf : (l.factorial : Per.Acris l) = (l : Per.Acris l) * ((l - 1).factorial : Per.Acris l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hl.out.ne_zero]
  refine ⟨((l - 1).factorial : Per.Acris l) * d + ainfToAcris l c, ?_⟩
  rw [hc, map_add (f := _), map_pow, ← hd, map_mul, map_natCast, hf]
  ring

theorem padicValNat_factorial_bound {n : ℕ} (hn : n ≠ 0) :
    l * padicValNat l n.factorial < padicValNat l n.factorial + n := by
  rw [Nat.padicValNat_def]
  have h := hl.out.sub_one_mul_multiplicity_factorial (n := n)
  have hlast := Nat.getLast_digit_ne_zero l hn
  have hpos : 0 < (l.digits n).sum :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hlast) (List.le_sum_of_mem (List.getLast_mem _))
  have h2 : 2 ≤ l := hl.out.two_le
  generalize multiplicity l n.factorial = v at h ⊢
  generalize (l.digits n).sum = s at h hpos
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have e : (k + 1) * v = k * v + v := by ring
  rw [e]
  generalize k * v = t at h ⊢
  omega

theorem cong_gen {x : Ainf l} (hx : Per.θ l x = 0) {n : ℕ} {Y : Per.Acris l}
    (hY : (n.factorial : Per.Acris l) * Y = ainfToAcris l x ^ n) :
    ∃ w, frobC l Y = Y ^ l + (l : Per.Acris l) * w := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Y = 1 := by simpa using hY
    exact ⟨0, by rw [this]; simp⟩
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  obtain ⟨w1, hw1⟩ : ∃ w, frobC l Y = (l : Per.Acris l) * w := by
    have h1 := congrArg (frobC l) hY
    rw [map_mul, map_natCast, map_pow, frobC_ainfToAcris, hu, mul_pow] at h1
    refine exists_eq_l_mul_of_natCast htf (Nat.factorial_ne_zero n) (k := l ^ n) (z := u ^ n) ?_ ?_
    · simp only [Nat.padicValNat_def]
      rw [Nat.multiplicity_prime_pow]
      exact multiplicity_factorial_lt_of_ne_zero l hn.ne'
    · rw [h1]; push_cast; rfl
  obtain ⟨w2, hw2⟩ : ∃ w, Y ^ l = (l : Per.Acris l) * w := by
    obtain ⟨d, hd⟩ := exists_dpow hx (l * n)
    have h2 : ((n.factorial ^ l : ℕ) : Per.Acris l) * Y ^ l = ((l * n).factorial : ℕ) * d := by
      rw [hd, Nat.cast_pow, ← mul_pow, hY, ← pow_mul, mul_comm n l]
    refine exists_eq_l_mul_of_natCast htf (pow_ne_zero _ (Nat.factorial_ne_zero n)) ?_ h2
    simp only [Nat.padicValNat_def]
    rw [Nat.multiplicity_pow n.factorial l, multiplicity_factorial_mul]
    simpa only [Nat.padicValNat_def] using (padicValNat_factorial_bound (l := l) hn.ne')
  exact ⟨w1 - w2, by rw [hw1, hw2]; ring⟩

theorem cong_acris0 : ∀ (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l),
    ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) =
      (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) ^ l + (l : Per.Acris l) * w := by
  intro s hs
  let S : Subalgebra (Per.Ainf l) (Per.Acris0 l) :=
    { carrier := {t | ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) t) =
        (algebraMap (Per.Acris0 l) (Per.Acris l) t) ^ l + (l : Per.Acris l) * w}
      mul_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) ^ l + (l : Per.Acris l) * w
        rw [map_mul]
        exact cong_mul (frobC l).toRingHom hx hy
      add_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) ^ l + (l : Per.Acris l) * w
        have he : algebraMap (Per.Acris0 l) (Per.Acris l) (x + y) =
            algebraMap (Per.Acris0 l) (Per.Acris l) x + algebraMap (Per.Acris0 l) (Per.Acris l) y :=
          (algebraMap (Per.Acris0 l) (Per.Acris l)).map_add x y
        rw [he]
        exact cong_add (frobC l).toRingHom hx hy
      algebraMap_mem' := fun r => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) ^ l +
            (l : Per.Acris l) * w
        rw [← GlobalTheory.RingIface.tower]
        exact cong_ainf r }
  have hle : Per.Acris0 l ≤ S.map (Per.Acris0 l).val := by
    refine GlobalTheory.RingIface.acris0_le_3 l _ fun x hx n y hy hn => ?_
    refine Subalgebra.mem_map.2 ⟨⟨y, hy⟩, ?_, rfl⟩
    refine cong_gen hx (n := n) ?_
    have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * ⟨y, hy⟩ =
        algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
    rw [map_mul, map_natCast, map_pow, ← GlobalTheory.RingIface.tower] at h2
    exact h2
  obtain ⟨t, ht, e⟩ := Subalgebra.mem_map.1 (hle hs)
  have e' : (⟨s, hs⟩ : Per.Acris0 l) = t := Subtype.ext e.symm
  rw [e']
  exact ht

theorem frobC_cong (y : Per.Acris l) : ∃ w, frobC l y = y ^ l + (l : Per.Acris l) * w := by
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 y 1
  obtain ⟨w, hw⟩ := cong_acris0 s.1 s.2
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ 1 * z)
    (algebraMap (Per.Acris0 l) (Per.Acris l) s) l
  refine ⟨w + frobC l z - z * c, ?_⟩
  rw [map_add (f := _), map_mul, map_pow, map_natCast, hw]
  linear_combination -hc

end GlobalTheory.AcrisPrism

namespace GlobalTheory.AcrisPrism

variable (l : ℕ) [hl : Fact l.Prime]

def acrisDelta : Delta l (Per.Acris l) :=
  Delta.ofLift l (frobC l).toRingHom (GlobalTheory.MemLoc.acris_basic l).2.1 fun a => frobC_cong a

theorem isUnit_delta_l : IsUnit ((acrisDelta l).δ (l : Per.Acris l)) := by
  have h := (acrisDelta l).φ_eq (l : Per.Acris l)
  have h1 : (acrisDelta l).φ (l : Per.Acris l) = l := map_natCast _ _
  rw [h1] at h
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  have e : (l : Per.Acris l) ^ l = (l : Per.Acris l) ^ 2 * (l : Per.Acris l) ^ (l - 2) := by
    rw [← pow_add]
    congr 1
    have := hl.out.two_le
    omega
  have h2 : (acrisDelta l).δ (l : Per.Acris l) = (l : Per.Acris l) * (-(l : Per.Acris l) ^ (l - 2)) + 1 := by
    apply sub_eq_zero.1
    apply htf
    linear_combination -h - e
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  rw [h2]
  exact Ideal.mem_jacobson_bot.1
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self (l : Per.Acris l))) _

theorem l_mem_nonZeroDivisors : (l : Per.Acris l) ∈ nonZeroDivisors (Per.Acris l) := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  exact mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm, hx])⟩

def ainfPhiToAcris : Ainf l →+* Per.Acris l := (ainfToAcris l).toRingHom.comp WittVector.frobenius

theorem ainfPhiToAcris_le (F : FinExt l) :
    (ainfObj F).I ≤ (Ideal.span {(l : Per.Acris l)}).comap (ainfPhiToAcris l) := by
  intro a ha
  have hx : Per.θ l a = 0 := RingHom.mem_ker.1 ha
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  exact Ideal.mem_span_singleton'.2 ⟨u, by rw [mul_comm]; exact hu.symm⟩

def acrisObj (F : FinExt l) : Obj l ↥(OL F) :=
  Obj.ofDistinguished hl.out.pos (acrisDelta l) (l : Per.Acris l) (l_mem_nonZeroDivisors l)
    (isUnit_delta_l l) (by rw [sup_idem]; exact (GlobalTheory.MemLoc.acris_basic l).1)
    ⟨1, fun x _ => by
      have : ((l : ℕ) : Per.Acris l ⧸ Ideal.span {(l : Per.Acris l)}) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      simp [this]⟩
    ((Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l) (ainfPhiToAcris_le l F)).comp
      (ainfObj F).str)

def acrisHom (F : FinExt l) : Hom (ainfObj F) (acrisObj l F) where
  f := ainfPhiToAcris l
  f_δ := Delta.map_δ_of_map_φ (ainfObj F).D (acrisDelta l) (GlobalTheory.MemLoc.acris_basic l).2.1 _
    fun a => (frobC_ainfToAcris (WittVector.frobenius a)).symm
  f_I := fun a ha => ainfPhiToAcris_le l F ha
  f_str := fun r a h => by
    change Ideal.Quotient.mk _ (ainfPhiToAcris l a) =
      Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l)
        (ainfPhiToAcris_le l F) ((ainfObj F).str r)
    rw [← h]
    rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ (C : Obj l ↥(OL F)) (eC : C.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj F) C), C.I = Ideal.span {(l : C.A)} ∧ (∀ x, eC (C.D.φ x) = frobC l (eC x)) ∧ ∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x) :=
  fun l _ F => ⟨acrisObj l F, RingEquiv.refl _, acrisHom l F, rfl, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.AcrisPrism
end
end
