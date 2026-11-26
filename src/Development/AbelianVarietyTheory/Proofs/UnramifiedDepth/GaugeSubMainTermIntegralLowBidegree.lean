module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffCoordinatesGoodTangentsLtSq
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffCoordinatesGoodTangentsLtSq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)

noncomputable section

namespace GlobalTheory.MainTerm

theorem sum_pow_trunc_lt_sq {C : Type} [Field C] {I ι : Type} [Fintype I] {l : ℕ} (hl : 2 ≤ l)
    (T : I → MvPowerSeries ι C) (hT : ∀ c, OrdGE 1 (T c)) (f : I → ℕ → C) (μ : ι →₀ ℕ)
    (hμ : μ.degree < l ^ 2) :
    ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ c, f c 0 * MvPowerSeries.coeff μ (T c) + ∑ c, f c 1 * MvPowerSeries.coeff μ (T c ^ l) := by
  have h1 : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ s ∈ Finset.range (μ.degree + 1 + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) := by
    rw [Finset.sum_range_succ _ (μ.degree + 1), Finset.sum_eq_zero (s := Finset.univ), add_zero]
    intro c _
    rw [(hT c).pow _ μ ((Nat.lt_succ_self _).trans (Nat.lt_pow_self (by omega))), mul_zero]
  rw [h1, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, zero_add, add_comm]
  · simp
  · intro s _
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [(hT c).pow _ μ (hμ.trans_le (Nat.pow_le_pow_right (by omega) (by omega))), mul_zero]

theorem ordGE_one_of_constantCoeff {C : Type} [Field C] {ι : Type} {F : MvPowerSeries ι C}
    (h : MvPowerSeries.constantCoeff F = 0) : OrdGE 1 F := by
  intro A hA
  have : A = 0 := (Finsupp.degree_eq_zero_iff A).1 (by omega)
  subst this
  simpa using h

theorem sum_coeff_pow_ite {C : Type} [Field C] {I : Type} [Fintype I] {N : ℕ} (em : Fin N ↪ I)
    (g : I → C) {n : ℕ} (hn : n ≠ 0) (μ : Fin N →₀ ℕ) :
    ∑ c, g c * MvPowerSeries.coeff μ
        ((∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0) ^ n) =
      ∑ δ : Fin N, g (em δ) * MvPowerSeries.coeff μ ((MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ n) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map em)), Finset.sum_map]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    simp
  · intro c _ hc
    have h : ∀ δ, em δ ≠ c := fun δ h => hc (Finset.mem_map.2 ⟨δ, Finset.mem_univ _, h⟩)
    simp [h, hn]

theorem coeff_low_good : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by
  intro C _ V d I J _ _ G S t ht N em hem
  have hl : 2 ≤ V.l := V.l_prime.two_le
  let al : I → ℕ → I → C := fun c k b =>
    if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) (fun δ => S.tan (em δ))
    (fun b j => if em j = b then 1 else 0) al
    (by intro j x; simp)
    (by intro c b; simp [al])
    (by
      intro c k x hk
      have hk' : k ≠ 0 := by omega
      simp only [al, hk', if_false, Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  set T : I → MvPowerSeries (Fin N) C := fun c => linPull (fun δ => S.tan (em δ)) (t c) with hTdef
  set z : I → MvPowerSeries (Fin N) C := fun c =>
    ∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0 with hz
  have hT : ∀ c, OrdGE 1 (T c) := fun c => ordGE_one_of_constantCoeff (h0 c)
  have hz1 : ∀ c, OrdGE 1 (z c) := fun c => by
    refine OrdGE.sum _ fun δ _ => ?_
    split_ifs
    · exact OrdGE.X δ
    · exact OrdGE.zero
  have hal1 : ∀ δ b, al (em δ) 1 b = 0 := fun δ b => by
    have : ∀ x, S.cur (em δ) 1 (Sum.inl x) = 0 := hem δ
    simp [al, Sys.co, this]
  have key : ∀ D, D + 1 ≤ V.l ^ 2 → ∀ c, OrdGE (D + 1) (T c - z c) := by
    intro D
    induction D with
    | zero => exact fun _ c => (hT c).sub (hz1 c)
    | succ D ih =>
      intro hD b A hA
      have e := h1 b A
      have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => al c s b) A (by omega)
      rw [e2] at e
      have e3 : ∀ c, MvPowerSeries.coeff A (T c ^ V.l) = MvPowerSeries.coeff A (z c ^ V.l) := fun c => by
        have := OrdGE.pow_sub_pow (hT c) (hz1 c) (ih (by omega) c) (N := V.l) (by omega) A (by omega)
        rwa [map_sub, sub_eq_zero] at this
      have e4 : ∑ c, al c 1 b * MvPowerSeries.coeff A (T c ^ V.l) = 0 := by
        simp only [e3, hz]
        rw [sum_coeff_pow_ite em (fun c => al c 1 b) (by omega)]
        simp [hal1]
      rw [e4, add_zero] at e
      rw [map_sub, sub_eq_zero]
      have e5 : ∑ c, al c 0 b * MvPowerSeries.coeff A (T c) = MvPowerSeries.coeff A (T b) := by
        simp [al]
      rw [← e5, e]
      congr 1
      refine Finset.sum_congr rfl fun δ _ => ?_
      split_ifs <;> simp
  intro μ hμ
  refine ⟨fun c => ?_, fun κ => ?_⟩
  · have := key μ.degree hμ c μ (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  · have e2 := sum_pow_trunc_lt_sq hl T hT (fun c s => S.be c s κ) μ hμ
    have e3 : ∀ c, MvPowerSeries.coeff μ (T c ^ V.l) = MvPowerSeries.coeff μ (z c ^ V.l) := fun c => by
      have := OrdGE.pow_sub_pow (hT c) (hz1 c) (key μ.degree hμ c) (N := V.l) (by omega) μ (by omega)
      rwa [map_sub, sub_eq_zero] at this
    rw [h2 κ μ, e2]
    simp only [e3, hz]
    rw [sum_coeff_pow_ite em (fun c => S.be c 1 κ) (by omega)]
    simp [Sys.be, S.be_zero]

end GlobalTheory.MainTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffCoordinatesGoodTangentsLtSqStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (em : Fin N ↪ I), (∀ δ x, S.al (em δ) 1 x = 0) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l ^ 2 → (∀ c, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (t c)) = MvPowerSeries.coeff μ (∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0)) ∧ ∀ κ : J, MvPowerSeries.coeff μ (linPull (fun δ => S.tan (em δ)) (S.ze t κ)) = MvPowerSeries.coeff μ (-∑ δ : Fin N, S.be (em δ) 1 κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ V.l) := by
  first | exact @GlobalTheory.MainTerm.coeff_low_good | exact GlobalTheory.MainTerm.coeff_low_good | (intros; apply GlobalTheory.MainTerm.coeff_low_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateIntegralOfDegreeLt
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateIntegralOfDegreeLt
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coord_int_of_degree_lt :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  intro C _ V d I J _ _ G S t ht N e he μ hμ c
  have hz : ∀ b j, V.Ge 0 (S.co (Sum.elim (e j) (0 : J → C)) b) := fun b j =>
    S.co_int (fun n => by
      cases n with
      | inl x => exact he j x
      | inr κ => exact VF.Ge.zero 0) b
  obtain ⟨h0, h1, -⟩ := GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis C V d I J G S t ht (Fin N) e
    (fun b j => S.co (Sum.elim (e j) (0 : J → C)) b)
    (fun c k b => if k = 0 then (if c = b then 1 else 0) else S.co (S.cur c k) b)
    (fun j x => (S.co_spec (Sum.elim (e j) (0 : J → C)) x).symm)
    (fun c b => by simp)
    (fun c k x hk => by
      have hk' : k ≠ 0 := by omega
      simp only [if_neg hk', Sys.al, S.cur_zero_inl]
      exact (S.co_spec (S.cur c k) x).symm)
  have h2 := h1 c μ
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add] at h2
  · simp only [if_true, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum]
    refine VF.Ge.sum fun j _ => ?_
    rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine (hz c j).mul_int ?_
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · intro s _
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [MvPowerSeries.coeff_of_lt_order, mul_zero]
    refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero _ (h0 b))
    have : V.l ≤ V.l ^ (s + 1) := Nat.le_self_pow (Nat.succ_ne_zero s) _
    exact_mod_cast lt_of_lt_of_le hμ this

end GlobalTheory.MainTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateIntegralOfDegreeLtStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (N : ℕ) (e : Fin N → I → C), (∀ j x, V.Ge 0 (e j x)) → ∀ μ : Fin N →₀ ℕ, μ.degree < V.l → ∀ c, V.Ge 0 (MvPowerSeries.coeff μ (linPull e (t c))) := by
  first | exact @GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt | exact GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt | (intros; apply GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffIntegralOnExponentsSubstOfLowerSet
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffIntegralOnExponentsSubstOfLowerSet
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.LowerSubst

open MvPowerSeries

variable {C : Type} [Field C] (V : VF C) {σ : Type} (P : (σ →₀ ℕ) → Prop)

def IntOn (g : MvPowerSeries σ C) : Prop := ∀ μ, P μ → V.Ge 0 (coeff μ g)

theorem intOn_one : IntOn V P (1 : MvPowerSeries σ C) := by
  intro α _
  rw [coeff_one]
  split_ifs with h
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

theorem intOn_mul (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f g : MvPowerSeries σ C}
    (hf : IntOn V P f) (hg : IntOn V P g) : IntOn V P (f * g) := by
  intro α hα
  rw [coeff_mul]
  refine VF.Ge.sum fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  exact VF.Ge.mul_int (hf _ (hP α _ (hx ▸ le_self_add) hα)) (hg _ (hP α _ (hx ▸ le_add_self) hα))

theorem intOn_prod (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ C) (h : ∀ i ∈ s, IntOn V P (f i)) : IntOn V P (∏ i ∈ s, f i) :=
  Finset.prod_induction f (IntOn V P) (fun _ _ => intOn_mul V P hP) (intOn_one V P) h

theorem intOn_pow (hP : ∀ μ ν, ν ≤ μ → P μ → P ν) {f : MvPowerSeries σ C} (hf : IntOn V P f)
    (n : ℕ) : IntOn V P (f ^ n) := by
  induction n with
  | zero => simpa using intOn_one V P
  | succ n ih => rw [pow_succ]; exact intOn_mul V P hP ih hf

theorem subst_int_on_lower :
    ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  intro C _ V σ τ _ _ P hP γ T hγ hT0 hT α hα
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT0
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs γ α)]
  refine VF.Ge.sum fun β _ => ?_
  have hp : IntOn V P (β.prod fun s e => T s ^ e) :=
    intOn_prod V P hP _ _ fun s _ => intOn_pow V P hP (hT s) (β s)
  rw [smul_eq_mul]
  exact VF.Ge.mul_int (hγ β) (hp α hα)

end GlobalTheory.LowerSubst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffIntegralOnExponentsSubstOfLowerSetStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set : ∀ (C : Type) [Field C] (V : VF C) (σ τ : Type) [Fintype σ] [Fintype τ] (P : (σ →₀ ℕ) → Prop), (∀ μ ν, ν ≤ μ → P μ → P ν) → ∀ (γ : MvPowerSeries τ C) (T : τ → MvPowerSeries σ C), (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) → (∀ w, MvPowerSeries.constantCoeff (T w) = 0) → (∀ w μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (T w))) → ∀ μ, P μ → V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.subst T γ)) := by
  first | exact @GlobalTheory.LowerSubst.subst_int_on_lower | exact GlobalTheory.LowerSubst.subst_int_on_lower | (intros; apply GlobalTheory.LowerSubst.subst_int_on_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeSubMainTermIntegralLowBidegree
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

private theorem ge_coeff_rename_inl {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι →₀ ℕ, ν.degree = ∑ c, μ (Sum.inl c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inl F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]

private theorem ge_coeff_rename_inr {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι' C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι' →₀ ℕ, ν.degree = ∑ c, μ (Sum.inr c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inr F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply_of_injective Sum.inr_injective]

private theorem constantCoeff_linPull_eq_zero {C : Type} [Field C] {σ ι : Type} [Fintype σ]
    [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (h : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  unfold linPull
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  · intro x
    simp
  · exact h

private theorem pderiv_inr_mainM_one {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (mainM V 1 Φ) =
      MvPowerSeries.rename Sum.inl ((V.l : C)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X c : MvPowerSeries ι C) ^ V.l) := by
  have hE : expE V.l 1 = 1 := by simp [expE]
  unfold mainM
  rw [hE, pow_one, pow_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, MvPowerSeries.rename_X, map_pow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single b]
  · rw [Derivation.map_smul, Derivation.leibniz, MvPowerSeries.pderiv_X_self, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr]
    simp [mul_comm]
  · intro x _ hx
    rw [Derivation.map_smul, Derivation.leibniz, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr,
      MvPowerSeries.pderiv_X_of_ne (fun h => hx (Sum.inr_injective h))]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem mPlus_of_good_tangents : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  intro C _ V d _ I J _ _ X hAlt hd g a S t hT N em v' hty hal hint hpure μ hμl hμr
  by_cases h0 : ∀ b, μ (Sum.inr b) = 0
  · rw [GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis _ _ _ _ _ X g a 1 _ _ _ v' _ μ h0]
    exact VF.Ge.zero 0
  simp only [not_forall] at h0
  obtain ⟨b, hb⟩ := h0
  have he_pure : ∀ (c : Fin N) (x : I g), (X.G g).ty (Sum.inl x) ≠ a →
      (fun δ => (S g).tan (em δ)) c x = 0 := by
    intro c x hx
    exact tan_pure (S g) (em c) x (by rw [hty c]; exact hx)
  obtain ⟨γ, hγ, hγeq⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hAlt g a 1 odd_one hd S t hT (Fin N) (Fin X.n)
    (fun δ => (S g).tan (em δ)) v' he_pure hint hpure b
  have h91 := GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename C I g (Fin N) (Fin X.n) (fun δ => (S g).tan (em δ)) v'
  have hsingle : Finsupp.single (Sum.inr b) 1 ≤ μ :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hb)
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = μ' + Finsupp.single (Sum.inr b) 1 :=
    ⟨μ - Finsupp.single (Sum.inr b) 1, (tsub_add_cancel_of_le hsingle).symm⟩
  have hl' : ∑ c, μ' (Sum.inl c) < V.l ^ 2 :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμl
  have hr' : ∑ b', μ' (Sum.inr b') < V.l :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμr
  have hbl : μ' (Sum.inr b) + 1 < V.l := by
    refine lt_of_le_of_lt ?_ hμr
    have := Finset.single_le_sum (f := fun b' => (μ' + Finsupp.single (Sum.inr b) 1 : Fin N ⊕ Fin X.n →₀ ℕ) (Sum.inr b'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using this
  have hunit : V.v ((μ' (Sum.inr b) : C) + 1) = 0 := by
    have hc : ((μ' (Sum.inr b) : C) + 1) = ((μ' (Sum.inr b) + 1 : ℕ) : C) := by push_cast; ring
    rw [hc]
    exact ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime V.v V.v_l
      (Nat.coprime_of_lt_prime (by omega) hbl V.l_prime)
  have hne : ((μ' (Sum.inr b) : C) + 1) ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  set Φ : Fin X.n → Fin N → C := fun b c => ∑ κ : J g, ∑ k : I (1 - g),
    -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k with hΦ
  set F := X.hM g a 1 (fun δ => (S g).tan (em δ)) v' - mainM V 1 Φ with hF
  have hcoeff : MvPowerSeries.coeff (μ' + Finsupp.single (Sum.inr b) 1) F =
      ((μ' (Sum.inr b) : C) + 1)⁻¹ * MvPowerSeries.coeff μ' (MvPowerSeries.pderiv (R := C) (Sum.inr b) F) := by
    rw [MvPowerSeries.coeff_pderiv]
    field_simp
  rw [hcoeff]
  refine VF.Ge.mul_int (inv_unit_int hunit) ?_
  set G : MvPowerSeries (Fin N) C :=
    (∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • linPull (fun δ => (S g).tan (em δ)) ((S g).ze (t g) κ)) -
      (V.l : C)⁻¹ • ∑ c : Fin N, Φ b c • (MvPowerSeries.X c : MvPowerSeries (Fin N) C) ^ V.l with hG
  have hsplit : MvPowerSeries.pderiv (R := C) (Sum.inr b) F =
      MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2))
        (fun c => toW g ((fun δ => (S g).tan (em δ)) c)) (fun b => toW (1 - g) (v' b))) γ +
      MvPowerSeries.rename Sum.inl G := by
    rw [hF, map_sub, hγeq, pderiv_inr_mainM_one V Φ b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h91.1, hG, map_sub, map_sum, map_smul]
    abel
  rw [hsplit, map_add (f := _)]
  refine VF.Ge.add ?_ ?_
  · have h2 : ∀ j g : Fin 2, j = g ∨ j = 1 - g := by decide
    refine GlobalTheory.T.coeffIntegralOnExponents_subst_of_lower_set C V (Fin N ⊕ Fin X.n) (WV I)
      (fun ν => ∑ c, ν (Sum.inl c) < V.l ^ 2 ∧ ∑ b', ν (Sum.inr b') < V.l) ?_ γ _ hγ ?_ ?_ μ' ⟨hl', hr'⟩
    · intro ν ν' hle hP
      exact ⟨lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inl c)) hP.1,
        lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inr c)) hP.2⟩
    · rintro ⟨j, x⟩
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT j).1 x)
      · simp only
        rw [h91.2, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT (1 - g)).1 x)
    · rintro ⟨j, x⟩ ν hP
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1]
        apply ge_coeff_rename_inl V
        intro ν' hν'
        set_option synthInstance.maxHeartbeats 100000 in
          rw [(GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I j) (J j) (X.G j) (S j) (t j) (hT j) N em hal ν'
          (by rw [hν']; exact hP.1)).1 x, map_sum]
        apply VF.Ge.sum
        intro δ _
        split_ifs
        · rw [MvPowerSeries.coeff_X]
          split_ifs
          exacts [VF.Ge.one, VF.Ge.zero 0]
        · rw [map_zero]
          exact VF.Ge.zero 0
      · simp only
        rw [h91.2]
        apply ge_coeff_rename_inr V
        intro ν' hν'
        exact GlobalTheory.T.linearSubst_coordinate_integral_of_degree_lt C V d (I (1 - g)) (J (1 - g)) (X.G (1 - g)) (S (1 - g)) (t (1 - g))
          (hT (1 - g)) X.n v' hint ν' (by rw [hν']; exact hP.2) x
  · apply ge_coeff_rename_inl V
    intro ν hν
    have hdeg : ν.degree < V.l ^ 2 := by rw [hν]; exact hl'
    have h19 := (GlobalTheory.T.coeff_coordinates_good_tangents_lt_sq C V d (I g) (J g) (X.G g) (S g) (t g) (hT g) N em hal ν hdeg).2
    have hz : MvPowerSeries.coeff ν G = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hG, map_sub, map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [MvPowerSeries.coeff_smul, h19, map_neg, map_sum, hΦ]
      have hL : (V.l : C) ≠ 0 := VF.l_ne_zero
      rw [sub_eq_zero]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_mul]
      rw [neg_inj, Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [hz]
    exact VF.Ge.zero 0

end GlobalTheory.MainTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeSubMainTermIntegralLowBidegreeStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauge_sub_mainTerm_integral_lowBidegree : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  first | exact @GlobalTheory.MainTerm.mPlus_of_good_tangents | exact GlobalTheory.MainTerm.mPlus_of_good_tangents | (intros; apply GlobalTheory.MainTerm.mPlus_of_good_tangents <;> assumption)
end
