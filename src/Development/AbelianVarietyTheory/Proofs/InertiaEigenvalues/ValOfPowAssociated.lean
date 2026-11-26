module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeAndInvariantsGen
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueSum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc

namespace ParamRing

variable {R : Type} [CommRing R] {σ : R⟦X⟧ →ₐ[R] R⟦X⟧} {w : R⟦X⟧} {s : ℕ}

theorem X_pow_dvd_map (h : σ X = w * X ^ s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    X ^ (s * j) ∣ σ G := by
  obtain ⟨H, rfl⟩ := hG
  exact ⟨w ^ j * σ H, by rw [map_mul, map_pow, h, pow_mul]; ring⟩

theorem coeff_map_lead (h : σ X = w * X ^ s) (hs : 0 < s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    coeff (s * j) (σ G) = constantCoeff w ^ j * coeff j G := by
  obtain ⟨H, rfl⟩ := hG
  have h0 : constantCoeff (σ H) = constantCoeff H := by
    conv_lhs => rw [eq_X_mul_shift_add_const H]
    rw [map_add (f := _), map_mul, h, show σ (C (constantCoeff H)) = C (constantCoeff H) from σ.commutes _]
    simp [hs.ne']
  have h1 : σ (X ^ j * H) = X ^ (s * j) * (w ^ j * σ H) := by
    rw [map_mul, map_pow, h, pow_mul]; ring
  have h2 := coeff_X_pow_mul (w ^ j * σ H) (s * j) 0
  have h3 := coeff_X_pow_mul H j 0
  rw [zero_add] at h2 h3
  rw [h1, h2, h3]
  simp [h0]

theorem lead_sum (h : σ X = w * X ^ s) (hs : 0 < s) (G : Fin s → R⟦X⟧) (n : ℕ)
    (hG : ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0) :
    X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) ∧
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) =
        constantCoeff w ^ (n / s) * coeff (n / s) (G ⟨n % s, Nat.mod_lt _ hs⟩) := by
  have hn := Nat.mod_add_div n s
  have key : ∀ k : Fin s, (k : ℕ) ≠ n % s → X ^ (n + 1) ∣ X ^ (k : ℕ) * σ (G k) := by
    intro k hk
    have hk' := k.2
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h1 : X ^ (n / s + 1) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.lt_succ_iff.1 hm)
        omega)
      refine (pow_dvd_pow X ?_).trans ((X_pow_dvd_map h h1).mul_left _)
      have := Nat.mod_lt n hs
      rw [mul_add]; omega
    · have h1 : X ^ (n / s) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm)
        rw [Nat.mul_succ] at this
        omega)
      refine (pow_dvd_pow X (show n + 1 ≤ k + s * (n / s) by omega)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
  have h1 : X ^ (n / s) ∣ G ⟨n % s, Nat.mod_lt _ hs⟩ := X_pow_dvd_iff.2 fun m hm => hG _ m (by
    have := Nat.mul_lt_mul_of_pos_left hm hs
    simp only
    omega)
  constructor
  · refine Finset.dvd_sum fun k _ => ?_
    by_cases hk : (k : ℕ) = n % s
    · obtain rfl : k = ⟨n % s, Nat.mod_lt _ hs⟩ := Fin.ext hk
      conv_lhs => rw [← hn, pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
    · exact (pow_dvd_pow X n.le_succ).trans (key k hk)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single ⟨n % s, Nat.mod_lt _ hs⟩]
    · rw [← coeff_map_lead h hs h1, ← coeff_X_pow_mul (σ _) (n % s) (s * (n / s)), add_comm, hn]
    · intro k _ hk
      exact X_pow_dvd_iff.1 (key k fun e => hk (Fin.ext e)) n n.lt_succ_self
    · simp

theorem eq_zero_of_lead (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (G : Fin s → R⟦X⟧)
    (hG : ∀ n, X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) →
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) = 0 ∨ G ⟨n % s, Nat.mod_lt _ hs⟩ = 0) : G = 0 := by
  have key : ∀ n, ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0 := by
    intro n
    induction n with
    | zero => intro k j hj; omega
    | succ n ih =>
      intro k j hj
      rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | hj
      · exact ih k j hj
      obtain ⟨h1, h2⟩ := lead_sum h hs G n ih
      have e1 : n % s = k := by rw [← hj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]
      have e2 : n / s = j := by rw [← hj, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt k.2, zero_add]
      have e3 : (⟨n % s, Nat.mod_lt _ hs⟩ : Fin s) = k := Fin.ext e1
      have h3 := hG n h1
      rw [h2, e3, e2] at h3
      rcases h3 with h3 | h3
      · exact ((hw.map constantCoeff).pow j).mul_right_eq_zero.1 h3
      · rw [h3, map_zero]
  ext k j
  exact key _ k j (Nat.lt_succ_self _)

theorem exists_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃ G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  let T : R⟦X⟧ → R⟦X⟧ := fun b => v * mk fun i => coeff (i + s) b
  let G : R⟦X⟧ → Fin s → R⟦X⟧ := fun b k => mk fun j => coeff k (T^[j] b)
  have hT : ∀ b : R⟦X⟧, b = σ X * T b + ∑ k : Fin s, X ^ (k : ℕ) * C (coeff k b) := by
    intro b
    have h1 : σ X * T b = X ^ s * mk fun i => coeff (i + s) b := by
      simp only [h, T]
      linear_combination (X ^ s * mk fun i => coeff (i + s) b) * hv
    rw [h1]
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), coeff_X_pow_mul', map_sum]
    simp only [coeff_mul_C, coeff_X_pow, coeff_mk]
    split_ifs with hn
    · rw [Nat.sub_add_cancel hn, Finset.sum_eq_zero, add_zero]
      intro k _
      have := k.2
      rw [if_neg (by omega), zero_mul]
    · rw [zero_add, Finset.sum_eq_single ⟨n, by omega⟩]
      · simp
      · intro k _ hk
        rw [if_neg (fun e => hk (Fin.ext e.symm)), zero_mul]
      · simp
  have hG : ∀ b k, σ (G b k) = σ X * σ (G (T b) k) + C (coeff k b) := by
    intro b k
    have : G b k = X * G (T b) k + C (coeff k b) := by
      conv_lhs => rw [eq_X_mul_shift_add_const (G b k)]
      simp [G]
    rw [this, map_add (f := _), map_mul]
    congr 1
    exact σ.commutes _
  have key : ∀ n, ∀ b : R⟦X⟧, X ^ n ∣ b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro b
      have : b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) =
          σ X * (T b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G (T b) k)) := by
        have h1 := hT b
        simp only [hG b, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum, mul_left_comm (σ X)]
        linear_combination h1
      rw [this, pow_succ']
      refine mul_dvd_mul ?_ (ih _)
      rw [h]
      exact (dvd_pow_self X hs.ne').mul_left w
  refine ⟨G b, sub_eq_zero.1 ?_⟩
  ext n
  exact X_pow_dvd_iff.1 (key (n + 1) b) n n.lt_succ_self

theorem existsUnique_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃! G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨G, hG⟩ := exists_sum h hs hw b
  refine ⟨G, hG, fun G' hG' => sub_eq_zero.1 (eq_zero_of_lead h hs hw _ fun n _ => Or.inl ?_)⟩
  simp only [Pi.sub_apply, map_sub σ, mul_sub, Finset.sum_sub_distrib, ← hG, ← hG', sub_self, map_zero]

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] (hl : (l : O) ≠ 0) : Function.Injective (algebraMap ℤ_[l] O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl) hx

end ParamRing

open ParamRing

theorem invariants_param : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Δ : Subgroup ℤ_[l]ˣ) [Fintype ↥Δ] (π' w : PowerSeries O), IsUnit w → π' = w * PowerSeries.X ^ Fintype.card ↥Δ → (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) π' = π') → (∀ b : PowerSeries O, ∃! G : Fin (Fintype.card ↥Δ) → PowerSeries O, b = ∑ k : Fin (Fintype.card ↥Δ), PowerSeries.X ^ (k : ℕ) * PowerSeries.subst π' (G k)) ∧ ∀ b : PowerSeries O, (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) b = b) ↔ ∃ g : PowerSeries O, b = PowerSeries.subst π' g := by
  intro l _ O _ _ _ _ _ hl _ Δ _ π' w hw hπ hinv
  have hs : 0 < Fintype.card ↥Δ := Fintype.card_pos
  have hsub : HasSubst π' := HasSubst.of_constantCoeff_zero' (by simp [hπ, hs.ne'])
  set σ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hsub with hσ
  have hσa : ∀ g, subst π' g = σ g := fun g => (congrFun (coe_substAlgHom hsub) g).symm
  have hσX : σ X = w * X ^ Fintype.card ↥Δ := (substAlgHom_X hsub).trans hπ
  have hfix : ∀ (d : ↥Δ) (g : O⟦X⟧), act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) (σ g) = σ g := by
    intro d g
    have := hinv d
    rw [act_apply] at this
    rw [← hσa, act_apply, subst_comp_subst_apply hsub
      (HasSubst.of_constantCoeff_zero' (cyc_const l O _)), this]
  simp only [hσa]
  refine ⟨existsUnique_sum hσX hs hw, fun b => ⟨fun hb => ?_, ?_⟩⟩
  swap
  · rintro ⟨g, rfl⟩ d
    exact hfix d g
  obtain ⟨G, hG⟩ := exists_sum hσX hs hw b
  refine ⟨G ⟨0, hs⟩, ?_⟩
  have hG' : b - σ (G ⟨0, hs⟩) =
      ∑ k : Fin (Fintype.card ↥Δ), X ^ (k : ℕ) * σ (Function.update G ⟨0, hs⟩ 0 k) := by
    rw [hG, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩)]
    simp only [pow_zero, one_mul, Function.update_self, map_zero, zero_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h0 : Function.update G ⟨0, hs⟩ 0 = 0 := by
    refine eq_zero_of_lead hσX hs hw _ fun n hn => ?_
    rw [← hG'] at hn ⊢
    by_cases hd : Fintype.card ↥Δ ∣ n
    · right
      have : (⟨n % _, Nat.mod_lt _ hs⟩ : Fin (Fintype.card ↥Δ)) = ⟨0, hs⟩ :=
        Fin.ext (Nat.mod_eq_zero_of_dvd hd)
      rw [this, Function.update_self]
    left
    by_contra hc
    apply hd
    haveI : IsCyclic ↥Δ := isCyclic_of_injective_ringHom ((Units.coeHom ℤ_[l]).comp Δ.subtype)
      (Units.val_injective.comp Subtype.val_injective)
    obtain ⟨d, hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Δ)
    rw [← Nat.card_eq_fintype_card, ← hd, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨u, hu⟩ : (X : O⟦X⟧) ∣ cyc l O ((d : ℤ_[l]ˣ) : ℤ_[l]) := X_dvd_iff.2 (cyc_const l O _)
    have hu0 : constantCoeff u = algebraMap ℤ_[l] O ((d : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [← coeff_one_cyc, hu, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
    have h1 := coeff_map_lead (σ := act l O ((d : ℤ_[l]ˣ) : ℤ_[l])) (w := u) (s := 1)
      (by rw [act_X, hu, pow_one, mul_comm]) one_pos hn
    rw [map_sub (act l O _), hb, hfix, one_mul, hu0, ← map_pow, eq_comm, mul_eq_right₀ hc,
      ← map_one (algebraMap ℤ_[l] O)] at h1
    have h2 := algebraMap_injective l O hl h1
    apply Subtype.ext
    apply Units.ext
    simpa using h2
  rw [← sub_eq_zero, hG', h0]
  simp

end GlobalTheory.Cyc
end
end

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.DelParam

theorem algHom_eq_subst {O : Type} [CommRing O] (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : (X : O⟦X⟧) ∣ j X)
    (a : O⟦X⟧) : j a = a.subst (j X) := by
  have hs : HasSubst (j X) := HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 hj)
  have := algHom_ext_X j (substAlgHom hs) hj (by rw [coe_substAlgHom, subst_X hs])
  rw [← coe_substAlgHom hs, ← this]

theorem dvd_coeff_of_aeval {O : Type} [CommRing O] (a : O) (ξ w : O⟦X⟧) (s e : ℕ) (hs : 0 < s)
    (hw : IsUnit w) (hξ : ξ = w * X ^ s) (E : Polynomial O) (b c : O⟦X⟧)
    (h : Polynomial.aeval ξ E = X ^ (e * s) * b + C a * c) : ∀ k < e, a ∣ E.coeff k := by
  induction e generalizing E b c with
  | zero => intro k hk; omega
  | succ e ih =>
    have hE := Polynomial.X_mul_divX_add E
    have h0 : a ∣ E.coeff 0 := by
      have h1 := congrArg constantCoeff h
      rw [← hE] at h1
      simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hξ, map_pow,
        constantCoeff_X, zero_pow hs.ne', zero_pow (Nat.mul_pos e.succ_pos hs).ne', mul_zero,
        zero_mul, zero_add, constantCoeff_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply] at h1
      exact ⟨_, h1⟩
    obtain ⟨d, hd⟩ := h0
    obtain ⟨w', hw'⟩ := hw.exists_right_inv
    have h2 : X ^ s * (w * Polynomial.aeval ξ E.divX - X ^ (e * s) * b) = C a * (c - C d) := by
      rw [← hE, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hd] at h
      have hC : algebraMap O O⟦X⟧ (a * d) = C a * C d := by rw [← map_mul]; rfl
      rw [hC] at h
      nth_rewrite 1 [hξ] at h
      linear_combination h
    have h3 : ∃ c', w * Polynomial.aeval ξ E.divX - X ^ (e * s) * b = C a * c' := by
      refine ⟨PowerSeries.mk fun k => coeff (k + s) (c - C d), ?_⟩
      ext k
      rw [coeff_C_mul, coeff_mk, ← coeff_C_mul, ← h2, coeff_X_pow_mul]
    obtain ⟨c', hc'⟩ := h3
    have h4 := ih E.divX (w' * b) (w' * c') (by
      linear_combination w' * hc' - Polynomial.aeval ξ E.divX * hw')
    intro k hk
    cases k with
    | zero => exact ⟨d, hd⟩
    | succ k => rw [← Polynomial.coeff_divX]; exact h4 k (by omega)

theorem prod_one_root {O : Type} [CommRing O] (ϖ : Fin 1 → O) (a : O) (E : Polynomial O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))) (h : ϖ 0 = -a) :
    E = Polynomial.X + Polynomial.C a := by
  rw [hE, Fin.prod_univ_one, h, map_neg, sub_neg_eq_add]

theorem lvl_zero_mod {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] :
    ∃ r : O⟦X⟧, lvl l O 0 = X ^ (l - 1) + C (l : O) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (1 : O⟦X⟧) X
  have h1 := mul_lvl (l := l) (O := O) 0
  simp only [pow_zero, pow_one, zero_add, add_sub_cancel_left] at h1
  refine ⟨r, mul_left_cancel₀ (X_ne_zero (R := O)) ?_⟩
  have h2 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : l.Prime).one_le]
  rw [h1, hr, map_natCast, h2]; ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O]
    (hp : PD.p = l)

def EisAt (l e : ℕ) (ξ : O⟦X⟧) (E : Polynomial O) : Prop :=
  E.Monic ∧ E.natDegree = e ∧ (∀ k < e, (l : O) ∣ E.coeff k) ∧
    Associated (E.coeff 0) (l : O) ∧ Associated (Polynomial.aeval ξ E) W.q₀ ∧
    (∃ c : O⟦X⟧, IsUnit c ∧ W.φ₀ ξ = c.subst ξ * ξ * Polynomial.aeval ξ E ^ W.DelF.card) ∧
    ∃ c : O⟦X⟧, IsUnit c ∧ W.γ₀ W.gam ξ - ξ = c.subst ξ * ξ * Polynomial.aeval ξ E

def HasEis (l e : ℕ) (ξ : O⟦X⟧) : Prop :=
  ∃ (E : Polynomial O) (ϖ : Fin e → O), E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)) ∧
    (∀ τ, Associated (ϖ τ ^ e) (l : O)) ∧
    (∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ ξ - C (ϖ τ)) ∧
    Function.Injective ϖ ∧ EisAt W l e ξ E

include hp

theorem free_and_invariants_gen [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hu : ¬ IsUnit (l : O))
    (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (ξ : O⟦X⟧)
    (hξ : Associated ξ (X ^ W.DelF.card)) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    (∀ b : O⟦X⟧, ∃! G : Fin W.DelF.card → O⟦X⟧,
      b = ∑ k : Fin W.DelF.card, X ^ (k : ℕ) * (G k).subst ξ) ∧
    ∀ b : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ b = b) ↔ ∃ g : O⟦X⟧, b = g.subst ξ := by
  classical
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Cyc.act l O (χ g : ℤ_[l]) := fun g => by
    rw [γ₀_eq W hp χ hχ g]
    refine algHom_ext_X _ _ (X_dvd_act_X _) ?_
    rw [act_X, GlobalTheory.Cyc.Series.act_X, GlobalTheory.Cyc.Series.cyc_eq]
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  have : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  let _ : Fintype Δ := Fintype.ofFinite _
  have hcard : Fintype.card Δ = W.DelF.card := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  obtain ⟨w, hw⟩ := hξ.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.Cyc.invariants_param l O
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hu Δ ξ w w.isUnit
    (by rw [hcard, ← hw, mul_comm])
    (fun d => (hfa fun d => GlobalTheory.Cyc.act l O (d : ℤ_[l]) ξ = ξ).2 (fun δ hδ => by
      rw [← hγ]; exact hinv δ hδ) d d.2)
  refine ⟨hcard ▸ h1, fun b => ?_⟩
  rw [← h2, Subtype.forall, hfa fun d => GlobalTheory.Cyc.act l O (d : ℤ_[l]) b = b]
  simp only [hγ]

theorem eisenstein_gen (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (ht : FrTie W R j)
    (E : Polynomial O) (hEd : E = ∏ τ, (Polynomial.X - Polynomial.C (R.ϖ τ))) :
    Function.Injective R.ϖ ∧ EisAt W l R.e (j X) E := by
  subst hEd
  obtain ⟨-, -, hφ, hγ, -, hs, hX, hE⟩ := ht
  have hes := R.es
  have h2l := (Fact.out : l.Prime).two_le
  have hs0 : 0 < R.s := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hes; omega
  have he0 : R.e ≠ 0 := fun h0 => by rw [h0] at hes; omega
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hj : (X : O⟦X⟧) ∣ j X := (dvd_pow_self X hs0.ne').trans hX.symm.dvd
  have hq := (φ₀_eq W hp).2
  rw [EisAt, ← hs]
  have hjE : Polynomial.aeval (j X) (∏ τ, (Polynomial.X - Polynomial.C (R.ϖ τ))) = j R.E := by
    rw [R.E_def, map_prod, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algHom_C]
  refine ⟨fun τ τ' hτ => ?_,
    Polynomial.monic_prod_of_monic _ _ fun τ _ => Polynomial.monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hne
    have h1 := R.ϖ_sub τ τ' hne
    rw [hτ, sub_self, ← hτ] at h1
    have h2 := R.ϖ_val τ
    rw [(associated_zero_iff_eq_zero _).1 h1.symm, zero_pow he0] at h2
    exact hl0 ((associated_zero_iff_eq_zero _).1 h2.symm)
  · rw [Polynomial.natDegree_prod_of_monic _ _ fun τ _ => Polynomial.monic_X_sub_C _]
    simp
  · obtain ⟨w, hw⟩ := hX.symm
    obtain ⟨u, hu⟩ := hE.symm
    obtain ⟨r, hr⟩ := lvl_zero_mod (l := l) O
    refine dvd_coeff_of_aeval _ (j X) w R.s R.e hs0 w.isUnit (by rw [← hw, mul_comm]) _ u (r * u) ?_
    rw [hjE, ← hu, hq, hr, hes]; ring
  · obtain ⟨u, hu⟩ := hE.symm
    have h1 := congrArg constantCoeff hu
    rw [map_mul, hq, constantCoeff_lvl, constantCoeff_algHom j hj, R.E_def, map_prod] at h1
    rw [Polynomial.coeff_zero_prod]
    simp only [map_sub, constantCoeff_X, constantCoeff_C] at h1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
    rw [← h1]
    exact associated_mul_unit_left _ _ (u.isUnit.map _)
  · rw [hjE]; exact hE
  · refine ⟨R.u, R.u.isUnit, ?_⟩
    rw [← hφ, R.φ_X, map_mul, map_mul, map_pow, hjE, algHom_eq_subst j hj R.u]
  · refine ⟨R.κ, R.κ.isUnit, ?_⟩
    rw [← hγ, R.γ_X, map_mul, map_add (f := _), map_one, map_mul, hjE, algHom_eq_subst j hj R.κ]
    ring


omit hp [CharZero O] [Algebra ℤ_[l] O] in
theorem eisAt_one [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hu : ¬ IsUnit (l : O)) (ξ : O⟦X⟧) (hq : lvl l O 0 ∣ ξ + (l : O⟦X⟧)) (e₀ : ℕ) (he₀ : e₀ = 1)
    (hA : HasEis W l e₀ ξ) : EisAt W l 1 ξ (Polynomial.X + Polynomial.C (l : O)) := by
  obtain ⟨E, ϖ, hE, -, hr, -, hA⟩ := hA
  subst he₀
  obtain ⟨ζ, hζ, hd⟩ := hr 0
  rwa [prod_one_root ϖ _ E hE (eq_neg_of_root hu _ _ ζ hζ hd hq)] at hA

end Generic

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
  (h : Good K 1 LL) (hl : l ≠ 2)
include hl

theorem card_eq : (H.W K 1 LL h).DelF.card = (l - 1) / Module.finrank ↥(K0 K) ↥K.1 := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
  have h2l := (Fact.out : l.Prime).two_le
  have h0 : 0 < Module.finrank ↥(K0 K) ↥K.1 := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hc; omega
  rw [← hc, Nat.mul_div_cancel _ h0]


omit hl in
theorem free_and_invariants (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    (∀ b : (↥(OL LL))⟦X⟧, ∃! G : Fin (H.W K 1 LL h).DelF.card → (↥(OL LL))⟦X⟧,
      b = ∑ k : Fin (H.W K 1 LL h).DelF.card, X ^ (k : ℕ) * (G k).subst ξ) ∧
    ∀ b : (↥(OL LL))⟦X⟧, (∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ b = b) ↔
      ∃ g : (↥(OL LL))⟦X⟧, b = g.subst ξ := by
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  let W := H.W K 1 LL h
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    apply (IsFractionRing.injective ℤ_[l] ℚ_[l])
    apply (algebraMap ℚ_[l] ↥LL.1).injective
    exact congrArg Subtype.val hab
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨a, rfl⟩ := W.resΓ_onto g
    have hm : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ a : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res a]
      exact (W.χΓ (W.resΓ a) : ↥(OL LL)).2
    have hi : IsIntegral ℤ_[l] ((P.PD K).χ a : ℚ_[l]) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
        (algebraMap ℚ_[l] ↥LL.1).injective).mp hm
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res a]
    rfl
  choose y hy using hex
  have hmul : ∀ g, y g * y g⁻¹ = 1 := fun g => hinj (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hmul' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hmul g⁻¹
  let u : W.Gam → ℤ_[l]ˣ := fun g => ⟨y g, y g⁻¹, hmul g, hmul' g⟩
  let χ : W.Gam →* ℤ_[l]ˣ := by
    refine { toFun := u, map_one' := ?_, map_mul' := ?_ }
    · apply Units.ext; apply hinj; simp [u, hy]
    · intro g k; apply Units.ext; apply hinj; simp [u, hy]
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL)) := fun g => hy g
  exact free_and_invariants_gen (H.W K 1 LL h) (P.PD_p K) hu χ hχ ξ hξ hinv

theorem exists_eisenstein (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    HasEis (H.W K 1 LL h) l (Module.finrank ↥(K0 K) ↥K.1) ξ := by
  obtain ⟨R, j, jE, hj, he, ht, -, hr, -⟩ := exists_attached H h hl ξ hξ hinv
  have h1 : HasEis (H.W K 1 LL h) l R.e (j X) :=
    ⟨_, R.ϖ, rfl, R.ϖ_val, hr, eisenstein_gen (H.W K 1 LL h) (P.PD_p K) R j ht _ rfl⟩
  rwa [hj, he] at h1


set_option maxHeartbeats 800000 in
theorem trace_param (h1 : Module.finrank ↥(K0 K) ↥K.1 = 1) :
    (H.W K 1 LL h).DelF.card = l - 1 ∧
    Associated (H.W K 1 LL h).π₀₁ (X ^ (H.W K 1 LL h).DelF.card) ∧
    (∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ (H.W K 1 LL h).π₀₁ = (H.W K 1 LL h).π₀₁) ∧
    EisAt (H.W K 1 LL h) l 1 (H.W K 1 LL h).π₀₁
      (Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL))) := by
  have hc := card_eq H h hl
  rw [h1, Nat.div_one] at hc
  let W := H.W K 1 LL h
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    apply (IsFractionRing.injective ℤ_[l] ℚ_[l])
    apply (algebraMap ℚ_[l] ↥LL.1).injective
    exact congrArg Subtype.val hab
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨a, rfl⟩ := W.resΓ_onto g
    have hm : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ a : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res a]
      exact (W.χΓ (W.resΓ a) : ↥(OL LL)).2
    have hi : IsIntegral ℤ_[l] ((P.PD K).χ a : ℚ_[l]) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
        (algebraMap ℚ_[l] ↥LL.1).injective).mp hm
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res a]
    rfl
  choose y hy using hex
  have hmul : ∀ g, y g * y g⁻¹ = 1 := fun g => hinj (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hmul' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hmul g⁻¹
  let u : W.Gam → ℤ_[l]ˣ := fun g => ⟨y g, y g⁻¹, hmul g, hmul' g⟩
  let χ : W.Gam →* ℤ_[l]ˣ := by
    refine { toFun := u, map_one' := ?_, map_mul' := ?_ }
    · apply Units.ext; apply hinj; simp [u, hy]
    · intro g k; apply Units.ext; apply hinj; simp [u, hy]
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL)) := fun g => hy g
  obtain ⟨p2, p3, p4⟩ := π₀₁_spec (H.W K 1 LL h) (P.PD_p K) χ hχ hl hc
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact ⟨hc, p2, p3, eisAt_one (H.W K 1 LL h) hu _ p4 _ h1 (exists_eisenstein H h hl _ p2 p3)⟩

end GlobalTheory.DelParam
end
end

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.CycFr GlobalTheory.WachTie GlobalTheory.TorsionCard

namespace GlobalTheory.DelParam

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime]


omit [Fact l.Prime] in
theorem ring_of_const {e : ℕ} (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (hs : W.DelF.card ≠ 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ)
    (hfree : ∀ b : O⟦X⟧, ∃! G : Fin W.DelF.card → O⟦X⟧,
      b = ∑ k : Fin W.DelF.card, X ^ (k : ℕ) * (G k).subst ξ)
    (hrange : ∀ b : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ b = b) ↔ ∃ g : O⟦X⟧, b = g.subst ξ)
    (E : Polynomial O) (hA : EisAt W l e ξ E) (ϖ : Fin e → O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)))
    (hv : ∀ τ, v (algebraMap O LL (ϖ τ)) = ((1 / (e : ℚ) : ℚ) : WithTop ℚ))
    (E₁ : Polynomial Qp) (h1 : E.map (algebraMap O LL) = E₁.map (algebraMap Qp LL))
    (x : K) (hx : Polynomial.aeval x E₁ = 0) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e W.DelF.card (fun _ => ξ) (fun _ => E) := by
  obtain ⟨-, hd, -, -, hq, ⟨c₁, u₁, hc₁⟩, ⟨c₂, u₂, hc₂⟩⟩ := hA
  have hX : (X : O⟦X⟧) ∣ ξ := (dvd_pow_self X hs).trans hξ.symm.dvd
  have hsub : HasSubst ξ := HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 hX)
  have hun : ∀ c : O⟦X⟧, IsUnit c → IsUnit (c.subst ξ) := fun c hc => by
    rw [← coe_substAlgHom hsub]; exact hc.map _
  have hpi : ∀ c : O⟦X⟧, IsUnit c → ∃ w : (LetA O n)ˣ, (w : LetA O n) = fun _ => c :=
    fun c hc => Pi.isUnit_iff.2 fun _ => hc
  have hinj : ∀ f g : O⟦X⟧, (f.subst ξ : O⟦X⟧) = g.subst ξ → f = g := by
    intro f g hfg
    let k₀ : Fin W.DelF.card := ⟨0, Nat.pos_of_ne_zero hs⟩
    have key : ∀ f : O⟦X⟧, (f.subst ξ : O⟦X⟧) = ∑ k : Fin W.DelF.card,
        X ^ (k : ℕ) * ((Pi.single k₀ f : Fin W.DelF.card → O⟦X⟧) k).subst ξ := by
      intro f
      rw [Finset.sum_eq_single k₀ (fun k _ hk => by
        rw [Pi.single_eq_of_ne hk, ← coe_substAlgHom hsub, map_zero, mul_zero]) (by simp)]
      simp [k₀]
    have := (hfree (f.subst ξ)).unique (key f) (hfg.trans (key g))
    simpa using congrFun this k₀
  refine ⟨fun δ hδ => funext fun _ => hinv δ hδ, fun a ha => ?_, ?_, fun _ => hd, ?_, ?_, ?_,
    E₁.map (algebraMap Qp K₀), fun i => ?_, x, ?_, fun τ => ?_⟩
  · choose f hf using fun i => (hrange (a i)).1 fun δ hδ => congrFun (ha δ hδ) i
    exact ⟨f, hf, fun g hg => funext fun i => hinj _ _ ((hg i).symm.trans (hf i))⟩
  · obtain ⟨u, hu⟩ := hξ.symm
    obtain ⟨w, hw⟩ := hpi u u.isUnit
    exact ⟨w, by rw [hw]; exact funext fun _ => (hu.symm.trans (mul_comm _ _))⟩
  · obtain ⟨u, hu⟩ := hq
    obtain ⟨w, hw⟩ := hpi u u.isUnit
    exact ⟨w, by rw [hw]; exact funext fun _ => (hu.symm.trans (mul_comm _ _))⟩
  · obtain ⟨w, hw⟩ := hpi _ (hun c₁ u₁)
    exact ⟨w, by rw [hw]; exact funext fun _ => hc₁⟩
  · obtain ⟨w, hw⟩ := hpi _ (hun c₂ u₂)
    exact ⟨w, by rw [hw]; exact funext fun _ => hc₂⟩
  · rw [h1, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun c => ((W.emb i).commutes c).symm
  · rw [Polynomial.aeval_map_algebraMap, hx]
  · have h2 : Polynomial.eval (τ x) (E.map (algebraMap O LL)) = 0 := by
      rw [h1, Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, hx, map_zero]
    rw [hE, Polynomial.map_prod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
    obtain ⟨τ', -, h3⟩ := h2
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at h3
    rw [h3, hv]

variable (χ : W.Gam →* ℤ_[l]ˣ)

def resid (g : W.Gam) : ℕ := (red l (χ g) : ZMod l).val

def nrm {R : Type} [CommRing R] (ζ : R) : R := ∏ δ ∈ W.DelF, (ζ ^ resid W χ δ - 1)

theorem map_nrm {R S F : Type} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (ζ : R) : f (nrm W χ ζ) = nrm W χ (f ζ) := by
  simp [nrm, map_prod]

theorem nrm_pow {R : Type} [CommRing R] (ζ : R) (hζ : ζ ^ l = 1) (d : W.Gam) (hd : d ∈ W.DelF) :
    nrm W χ (ζ ^ resid W χ d) = nrm W χ ζ := by
  rw [nrm, nrm, ← prod_DelF_mul W (fun δ => ζ ^ resid W χ δ - 1) d hd]
  refine Finset.prod_congr rfl fun δ _ => ?_
  simp only [resid, map_mul, Units.val_mul, ZMod.val_mul]
  rw [← pow_eq_pow_mod _ hζ, pow_mul]

theorem exists_torsion_resid (hl : l ≠ 2) (hχ : Function.Injective χ)
    (hk : ∀ x, red l x = 1 → ∃ g, χ g = x) (g : W.Gam) :
    ∃ d ∈ W.DelF, resid W χ d = resid W χ g := by
  obtain ⟨x, hx, hxu⟩ := exists_lift hl (red l (χ g))
  obtain ⟨h, hh⟩ := hk (x * (χ g)⁻¹) (by rw [map_mul, map_inv, hxu, mul_inv_cancel])
  have e : χ (h * g) = x := by rw [map_mul, hh, inv_mul_cancel_right]
  exact ⟨h * g, (mem_DelF_iff W _).2 (hχ.isOfFinOrder_iff.1 (e ▸ hx)), by rw [resid, e, hxu, resid]⟩

variable [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem dvd_piNorm_sub (ζ : O) (hζ : ζ ^ l = 1) :
    (X - C (ζ - 1) : O⟦X⟧) ∣ piNorm W - C (nrm W χ ζ) := by
  have h0 : ∀ k : ℕ, (X - C (ζ - 1) : O⟦X⟧) ∣ (1 + X) ^ k - C ζ ^ k := fun k => by
    convert sub_dvd_pow_sub_pow (1 + X : O⟦X⟧) (C ζ) k using 1
    rw [map_sub, map_one]; ring
  have h1 : (X - C (ζ - 1) : O⟦X⟧) ∣ (1 + X) ^ l ^ 1 - 1 := by
    have := h0 l
    rwa [← map_pow, hζ, map_one, ← pow_one l] at this
  rw [piNorm, nrm, map_prod, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, map_prod, map_prod]
  refine Finset.prod_congr rfl fun δ _ => ?_
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, γ₀_eq W hp χ hχ, act_X]
  have h2 : (l : ℤ_[l]) ^ 1 ∣ (χ δ : ℤ_[l]) - (resid W χ δ : ℕ) := by
    rw [pow_one, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
      RingHom.mem_ker, map_sub, map_natCast, resid, ZMod.natCast_zmod_val, red_val, sub_self]
  have h3 := (h1.trans (dvd_bin_sub (O := O) 1 _ _ h2)).add (h0 (resid W χ δ))
  rw [bin_nat] at h3
  convert h3 using 1
  rw [map_sub, map_pow, map_one]; ring

theorem roots_eq_nrm [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hu : ¬ IsUnit (l : O)) {e : ℕ} (E : Polynomial O) (ϖ : Fin e → O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)))
    (hr : ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ piNorm W - C (ϖ τ))
    (hq : Associated (Polynomial.aeval (piNorm W) E) W.q₀) :
    (∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ ϖ τ = nrm W χ ζ) ∧
      ∀ ζ : O, IsPrimitiveRoot ζ l → ∃ τ, ϖ τ = nrm W χ ζ := by
  have key : ∀ (ζ x : O), IsPrimitiveRoot ζ l → X - C (ζ - 1) ∣ piNorm W - C x → x = nrm W χ ζ := by
    intro ζ x hζ hd
    refine sub_eq_zero.1 ((prime_X_sub_C _ (sub_one_mem_max hu ζ hζ.pow_eq_one)).2 _ ?_)
    convert (dvd_piNorm_sub W χ hp hχ ζ hζ.pow_eq_one).sub hd using 1
    rw [map_sub]; ring
  refine ⟨fun τ => ?_, fun ζ hζ => ?_⟩
  · obtain ⟨ζ, hζ, hd⟩ := hr τ
    exact ⟨ζ, hζ, key ζ _ hζ hd⟩
  · have h4 : X - C (ζ - 1) ∣ lvl l O 0 := by
      have h5 : lvl l O 0 = ∑ i ∈ Finset.range l, ((1 + X) ^ i - C ζ ^ i) := by
        rw [Finset.sum_sub_distrib]
        simp only [← map_pow]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hζ.geom_sum_eq_zero (Fact.out : l.Prime).one_lt]
        simp [lvl]
      rw [h5]
      refine Finset.dvd_sum fun i _ => ?_
      convert sub_dvd_pow_sub_pow (1 + X) (C ζ) i using 1
      rw [map_sub, map_one]; ring
    rw [← (φ₀_eq W hp).2] at h4
    have h6 := h4.trans hq.symm.dvd
    rw [hE, map_prod, (prime_X_sub_C _ (sub_one_mem_max hu ζ hζ.pow_eq_one)).1.dvd_finsetProd_iff] at h6
    obtain ⟨τ, -, hτ⟩ := h6
    rw [map_sub (Polynomial.aeval _), Polynomial.aeval_X, Polynomial.aeval_C] at hτ
    exact ⟨τ, key ζ _ hζ hτ⟩


omit [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] hp hχ in
theorem exists_lift_base {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (f : O →+* Ω) (hf : Function.Injective f) {e : ℕ} (ϖ : Fin e → O) (hϖ : Function.Injective ϖ)
    (h1 : ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ ϖ τ = nrm W χ ζ)
    (h2 : ∀ ζ : O, IsPrimitiveRoot ζ l → ∃ τ, ϖ τ = nrm W χ ζ) :
    ∃ E₁ : Polynomial F, E₁.map (algebraMap F Ω) =
      (∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))).map f := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro k
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun g => ?_
  have h3 : ∀ τ, ∃ τ', f (ϖ τ') = g (f (ϖ τ)) := by
    intro τ
    obtain ⟨ζ, hζ, hτ⟩ := h1 τ
    have hz := hζ.map_of_injective hf
    have hg := hz.map_of_injective g.injective
    have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hg.pow_eq_one
    rw [← map_pow] at ha
    obtain ⟨τ', hτ'⟩ := h2 (ζ ^ a) (IsPrimitiveRoot.of_map_of_injective (ha ▸ hg) hf)
    exact ⟨τ', by rw [hτ', hτ, map_nrm, map_nrm, map_nrm, ha]⟩
  choose σ hσ using h3
  have hσi : Function.Injective σ := fun a b hab =>
    hϖ (hf (g.injective (by rw [← hσ, ← hσ, hab])))
  have h4 : ((∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))).map f).map (g : Ω →+* Ω) =
      (∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))).map f := by
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine Fintype.prod_bijective σ (Finite.injective_iff_bijective.1 hσi) _ _ fun τ => ?_
    rw [hσ]; rfl
  have h5 := congrArg (fun p => p.coeff k) h4
  simp only [Polynomial.coeff_map (g : Ω →+* Ω)] at h5
  exact h5

end Generic

variable {l : ℕ} [Fact l.Prime]

theorem val_of_pow_associated (P : LocPrime l) (LL : FinExt l) (x : ↥(OL LL)) (e : ℕ)
    (h : Associated (x ^ e) (l : ↥(OL LL))) :
    P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) = ((1 / (e : ℚ) : ℚ) : WithTop ℚ) := by
  obtain ⟨u, hu⟩ := h
  have h0 : ∀ y : ↥(OL LL), 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 y) := fun y => (P.v_O LL _).2 y.2
  have h1 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 u) = 0 := by
    have h2 := congrArg (fun y => P.v LL (algebraMap ↥(OL LL) ↥LL.1 y)) u.mul_inv
    simp only [map_mul, AddValuation.map_mul, map_one, AddValuation.map_one] at h2
    exact le_antisymm (h2 ▸ le_add_of_nonneg_right (h0 _)) (h0 _)
  have h3 := congrArg (fun y => P.v LL (algebraMap ↥(OL LL) ↥LL.1 y)) hu
  simp only [map_mul, AddValuation.map_mul, map_pow, AddValuation.map_pow, map_natCast, P.v_l, h1,
    add_zero] at h3
  generalize P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) = a at h3
  have he : e ≠ 0 := by
    rintro rfl
    simp at h3
  induction a using WithTop.recTopCoe with
  | top =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
    rw [succ_nsmul, add_top] at h3
    exact absurd h3 WithTop.top_ne_one
  | coe a =>
    rw [← WithTop.coe_nsmul, ← WithTop.coe_one, WithTop.coe_inj, nsmul_eq_mul] at h3
    rw [WithTop.coe_inj, eq_div_iff (Nat.cast_ne_zero.2 he), mul_comm, h3]

theorem act_root (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : ↥(GK K))
    (z : Om l) (hz : z ^ l = 1) : (g : GQ l) z = z ^ resid W χ (W.resΓ g) := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g 1 z (by rwa [pow_one])
  have hr := W.χΓ_res g
  rw [P.PD_χ, ← hχ] at hr
  have h1 : ((χ (W.resΓ g) : ℤ_[l]) : ℚ_[l]) = (P.χQ g : ℚ_[l]) :=
    (algebraMap ℚ_[l] ↥LL.1).injective hr
  have h2 : (χ (W.resΓ g) : ℤ_[l]) - a ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, ← pow_one (l : ℤ_[l]),
      ← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [← h1] at ha
    exact ha
  rw [RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h2
  rw [hga, resid, red_val, h2, ZMod.val_natCast, ← pow_eq_pow_mod _ hz]

variable {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l} (h : Good K 1 LL) (hl : l ≠ 2)
include hl

theorem card_ne_zero : (H.W K 1 LL h).DelF.card ≠ 0 := fun h0 => by
  have hc := card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
  have h2l := (Fact.out : l.Prime).two_le
  rw [h0] at hc; omega


set_option maxHeartbeats 800000 in
theorem norm_ring (χ : (H.W K 1 LL h).Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = ((H.W K 1 LL h).χΓ g : ↥(OL LL)))
    (hk : ∀ x, red l x = 1 → ∃ g, χ g = x) :
    ∃ π' E', Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations (H.W K 1 LL h) (Module.finrank ↥(K0 K) ↥K.1)
      (H.W K 1 LL h).DelF.card π' E' := by
  have hA := exists_eisenstein H h hl _ (piNorm_spec _).1 (piNorm_spec _).2
  have hF := free_and_invariants H h _ (piNorm_spec _).1 (piNorm_spec _).2
  have hs := card_ne_zero H h hl
  have he : 0 < Module.finrank ↥(K0 K) ↥K.1 := Nat.pos_of_ne_zero fun h0 => by
    have hc := card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
    have h2l := (Fact.out : l.Prime).two_le
    rw [h0] at hc; omega
  generalize Module.finrank ↥(K0 K) ↥K.1 = e at hA he
  generalize H.W K 1 LL h = W at *
  obtain ⟨E, ϖ, hE, hv, hr, hϖ, hA⟩ := hA
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨r1, r2⟩ := roots_eq_nrm W χ (P.PD_p K) hχ hu E ϖ hE hr hA.2.2.2.2.1
  let f₀ : ↥LL.1 →+* Om l := algebraMap _ _
  let f : ↥(OL LL) →+* Om l := f₀.comp (algebraMap ↥(OL LL) ↥LL.1)
  have hf : Function.Injective f := f₀.injective.comp Subtype.val_injective
  obtain ⟨E₁, hE₁⟩ := exists_lift_base (F := ℚ_[l]) W χ f hf ϖ hϖ r1 r2
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hx : f (ϖ ⟨0, he⟩) ∈ K.1 := by
    obtain ⟨ζ, hζ, hτ⟩ := r1 ⟨0, he⟩
    have hz := (hζ.map_of_injective hf).pow_eq_one
    rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨d, hd, hdg⟩ := exists_torsion_resid W χ hl hχi hk (W.resΓ ⟨g, hg⟩)
    have h1 : g (f ζ) = f ζ ^ resid W χ d := hdg ▸ act_root P K LL W χ hχ ⟨g, hg⟩ _ hz
    rw [hτ, map_nrm, map_nrm, h1, nrm_pow W χ _ hz d hd]
  refine ⟨_, _, ring_of_const W _ (piNorm_spec W).1 hs (piNorm_spec W).2 hF.1 hF.2 E hA ϖ hE
    (fun τ => val_of_pow_associated P LL _ e (hv τ)) E₁ ?_ ⟨_, hx⟩ ?_⟩
  · apply Polynomial.map_injective f₀ f₀.injective
    rw [Polynomial.map_map, Polynomial.map_map, hE, ← hE₁]
    rfl
  · apply (algebraMap ↥K.1 (Om l)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero, ← Polynomial.eval_map_algebraMap, hE₁,
      Polynomial.map_prod, Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, he⟩) ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    exact sub_self _


set_option maxHeartbeats 800000 in
theorem trace_ring (h1 : Module.finrank ↥(K0 K) ↥K.1 = 1) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations (H.W K 1 LL h) 1 (l - 1) (H.W K 1 LL h).π₀
      (fun _ => Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL))) := by
  obtain ⟨hc, p2, p3, hA⟩ := trace_param H h hl h1
  have hF := free_and_invariants H h _ p2 p3
  have hs := card_ne_zero H h hl
  generalize H.W K 1 LL h = W at *
  rw [← hc]
  refine ring_of_const W _ p2 hs p3 hF.1 hF.2 _ hA (fun _ => -(l : ↥(OL LL))) ?_
    (fun _ => ?_) (Polynomial.X + Polynomial.C (l : ℚ_[l])) ?_ (-(l : ↥K.1)) ?_
  · rw [Fin.prod_univ_one, map_neg, sub_neg_eq_add]
  · exact val_of_pow_associated P LL _ 1 (by rw [pow_one]; exact Associated.rfl.neg_left)
  · simp
  · simp

end GlobalTheory.DelParam


open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices in
theorem GlobalTheory.DelParam.torsion_parameters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; W.s = 1 → l ≠ 2 → W.DelF.card = (l - 1) / Module.finrank ↥(K0 K) ↥K.1 ∧ (∃ π' E', wachRingRelations W (Module.finrank ↥(K0 K) ↥K.1) ((l - 1) / Module.finrank ↥(K0 K) ↥K.1) π' E') ∧ (Module.finrank ↥(K0 K) ↥K.1 = 1 → wachRingRelations W 1 (l - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL)))) := by
  intro D HW l _ K s LL h W hs hl
  obtain rfl : 1 = s := hs.symm.trans ((HW l).W_s K s LL h)
  obtain ⟨χ, hχ, -, -, -, -, -, hk⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K 1 LL h
  have hc := GlobalTheory.DelParam.card_eq (HW l) h hl
  refine ⟨hc, ?_, GlobalTheory.DelParam.trace_ring (HW l) h hl⟩
  rw [← hc]
  refine GlobalTheory.DelParam.norm_ring (HW l) h hl χ hχ fun x hx => hk x ?_
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
    ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, ← GlobalTheory.TorsionCard.red_val, hx]
  simp
