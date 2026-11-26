module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NabValPullbackMonomial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffSubstSumLPowPowMvPowerSeriesStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffSubstSumLPowPowMvPowerSeries
namespace GlobalTheory.LogSubst

open MvPowerSeries

theorem coeff_pow_pow_eq_zero {C σ : Type} [CommRing C] {l : ℕ} (hl : 2 ≤ l)
    {u : MvPowerSeries σ C} (hu : constantCoeff u = 0) {μ : σ →₀ ℕ} {s : ℕ}
    (h : μ.degree ≤ s) : coeff μ (u ^ (l ^ s)) = 0 := by
  apply coeff_of_lt_order
  refine lt_of_lt_of_le ?_ (le_order_pow_of_constantCoeff_eq_zero _ hu)
  have : s < l ^ s := Nat.lt_pow_self (by omega)
  exact_mod_cast lt_of_le_of_lt h this

theorem coeff_subst_sum_pow_pow : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  intro C _ σ τ I _ _ _ l hl co t F f hf ht hF ν
  have hs : HasSubst f := hasSubst_of_constantCoeff_zero hf
  set G : MvPowerSeries σ C :=
    ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s • t c ^ (l ^ s) with hG
  have hord : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (F - G).order := by
    apply nat_le_order
    intro μ hμ
    rw [map_sub, hF μ, hG, sub_eq_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, coeff_smul]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro s _ hs'
    rw [Finset.mem_range] at hs'
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [coeff_pow_pow_eq_zero hl (ht c) (by omega), mul_zero]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (f i).order :=
    le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (hf i)
  have h2 : ((ν.degree + 1 : ℕ) : ℕ∞) ≤ (subst f (F - G) : MvPowerSeries τ C).order := by
    refine le_trans ?_ (le_order_subst hs (F - G))
    calc ((ν.degree + 1 : ℕ) : ℕ∞) = 1 * ((ν.degree + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hord
  have h3 : coeff ν (subst f (F - G) : MvPowerSeries τ C) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h2
    exact_mod_cast Nat.lt_succ_self _
  rw [← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply] at h3
  rw [h3, hG]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_pow, substAlgHom_apply, smul_eq_mul]

end GlobalTheory.LogSubst
end

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries : ∀ (C : Type) [Field C] (σ τ I : Type) [Fintype σ] [Fintype τ] [Fintype I] (l : ℕ), 2 ≤ l → ∀ (co : I → ℕ → C) (t : I → MvPowerSeries σ C) (F : MvPowerSeries σ C) (f : σ → MvPowerSeries τ C), (∀ x, MvPowerSeries.constantCoeff (f x) = 0) → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ μ : σ →₀ ℕ, MvPowerSeries.coeff μ F = ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, co c s * MvPowerSeries.coeff μ (t c ^ (l ^ s))) → ∀ ν : τ →₀ ℕ, MvPowerSeries.coeff ν (MvPowerSeries.subst f F) = ∑ s ∈ Finset.range (ν.degree + 1), ∑ c, co c s * MvPowerSeries.coeff ν ((MvPowerSeries.subst f (t c) : MvPowerSeries τ C) ^ (l ^ s)) := by
  first | exact @GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | exact GlobalTheory.LogSubst.coeff_subst_sum_pow_pow | (intros; apply GlobalTheory.LogSubst.coeff_subst_sum_pow_pow <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasis
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

theorem linPull_coords : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  intro C _ V d I J _ _ G S t ht ι _ e z al he hal0 hal
  obtain ⟨f, hf⟩ : ∃ f : I → MvPowerSeries ι C,
      f = fun x => ∑ j, e j x • (MvPowerSeries.X j : MvPowerSeries ι C) := ⟨_, rfl⟩
  have hlp : ∀ F : MvPowerSeries I C, linPull e F = MvPowerSeries.subst f F := by
    intro F; subst hf; rfl
  have hf0 : ∀ x, MvPowerSeries.constantCoeff (f x) = 0 := by
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hf, map_sum, MvPowerSeries.smul_eq_C_mul]
  have hsub : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hal' : ∀ c s x, S.al c s x = ∑ b', al c s b' * S.tan b' x := by
    intro c s x
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [hal0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact S.cur_zero_inl c x
    · rw [hal c s x hs]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [show S.al b' 0 x = S.tan b' x from S.cur_zero_inl b' x]
  simp only [hlp]
  refine ⟨fun c => MvPowerSeries.constantCoeff_subst_eq_zero hsub hf0 (ht.1 c), fun b μ => ?_,
    fun κ μ => ?_⟩
  · set P : I → ℕ → C := fun c s =>
      MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) with hP
    set Y : I → C := fun b' => ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s with hY
    set Zf : I → C := fun b' =>
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b' j) *
        (MvPowerSeries.X j : MvPowerSeries ι C)) with hZ
    have hx : ∀ x, ∑ b', (Y b' - Zf b') * S.tan b' x = 0 := by
      intro x
      have h := GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => S.al c s x) t (MvPowerSeries.X x) f hf0 ht.1
        (fun μ' => by rw [MvPowerSeries.coeff_X, ht.2 x μ']) μ
      rw [MvPowerSeries.subst_X hsub] at h
      have eL : MvPowerSeries.coeff μ (f x) = ∑ b', Zf b' * S.tan b' x := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hf, hZ, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_C_mul, he,
          Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have eR : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.al c s x *
          MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) =
          ∑ b', Y b' * S.tan b' x := by
        calc _ = ∑ s ∈ Finset.range (μ.degree + 1), ∑ b', ∑ c,
              al c s b' * P c s * S.tan b' x := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp only [hP, hal', Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = ∑ b', ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s * S.tan b' x :=
              Finset.sum_comm
          _ = _ := by simp only [hY, Finset.sum_mul]
      rw [eL, eR] at h
      simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
    have hv : Matrix.vecMul (fun b' => Y b' - Zf b') (Matrix.of S.tan) = 0 := by
      funext x
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hx x
    have h0 := congrFun (Matrix.eq_zero_of_vecMul_eq_zero S.U_det_ne hv) b
    exact sub_eq_zero.mp h0
  · have hF : ∀ μ' : I →₀ ℕ, MvPowerSeries.coeff μ' (S.ze t κ) =
        ∑ s ∈ Finset.range (μ'.degree + 1), ∑ c, (-S.be c s κ) *
          MvPowerSeries.coeff μ' (t c ^ V.l ^ s) := by
      intro μ'
      show -(∑ s ∈ Finset.Icc 1 μ'.degree, ∑ c : I,
        S.be c s κ * MvPowerSeries.coeff μ' (t c ^ V.l ^ s)) = _
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_subset
      · intro s hs
        simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢
        omega
      · intro s hs hns
        have hs0 : s = 0 := by
          simp only [Finset.mem_Icc, Finset.mem_range] at hs hns
          omega
        subst hs0
        simp [show ∀ c, S.be c 0 κ = 0 from fun c => S.be_zero c κ]
    rw [GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => -S.be c s κ) t (S.ze t κ) f hf0 ht.1 hF μ]
    simp only [neg_mul, Finset.sum_neg_distrib]

end GlobalTheory.MainTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupCoordinatesPullbackLinearTangentBasisStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupCoordinates_pullback_linear_tangentBasis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  first | exact @GlobalTheory.MainTerm.linPull_coords | exact GlobalTheory.MainTerm.linPull_coords | (intros; apply GlobalTheory.MainTerm.linPull_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxis
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm.Axis

variable {C : Type} [Field C] {ι ι' : Type}

def VanishesOnFirstAxis (F : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ F = 0

theorem VanishesOnFirstAxis.mul_left {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (G : MvPowerSeries (ι ⊕ ι') C) : VanishesOnFirstAxis (G * F) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [h p.2, mul_zero]
  intro b
  have h1 := hμ b
  rw [← hp', Finsupp.add_apply] at h1
  omega

theorem VanishesOnFirstAxis.smul {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (c : C) : VanishesOnFirstAxis (c • F) := by
  intro μ hμ
  rw [map_smul, h μ hμ, smul_zero]

theorem VanishesOnFirstAxis.sum {α : Type} (s : Finset α) {F : α → MvPowerSeries (ι ⊕ ι') C}
    (h : ∀ x, VanishesOnFirstAxis (F x)) : VanishesOnFirstAxis (∑ x ∈ s, F x) := by
  intro μ hμ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => h x μ hμ

theorem vanishes_X_inr (b : ι') :
    VanishesOnFirstAxis (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_X, if_neg]
  intro h
  have h1 := hμ b
  rw [h] at h1
  simp at h1

theorem VanishesOnFirstAxis.of_dvd {F G : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (hd : F ∣ G) : VanishesOnFirstAxis G := by
  obtain ⟨K, rfl⟩ := hd
  rw [mul_comm]
  exact h.mul_left K

theorem vanishes_mainM [Fintype ι] [Fintype ι'] (V : VF C) (i : ℕ) (Φ : ι' → ι → C) :
    VanishesOnFirstAxis (mainM V i Φ) :=
  (VanishesOnFirstAxis.sum _ fun b => VanishesOnFirstAxis.sum _ fun _ =>
    ((vanishes_X_inr b).mul_left _).smul _).smul _

theorem vanishes_hM {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ)
    [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) :
    VanishesOnFirstAxis (X.hM g a i e v') := by
  intro μ hμ
  unfold RowData.hM hPullW
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    intro w
    simp [map_sum]))]
  refine finsum_eq_zero_of_forall_eq_zero fun ν => ?_
  by_cases hν : ∀ w ∈ ν.support, w.1 = g
  · rw [X.hL_axes g _ _ ν (Or.inl hν), zero_smul]
  · push Not at hν
    obtain ⟨w, hw, hg⟩ := hν
    have h1 : VanishesOnFirstAxis
        ((∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
          ∑ b : ι', toW (1 - g) (v' b) w •
            (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) := by
      have h0 : ∀ c, toW g (e c) w = 0 := fun c => by simp [toW, hg]
      simp only [h0, zero_smul, Finset.sum_const_zero, zero_add]
      exact VanishesOnFirstAxis.sum _ fun b => (vanishes_X_inr b).smul _
    rw [h1.of_dvd _ μ hμ, smul_zero]
    unfold Finsupp.prod
    exact (dvd_pow_self _ (Finsupp.mem_support_iff.1 hw)).trans (Finset.dvd_prod_of_mem _ hw)

theorem coeff_hM_sub_mainM_eq_zero : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d]
    (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J)
    (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  intro C _ V d _ I J _ _ X g a i ι ι' _ _ e v' Φ μ hμ
  rw [map_sub, vanishes_hM X g a i e v' μ hμ, vanishes_mainM V i Φ μ hμ, sub_zero]

end GlobalTheory.MainTerm.Axis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  first | exact @GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | exact GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero | (intros; apply GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRename
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRename
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.MainTerm

theorem toW_same {C : Type} [Field C] {I : Fin 2 → Type} (g : Fin 2) (u : I g → C) (x : I g) :
    toW g u ⟨g, x⟩ = u x := by
  simp [toW]

theorem toW_other {C : Type} [Field C] {I : Fin 2 → Type} {g g' : Fin 2} (h : g' ≠ g) (u : I g → C)
    (x : I g') : toW g u ⟨g', x⟩ = 0 := by
  simp [toW, h]

theorem hPullW_upG {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (g : Fin 2) (F : MvPowerSeries (I g) C) (a : ι → WV I → C)
    (b : ι' → WV I → C) :
    hPullW (upG g F) a b = MvPowerSeries.subst (fun x : I g =>
      (∑ c, a c ⟨g, x⟩ • MvPowerSeries.X (Sum.inl c) + ∑ c, b c ⟨g, x⟩ • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) F := by
  have hb : MvPowerSeries.HasSubst (fun w : WV I =>
      (∑ c, a c w • MvPowerSeries.X (Sum.inl c) + ∑ c, b c w • MvPowerSeries.X (Sum.inr c) :
        MvPowerSeries (ι ⊕ ι') C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  have ha : MvPowerSeries.HasSubst (fun x : I g => (MvPowerSeries.X ⟨g, x⟩ : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold hPullW upG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb]
  congr 1
  funext x
  rw [MvPowerSeries.subst_X hb]

theorem rename_linPull {C : Type} [Field C] {σ ι τ : Type} [Fintype σ] [Fintype ι] (f : ι → τ)
    (e : ι → σ → C) (F : MvPowerSeries σ C) :
    MvPowerSeries.rename f (linPull e F) = MvPowerSeries.subst (fun x : σ =>
      (∑ c, e c x • MvPowerSeries.X (f c) : MvPowerSeries τ C)) F := by
  have ha : MvPowerSeries.HasSubst (fun x : σ =>
      (∑ c : ι, e c x • MvPowerSeries.X c : MvPowerSeries ι C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by simp
  unfold linPull
  rw [MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply ha (MvPowerSeries.HasSubst.X_comp f)]
  congr 1
  funext x
  rw [← MvPowerSeries.rename_eq_subst]
  simp

theorem hPullW_upG_toW : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  intro C _ I _ g ι ι' _ _ e v'
  have h : g ≠ 1 - g := by fin_cases g <;> decide
  refine ⟨fun F => ?_, fun F => ?_⟩
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h]
  · rw [hPullW_upG, rename_linPull]
    simp [toW_same, toW_other h.symm]

end GlobalTheory.MainTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRenameStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename : ∀ (C : Type) [Field C] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (g : Fin 2) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ F : MvPowerSeries (I g) C, hPullW (upG g F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inl (linPull e F)) ∧ ∀ F : MvPowerSeries (I (1 - g)) C, hPullW (upG (1 - g) F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = MvPowerSeries.rename Sum.inr (linPull v' F) := by
  first | exact @GlobalTheory.MainTerm.hPullW_upG_toW | exact GlobalTheory.MainTerm.hPullW_upG_toW | (intros; apply GlobalTheory.MainTerm.hPullW_upG_toW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubstEqOfCoeffEqOfKilled
namespace GlobalTheory

theorem subst_eq_of_coeff_eq_of_killed :
    ∀ (C : Type) [Field C] (σ τ : Type) [Fintype σ] [Fintype τ] (P : σ → Prop) (f : σ → MvPowerSeries τ C) (F F' : MvPowerSeries σ C), (∀ w, MvPowerSeries.constantCoeff (f w) = 0) → (∀ w, ¬ P w → f w = 0) → (∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, P w) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F') → MvPowerSeries.subst f F = MvPowerSeries.subst f F' := by
  intro C _ σ τ _ _ P f F F' h0 hk hF
  have hs : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  ext ν
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun μ => ?_
  by_cases h : ∀ w ∈ μ.support, P w
  · rw [hF μ h]
  · push Not at h
    obtain ⟨w, hw, hP⟩ := h
    have hz : (μ.prod fun s e => f s ^ e) = 0 := by
      refine Finset.prod_eq_zero hw ?_
      show f w ^ μ w = 0
      rw [hk w hP]
      exact zero_pow (Finsupp.mem_support_iff.mp hw)
    rw [hz]
    simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegral
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.GaugeDeriv

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def linForm {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries (ι ⊕ ι') C :=
  (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)

variable {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem hPullW_eq (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW H e e' = MvPowerSeries.subst (linForm e e') H := rfl

theorem constantCoeff_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries.constantCoeff (linForm e e' w) = 0 := by
  simp [linForm]

theorem hasSubst_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) :
    MvPowerSeries.HasSubst (linForm e e') := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_linForm e e' w)

theorem pderiv_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (linForm e e' w) = MvPowerSeries.C (e' b w) := by
  classical
  simp [linForm, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = MvPowerSeries.pderiv (R := C) w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem sum_toW {M : Type} [AddCommGroup M] [Module C M] (g : Fin 2) (u : I g → C) (F : WV I → M) :
    ∑ w, toW g u w • F w = ∑ k, u k • F ⟨g, k⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single g]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [toW]
  · intro g' _ hg'
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp [toW, hg']
  · simp

theorem pderiv_hPullW (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (g : Fin 2)
    (v' : ι' → I g → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (hPullW H e (fun b => toW g (v' b))) =
      ∑ k, v' b k • hPullW (dVar ⟨g, k⟩ H) e (fun b => toW g (v' b)) := by
  have hs := hasSubst_linForm e (fun b => toW g (v' b))
  rw [hPullW_eq, GlobalTheory.FormalCalc.pderiv_subst hs]
  have key : ∀ w : WV I,
      MvPowerSeries.subst (linForm e (fun b => toW g (v' b))) (MvPowerSeries.pderiv (R := C) w H) *
          MvPowerSeries.pderiv (R := C) (Sum.inr b) (linForm e (fun b => toW g (v' b)) w) =
        toW g (v' b) w • hPullW (dVar w H) e (fun b => toW g (v' b)) := by
    intro w
    rw [pderiv_linForm, hPullW_eq, dVar_eq, MvPowerSeries.smul_eq_C_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  exact sum_toW g (v' b) (fun w => hPullW (dVar w H) e (fun b => toW g (v' b)))

theorem constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C}
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (upG g F) = 0 := by
  unfold upG
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _))
    (fun _ => MvPowerSeries.constantCoeff_X _), hF, map_zero]

variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

theorem hPullW_toLeaf (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b k, (G (1 - g)).ty (Sum.inl k) ≠ a' → v' b k = 0) (F : MvPowerSeries (WV I) C) :
    hPullW (toLeaf G g a a' F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
      hPullW F (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  rw [hPullW_eq, hPullW_eq]
  apply GlobalTheory.subst_eq_of_coeff_eq_of_killed C (WV I) (ι ⊕ ι') (OnLeafV G g a a')
  · exact constantCoeff_linForm _ _
  · rintro ⟨w1, w2⟩ hw
    have h1 : ∀ c, toW g (e c) ⟨w1, w2⟩ = 0 := by
      intro c
      by_cases h : w1 = g
      · subst h
        simp only [toW]
        exact he c w2 (fun hty => hw (Or.inl ⟨rfl, hty⟩))
      · simp [toW, h]
    have h2 : ∀ b, toW (1 - g) (v' b) ⟨w1, w2⟩ = 0 := by
      intro b
      by_cases h : w1 = 1 - g
      · subst h
        simp only [toW]
        exact hv b w2 (fun hty => hw (Or.inr ⟨rfl, hty⟩))
      · simp [toW, h]
    simp [linForm, h1, h2]
  · intro μ hμ
    rw [show MvPowerSeries.coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ from rfl]
    unfold toLeaf
    exact if_pos hμ

theorem odd_val_sub {d : ℕ} [NeZero d] (a : ZMod d) {i : ℕ} (hi : Odd i) (hid : i < d) :
    Odd (a + (i : ZMod d) - a).val := by
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hid]
  exact hi

private theorem hPullW_add (H H' : MvPowerSeries (WV I) C) (e : ι → WV I → C)
    (e' : ι' → WV I → C) :
    hPullW (H + H') e e' = hPullW H e e' + hPullW H' e e' := by
  rw [hPullW_eq, hPullW_eq, hPullW_eq, MvPowerSeries.subst_add (hasSubst_linForm e e')]

private theorem hPullW_sum_smul {κ : Type} [Fintype κ] (c : κ → C) (F : κ → MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW (∑ q, c q • F q) e e' = ∑ q, c q • hPullW (F q) e e' := by
  simp only [hPullW_eq]
  rw [GlobalTheory.FormalCalc.subst_sum' (hasSubst_linForm e e')]
  simp only [MvPowerSeries.subst_smul (hasSubst_linForm e e')]

theorem pderiv_hM : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv (R := C) (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  intro C _ V d _ I J _ _ X hAlt g a i hi hid S t ht ι ι' _ _ e v' he hvint hv b
  have hΦ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_upG w.1 ((ht w.1).1 w.2))
  have hLs := hasSubst_linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
  have hK : ∀ k : I (1 - g), ∃ γ : MvPowerSeries (WV I) C,
      (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧
      v' b k • hPullW (dVar (⟨1 - g, k⟩ : WV I) (X.hL g a (a + (i : ZMod d))))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
        v' b k • hPullW (∑ κ : J g, X.pair g κ k • upG g ((S g).ze (t g) κ))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) +
        v' b k • hPullW (MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) γ)
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
    intro k
    by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
    · obtain ⟨K, ⟨γ, hγ, rfl⟩, hEq⟩ :=
        X.C_eq hAlt g a (a + (i : ZMod d)) (odd_val_sub a hi hid) S t ht k hk
      refine ⟨γ, hγ, ?_⟩
      rw [sub_eq_iff_eq_add'] at hEq
      rw [hEq, hPullW_add, hPullW_toLeaf X.G g a _ e v' he hv,
        hPullW_toLeaf X.G g a _ e v' he hv, smul_add]
    · refine ⟨0, fun μ => ?_, ?_⟩
      · rw [map_zero]
        exact VF.Ge.zero 0
      · rw [hv b k hk]
        simp only [zero_smul, add_zero]
  choose γ hγint hγeq using hK
  refine ⟨∑ k, v' b k • γ k, ?_, ?_⟩
  · intro μ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine VF.Ge.sum (fun k _ => ?_)
    simp only [map_smul, smul_eq_mul]
    exact VF.Ge.mul_int (hvint b k) (hγint k μ)
  · unfold RowData.hM
    rw [pderiv_hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (1 - g) v' b,
      Finset.sum_congr rfl (fun k _ => hγeq k), Finset.sum_add_distrib]
    refine (add_comm _ _).trans ?_
    congr 1
    · simp only [hPullW_eq]
      have hΨ : MvPowerSeries.HasSubst (fun w : WV I =>
          MvPowerSeries.subst (linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)))
            (upG w.1 (t w.1 w.2))) := by
        have h := hΦ.comp hLs
        simp only [MvPowerSeries.substAlgHom_apply] at h
        exact h
      rw [GlobalTheory.FormalCalc.subst_sum' hΨ]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MvPowerSeries.subst_smul hΨ, MvPowerSeries.subst_comp_subst_apply hΦ hLs]
    · simp only [hPullW_sum_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]

end GlobalTheory.GaugeDeriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegralStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv (R := C) (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  first | exact @GlobalTheory.GaugeDeriv.pderiv_hM | exact GlobalTheory.GaugeDeriv.pderiv_hM | (intros; apply GlobalTheory.GaugeDeriv.pderiv_hM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralGermNabValCongr
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.IntegralColumnGerm

theorem prod_pow_sub_one_mem {R : Type} [CommRing R] (I : Ideal R) {ι : Type} [Fintype ι] (α : ι → R)
    (hα : ∀ l, α l - 1 ∈ I) (n : ι → ℕ) : ∏ l, α l ^ n l - 1 ∈ I := by
  rw [← Ideal.Quotient.eq, map_prod, map_one]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [map_pow, Ideal.Quotient.eq.2 (hα l), map_one, one_pow]

theorem exists_eq_of_unit_mul {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) (I : Ideal R) {P x y : R}
    {v : k} (hP : IsUnit P) (hP1 : P - 1 ∈ I) (hxy : x - y ∈ I) (h : φ P * v = φ x) :
    ∃ r ∈ I, v = φ (y + r) := by
  obtain ⟨Q, hQ⟩ := hP.exists_left_inv
  refine ⟨Q * ((x - y) - (P - 1) * y), I.mul_mem_left _ (I.sub_mem hxy (I.mul_mem_right _ hP1)), ?_⟩
  have e : y + Q * ((x - y) - (P - 1) * y) = Q * x := by linear_combination (-y) * hQ
  rw [e, map_mul, ← h, ← mul_assoc, ← map_mul, hQ, map_one, one_mul]

end GlobalTheory.IntegralColumnGerm

namespace GlobalTheory

open IntegralColumnGerm

theorem exists_integral_germ_nabVal_congr :
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w : O) (N : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → R),
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B w).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ mo : ι →₀ ℕ, ∃ r : R, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (B.hL k h ((N : O) * w))) = algebraMap R k (N * r)) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (I : Ideal R) (ι : Type) [Fintype ι] (u : ι → Fin d → R) (f f' g : PS R 1 d),
    (∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo f) - constantCoeff (DmonOf F u mo f') ∈ I) →
    ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf F u mo (f * g)) - constantCoeff (DmonOf F u mo (f' * g)) ∈ I) →
  (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → Function.Injective (algebraMap R k) → ∀ (w0 a c : O) (N m : ℕ) (I : Ideal R), star a * a = (N : O) * c → (N : R) ∈ I →
    ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → R) (α : ι → R), (∀ l, α l - 1 ∈ I) → (∀ l, IsUnit (α l)) →
    (∀ l, (dAct k B a).mulVec (fun i => algebraMap R k (u l i)) = algebraMap R k (α l) • (fun i => algebraMap R k (u l i))) →
    (∀ l l', dotProduct (fun i => algebraMap R k (u l i)) ((bilinPart k h).mulVec ((dAct k B (c * w0)).mulVec (fun i => algebraMap R k (u l' i)))) ∈ (algebraMap R k).range) →
    ∀ χ : PS R 1 d, ∃ g : PS R 1 d, ∀ mo : ι →₀ ℕ, ∃ r ∈ I,
      B.nabVal k h w0 m (FB.toK k g) (fun l i => algebraMap R k (u l i)) (MvPolynomial.monomial mo 1) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo χ) + r)) := by
  intro hS hL R _ d O _ _ k _ _ _ B h hh hinj w0 a c N m I hac hN ι _ u α hα1 hαu hα hβ χ
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : ∀ w : O, constantCoeff (B.hL k h w) = 0 := fun w =>
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w) (gp_pt 0))) h hh0
  have e0 : star a * (w0 * a) = (N : O) * (c * w0) := by linear_combination w0 * hac
  have h1 := FramePull.expIntegral_ad hh a 1 (w0 * a)
  rw [e0, mul_one, ← FramePull.ev_actK_hL, ← FramePull.hL_eq] at h1
  obtain ⟨cD, υ, υ1, hυ⟩ := h1
  have hinv : υ * invOfUnit υ 1 = 1 := mul_invOfUnit υ 1 (by simpa using υ1)
  obtain ⟨g, hg⟩ : ∃ g : PS R 1 d, g * υ ^ m = χ :=
    ⟨χ * invOfUnit υ 1 ^ m, by rw [mul_assoc, ← mul_pow, mul_comm _ υ, hinv, one_pow, mul_one]⟩
  refine ⟨g, fun mo => ?_⟩
  have hga : FB.toK k (ev (n := 1) ![B.A.act a] g) = ev (n := 1) ![B.actK k a] (FB.toK k g) := by
    rw [FB.toK, QuadDeriv.map_ev _ _ (single_point_zero_constant (B.A.const a))]
    congr 1
    funext j; fin_cases j; rfl
  have hG : ev (n := 1) ![B.actK k a] (FB.toK k g * FB.expS k ((m : k) • B.hL k h w0)) =
      FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) *
        FB.expS k ((m : k) • B.hL k h ((N : O) * (c * w0))) := by
    have e : FB.toK k (ev (n := 1) ![B.A.act a] g * υ ^ m) =
        FB.toK k (ev (n := 1) ![B.A.act a] g) * FB.toK k υ ^ m := by
      rw [FB.toK, map_mul, map_pow]
    rw [e, hga, hυ, PullbackColumn.expS_pow _ cD, mul_assoc,
      ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero]) (by rw [nt_const_smul, cL, mul_zero]),
      gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, sub_add_cancel]
  have hend := (invariantDeriv_along_endo R d O k B a).2 ι (fun l i => algebraMap R k (u l i))
    (fun l => algebraMap R k (α l)) hα
  have hmap : ∀ (mo : ι →₀ ℕ) (f : PS R 1 d),
      constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo (FB.toK k f)) =
        algebraMap R k (constantCoeff (DmonOf B.G.F u mo f)) := fun mo f => by
    rw [← constantCoeff_map, map_dmonOf]
    rfl
  have hφ : ∀ mo : ι →₀ ℕ, ∃ r ∈ I, constantCoeff (DmonOf (B.FK k) (fun l i => algebraMap R k (u l i)) mo
      ((m : k) • B.hL k h ((N : O) * (c * w0)))) = algebraMap R k r := by
    intro mo
    obtain ⟨t, ht⟩ := hS R d O k B h hh (c * w0) N ι u hβ mo
    refine ⟨(m : R) * (N * t), I.mul_mem_left _ (I.mul_mem_right _ hN), ?_⟩
    rw [smul_eq_C_mul, GE.dmonOf_Cmul, map_mul, constantCoeff_C, ht, map_mul (algebraMap R k) (m : R),
      map_natCast]
  obtain ⟨r, hr, e⟩ := dmonOf_mul_expS_congr R d k B.G.F I ι u _
    (by rw [nt_const_smul, cL, mul_zero]) hφ (ev (n := 1) ![B.A.act a] g * υ ^ m) mo
  have hcong : ∀ mo : ι →₀ ℕ, constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) -
      constantCoeff (DmonOf B.G.F u mo g) ∈ I := by
    intro mo
    have e1 : constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g)) =
        (∏ l, α l ^ mo l) * constantCoeff (DmonOf B.G.F u mo g) := by
      apply hinj
      rw [← hmap, hga, hend, hmap]
      simp only [map_mul, map_prod, map_pow]
    rw [e1, ← sub_one_mul]
    exact I.mul_mem_right _ (prod_pow_sub_one_mem I α hα1 mo)
  have hleib := hL R d B.G.F I ι u _ _ (υ ^ m) hcong mo
  rw [hg] at hleib
  refine exists_eq_of_unit_mul (algebraMap R k) I (P := ∏ l, α l ^ mo l)
    (x := constantCoeff (DmonOf B.G.F u mo (ev (n := 1) ![B.A.act a] g * υ ^ m)) + r)
    (IsUnit.prod_univ_iff.2 fun l => (hαu l).pow _) (prod_pow_sub_one_mem I α hα1 mo) ?_ ?_
  · rw [add_sub_right_comm]
    exact I.add_mem hleib hr
  · unfold FB.nabVal
    rw [PullbackColumn.dpolyOf_monomial_one, ← e]
    simp only [map_prod, map_pow]
    rw [← hend, hG]
    rfl

end GlobalTheory
end
end
