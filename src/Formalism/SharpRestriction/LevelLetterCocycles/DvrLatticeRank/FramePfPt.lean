module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
public import Formalism.SharpRestriction.LevelLetterCocycles.UpPositionOfModels
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfPt
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Zero

open PowerSeries

variable {LL : Type} [Field LL]

theorem framepf_exp_pow_sub_one (E : PowerSeries LL) (h0 : constantCoeff E = 1)
    (hd : PowerSeries.derivative E = E) (p : ℕ) :
    ∃ w : PowerSeries LL, E ^ p - 1 = X * w ∧ constantCoeff w = (p : LL) := by
  have hX1 : X ∣ E - 1 := by
    rw [PowerSeries.X_dvd_iff]
    simp [h0]
  obtain ⟨w1, hw1⟩ := hX1
  have hc1 : constantCoeff w1 = 1 := by
    have h2 : coeff 0 (PowerSeries.derivative E) = coeff 1 E := by
      rw [PowerSeries.coeff_derivative]
      simp
    rw [hd] at h2
    have h1 : coeff 1 (E - 1) = coeff 0 w1 := by
      rw [hw1]
      exact PowerSeries.coeff_succ_X_mul 0 w1
    have h3 : coeff 1 (E - 1) = coeff 1 E := by
      simp [PowerSeries.coeff_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1, h3, ← h2,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
  induction p with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, hwc⟩ := ih
    refine ⟨w * E + w1, ?_, ?_⟩
    · have he : E ^ (k + 1) - 1 = (E ^ k - 1) * E + (E - 1) := by ring
      rw [he, hw, hw1]
      ring
    · simp [hwc, hc1, h0]

end Zero

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)


open PowerSeries in
theorem framepf_lev_q_simple (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ u : PowerSeries LL, W.lev c ζ W.q = X * u ∧ constantCoeff u ≠ 0 := by
  obtain ⟨E, hE0, hEd, hE⟩ := W.lev_π c ζ ⟨1, by simpa using hζ⟩
  obtain ⟨w, hw, hwc⟩ := framepf_exp_pow_sub_one E hE0 hEd PD.p
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have h1 := W.v_l
    rw [h, AddValuation.map_zero] at h1
    simp at h1
  have hp1 : PD.p ≠ 1 := by
    intro h
    have h1 := W.v_l
    rw [h, Nat.cast_one, AddValuation.map_one] at h1
    simp at h1
  have hζ1 : ζ ≠ 1 := by
    intro h
    have h2 := hζ.eq_orderOf
    rw [h, orderOf_one] at h2
    exact hp1 h2
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply]
    exact W.q₀_def
  have hfq : W.lev c ζ letπ * W.lev c ζ W.q = E ^ PD.p - 1 := by
    rw [← map_mul, hq, map_sub, map_pow, map_add (f := _), map_one, hE, mul_pow, ← map_pow, hζp, map_one,
      one_mul]
  set P := W.lev c ζ letπ with hPdef
  have hP : P = C ζ * E - 1 := eq_sub_of_add_eq' hE
  have hPc : constantCoeff P = ζ - 1 := by
    rw [hP]
    simp [hE0]
  have hPne : constantCoeff P ≠ 0 := by
    rw [hPc]
    exact sub_ne_zero.mpr hζ1
  refine ⟨w * P⁻¹, ?_, ?_⟩
  · have hinv : P⁻¹ * P = 1 := PowerSeries.inv_mul_cancel P hPne
    calc W.lev c ζ W.q = (P⁻¹ * P) * W.lev c ζ W.q := by rw [hinv, one_mul]
      _ = P⁻¹ * (E ^ PD.p - 1) := by rw [mul_assoc, hfq]
      _ = X * (w * P⁻¹) := by rw [hw]; ring
  · rw [map_mul, hwc, PowerSeries.constantCoeff_inv, hPc]
    exact mul_ne_zero hp0 (inv_ne_zero (sub_ne_zero.mpr hζ1))

theorem framepf_Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  simp [Formalism.BasicNotions.LocWach.Q, hs]

theorem framepf_Q_at (hs : W.s = 1) (c : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := framepf_lev_q_simple W c ζ hζ
  rw [framepf_Q_eq_q W hs, hu]
  refine ⟨by simp, ?_⟩
  have h1 : PowerSeries.coeff 1 (PowerSeries.X * u) = PowerSeries.coeff 0 u :=
    PowerSeries.coeff_succ_X_mul 0 u
  rw [h1, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact hu0

end Local

theorem framepf_pt_prim (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : IsPrimitiveRoot ζ l := by
  obtain ⟨τs, ⟨-, hroot⟩, -⟩ := hpt
  have hpow : (D.loc l).ζQ 1 ^ l = 1 := by
    have h := (D.loc l).ζQ_succ 0
    rwa [zero_add, (D.loc l).ζQ_zero] at h
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    show _ ∈ K0 K ⊔ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1}
    refine (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ _) ?_
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one]
    exact hpow
  set y : Ks K 1 := ⟨_, hmem⟩ with hydef
  have hyζ : τs y = ζ := hroot y rfl
  have hy1 : y ^ l = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact hpow
  have hy2 : y ≠ 1 := by
    intro h
    apply (D.loc l).ζQ_one
    have h' := congrArg Subtype.val h
    exact h'
  have hprim : IsPrimitiveRoot y l := by
    have ho := orderOf_eq_prime hy1 hy2
    have h0 := IsPrimitiveRoot.orderOf y
    rwa [ho] at h0
  rw [← hyζ]
  exact hprim.map_of_injective τs.injective

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.Imports
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def Phi (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T) :
    (Fin r → LL) →ₗ[LL] T.V ⊗[Qp] BdR where
  toFun d := ∑ k, d k • valAt W T c ζ (rep k)
  map_add' d d' := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a d := by simp [Finset.smul_sum, smul_smul]

theorem Phi_apply (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) {r : ℕ} (rep : Fin r → W.DD T)
    (d : Fin r → LL) : Phi W T c ζ rep d = ∑ k, d k • valAt W T c ζ (rep k) := rfl

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfA
noncomputable section

namespace Formalism.MainNotions.N.Ln34.ModelFPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34

section Ser

variable {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V]

theorem finsum_mem_sub {ι : Type} (S : Submodule LL V) (t : ι → V) (ht : ∀ j, t j ∈ S) :
    ∑ᶠ j, t j ∈ S := by
  classical
  by_cases h : (Function.support t).Finite
  · rw [finsum_eq_sum _ h]
    exact Submodule.sum_mem _ fun j _ => ht j
  · rw [finsum_of_infinite_support h]
    exact Submodule.zero_mem _

theorem serMul_eq_sum (g : PowerSeries LL) (f : ℤ → V) (m : ℤ) (hf : ∀ k < m, f k = 0)
    (i : ℤ) (N : ℕ) (hN : i - m < N) :
    serMul g f i = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (i - j) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hj ⊢
  by_contra hjN
  push_neg at hjN
  apply hj
  rw [hf (i - j) (by omega), smul_zero]

theorem serMul_one (f : ℤ → V) (i : ℤ) : serMul (1 : PowerSeries LL) f i = f i := by
  unfold serMul
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem serMul_mem (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (f : ℤ → V) (hf : ∀ i, f i ∈ S i) (i : ℤ) :
    serMul g f i ∈ S (i - m) := by
  unfold serMul
  apply finsum_mem_sub
  intro j
  by_cases hj : j < m
  · rw [hg j hj, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (hS (by omega) (hf (i - j)))

theorem serMul_inv (S : ℤ → Submodule LL V) (hS : Monotone S) (g : PowerSeries LL) (m : ℕ)
    (hg : ∀ j < m, PowerSeries.coeff j g = 0) (hgm : PowerSeries.coeff m g ≠ 0) (f : ℤ → V)
    (m₀ : ℤ) (hf0 : ∀ k < m₀, f k = 0) (hF : ∀ i, serMul g f (i + m) ∈ S i) (i : ℤ) :
    f i ∈ S i := by
  have key : ∀ i, (∀ i' < i, f i' ∈ S i') → f i ∈ S i := by
    intro i ih
    by_cases hi : i < m₀
    · rw [hf0 i hi]; exact Submodule.zero_mem _
    push_neg at hi
    have hN : i + m - m₀ < (((i + m - m₀).toNat + m + 1 : ℕ) : ℤ) := by omega
    have hsum := serMul_eq_sum g f m₀ hf0 (i + m) ((i + m - m₀).toNat + m + 1) hN
    have hmN : m ∈ Finset.range ((i + m - m₀).toNat + m + 1) := Finset.mem_range.mpr (by omega)
    rw [← Finset.add_sum_erase _ _ hmN] at hsum
    have hrest : ∑ j ∈ (Finset.range ((i + m - m₀).toNat + m + 1)).erase m,
        PowerSeries.coeff j g • f (i + m - j) ∈ S i := by
      refine Submodule.sum_mem _ fun j hj => ?_
      have hjm : j ≠ m := Finset.ne_of_mem_erase hj
      rcases Nat.lt_or_gt_of_ne hjm with hlt | hgt
      · rw [hg j hlt, zero_smul]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (hS (by omega) (ih _ (by omega)))
    have hmain : PowerSeries.coeff m g • f i ∈ S i := by
      have h1 := hF i
      rw [hsum] at h1
      have h2 := Submodule.sub_mem _ h1 hrest
      simp only [add_sub_cancel_right] at h2
      simpa using h2
    exact (Submodule.smul_mem_iff _ hgm).mp hmain
  have hall : ∀ n : ℕ, ∀ i, i < m₀ + n → f i ∈ S i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      rw [hf0 i (by simpa using hi)]
      exact Submodule.zero_mem _
    | succ n ihn =>
      intro i hi
      apply key
      intro i' hi'
      exact ihn i' (by push_cast at hi; omega)
  exact hall ((i - m₀).toNat + 1) i (by omega)

end Ser

section Lev

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem lev_letE (c : ZMod n) (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h1 : W.lev c ζ (1 - letE c : LetA O n) = 0 :=
    W.lev_letter c ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h1
  exact h1.symm

theorem levN_eq_serMul (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T))
    (k : ℤ) : W.levN T c ζ (a • x) k = serMul (W.lev c ζ a) (W.levN T c ζ x) k :=
  W.levN_smul T c ζ a x k

theorem levN_letE (T : LocLat G Qp LL O) (c : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ) :
    W.levN T c ζ ((letE c : LetA O n) • x) k = W.levN T c ζ x k := by
  rw [levN_eq_serMul, lev_letE, serMul_one]

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  show (W.φA ^ (W.s - 1)) W.q = W.q
  rw [hs, Nat.sub_self, pow_zero]
  rfl

theorem levQ_pt (hs : W.s = 1) (i : ZMod n) (ζ : LL) (hζ : ζ ^ PD.p = 1) (hζ1 : ζ ≠ 1) :
    PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ∧ PowerSeries.coeff 1 (W.lev i ζ W.Q) ≠ 0 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hprim : IsPrimitiveRoot ζ (PD.p ^ 1) := by
    have h := IsPrimitiveRoot.orderOf ζ
    rw [orderOf_eq_prime hζ hζ1] at h
    rwa [pow_one]
  obtain ⟨E, hE0, hED, hE⟩ := W.lev_π i ζ ⟨1, hprim⟩
  have hprod : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext j
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q]
    exact W.q₀_def
  have hl := congrArg (W.lev i ζ) hprod
  rw [map_mul, map_sub, map_pow, map_add (f := _), map_one, hE] at hl
  rw [Q_eq_q W hs]
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have := W.v_l
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_coe this
  have ha0 : PowerSeries.constantCoeff (W.lev i ζ letπ) = ζ - 1 := by
    have h := congrArg PowerSeries.constantCoeff hE
    rw [map_add (f := _), map_one, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one] at h
    linear_combination h
  have hz : ζ - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hc0 : PowerSeries.constantCoeff (W.lev i ζ W.q) = 0 := by
    have h := congrArg PowerSeries.constantCoeff hl
    rw [map_mul, map_sub, map_one, map_pow, map_mul, PowerSeries.constantCoeff_C, hE0, mul_one,
      hζ, sub_self, ha0] at h
    exact (mul_eq_zero.1 h).resolve_left hz
  refine ⟨hc0, ?_⟩
  obtain ⟨b', hb'⟩ := PowerSeries.X_dvd_iff.2 hc0
  have hEp : PowerSeries.coeff 1 (E ^ PD.p) = (PD.p : LL) := by
    have hd : PowerSeries.derivative (R := LL) (E ^ PD.p) = (PD.p : LL) • E ^ PD.p := by
      rw [Derivation.leibniz_pow, hED, smul_eq_mul, ← pow_succ, Nat.sub_add_cancel PD.hp.one_lt.le,
        Nat.cast_smul_eq_nsmul]
    have h := congrArg (PowerSeries.coeff 0) hd
    have hc : PowerSeries.coeff 0 (E ^ PD.p) = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hE0, one_pow]
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_smul, hc] at h
    simpa using h
  have h1 := congrArg (PowerSeries.coeff 1) hl
  rw [hb', mul_left_comm, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, ha0, mul_pow, ← map_pow, hζ, map_one, one_mul, map_sub, hEp, PowerSeries.coeff_one,
    if_neg one_ne_zero, sub_zero] at h1
  rw [hb', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  intro h0
  rw [h0, mul_zero] at h1
  exact hp0 h1.symm

end Lev

end Formalism.MainNotions.N.Ln34.ModelFPf

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfA
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UnivLinkPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem univLinkPf_PiNS_anti (T : LocLat G Qp LL O) (π' : LetA O n) {j k : ℕ} (h : j ≤ k)
    {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ PiNS W T π' j := by
  rw [PiNS, Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, hx2⟩ := hx
  refine ⟨⟨π' ^ (k - j) • y, Submodule.smul_mem _ _ hy, ?_⟩, hx2⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem univLinkPf_InvS_anti (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    {j k : ℕ} (h : j ≤ k) {x : W.DD T} (hx : x ∈ InvS W T π' Eπ h' k c) : x ∈ InvS W T π' Eπ h' j c := by
  rw [InvS, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  exact ⟨hx.1, univLinkPf_PiNS_anti W T π' h hx.2⟩

theorem univLinkPf_cocycle {T : LocLat G Qp LL O} {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    W.γD T W.gamK y - y = W.φD T z - z := by
  have h1 := ((Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mp h).1
  try simp only [herrCocycles, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply] at h1
  rw [← sub_eq_zero, sub_eq_add_neg]
  exact h1

theorem univLinkPf_cocycleΔ {T : LocLat G Qp LL O} {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    ∀ δ ∈ W.DelF, W.γD T δ y = y ∧ W.γD T δ z = z := ((Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mp h).2

theorem univLinkPf_mem_Z1DΔ {T : LocLat G Qp LL O} (y z : W.DD T) (hy : ∀ δ ∈ W.DelF, W.γD T δ y = y)
    (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) (h : W.γD T W.gamK y - y = W.φD T z - z) :
    (y, z) ∈ W.wachCocyclesDelta T := by
  refine (Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mpr ⟨?_, fun δ hδ => ⟨hy δ hδ, hz δ hδ⟩⟩
  try simp only [herrCocycles, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact h

section Map

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

theorem univLinkPf_map_DelS {x : W.DD T₁} (hx : ∀ δ ∈ W.DelF, W.γD T₁ δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F x) = W.map F x := by
  intro δ hδ
  rw [← W.map_γ F δ x, hx δ hδ]

theorem univLinkPf_map_PiNS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (π' : LetA O n) (k : ℕ)
    {x : W.DD T₁} (hx : x ∈ PiNS W T₁ π' k) : W.map F x ∈ PiNS W T₂ π' k := by
  have hDel : ∀ {T : LocLat G Qp LL O} {x : W.DD T}, x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro T x
    simp [DelS, Submodule.mem_iInf, sub_eq_zero]
  rw [PiNS, Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, hx2⟩ := hx
  refine ⟨⟨W.map F y, W.map_N F h1 h2 y hy, ?_⟩, hDel.mpr (univLinkPf_map_DelS W F (hDel.mp hx2))⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  exact ((Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul _ _).symm

theorem univLinkPf_map_φspan (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (c : ZMod n) {x : W.DD T₁}
    (hx : x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₁ (W.Nl T₁ c)) : W.map F x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ c) := by
  have hNl : ∀ y ∈ W.Nl T₁ c, W.map F y ∈ W.Nl T₂ c := by
    intro y hy
    unfold Formalism.BasicNotions.LocWach.Nl at hy ⊢
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨W.map F z, W.map_N F h1 h2 z hz, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact ((Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul _ _).symm
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx ⊢
  have hm : (Formalism.MainNotions.DeltaInvariantLattices.mapA W F) x ∈ Submodule.map (Formalism.MainNotions.DeltaInvariantLattices.mapA W F)
      (Submodule.span (LetA O n) (W.φD T₁ '' (W.Nl T₁ c : Set (W.DD T₁)))) := Submodule.mem_map_of_mem hx
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨W.map F y, hNl y hy, (W.map_φ F y).symm⟩

theorem univLinkPf_map_LamPS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) {x : W.DD T₁} (hx : x ∈ LamPS W T₁ Eπ h' c) : W.map F x ∈ LamPS W T₂ Eπ h' c := by
  have hDel : ∀ {T : LocLat G Qp LL O} {x : W.DD T}, x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro T x
    simp [DelS, Submodule.mem_iInf, sub_eq_zero]
  have hsm : ∀ (a : LetA O n) (y : W.DD T₁), W.map F (a • y) = a • W.map F y :=
    fun a y => (Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul a y
  rw [LamPS, Submodule.mem_inf, Submodule.mem_inf] at hx ⊢
  obtain ⟨⟨hA, hB⟩, hC⟩ := hx
  refine ⟨⟨?_, hDel.mpr (univLinkPf_map_DelS W F (hDel.mp hB))⟩, ?_⟩
  · rw [Submodule.restrictScalars_mem, Submodule.mem_comap] at hA ⊢
    have hφ := univLinkPf_map_φspan W F h1 h2 (c - 1) hA
    simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply] at hφ ⊢
    rw [hsm] at hφ
    exact hφ
  · rw [letS, LinearMap.mem_ker] at hC ⊢
    simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hC ⊢
    rw [← hsm, ← map_sub, hC, map_zero]

theorem univLinkPf_map_InvS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (π' Eπ : LetA O n) (h' k : ℕ)
    (c : ZMod n) {x : W.DD T₁} (hx : x ∈ InvS W T₁ π' Eπ h' k c) : W.map F x ∈ InvS W T₂ π' Eπ h' k c := by
  rw [InvS, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  refine ⟨univLinkPf_map_LamPS W F h1 h2 Eπ h' c hx.1, ?_⟩
  have hP := univLinkPf_map_PiNS W F h1 h2 π' k hx.2
  simp only [LinearMap.sub_apply, LinearMap.id_apply] at hP ⊢
  rw [map_sub, W.map_γ] at hP
  exact hP

theorem univLinkPf_map_Z1DΔ {y z : W.DD T₁} (h : (y, z) ∈ W.wachCocyclesDelta T₁) :
    (W.map F y, W.map F z) ∈ W.wachCocyclesDelta T₂ := by
  have hc := univLinkPf_cocycle W h
  have hd := univLinkPf_cocycleΔ W h
  apply univLinkPf_mem_Z1DΔ W
  · exact univLinkPf_map_DelS W F (fun δ hδ => (hd δ hδ).1)
  · exact univLinkPf_map_DelS W F (fun δ hδ => (hd δ hδ).2)
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, hc]

end Map

section Frame

variable (T : LocLat G Qp LL O)

theorem univLinkPf_toLA_eq (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    toLA W T π' c S = (toLA W T π' c ⊤).comp (TensorProduct.map LinearMap.id (Submodule.inclusion le_top)) := by
  unfold toLA
  rw [← TensorProduct.map_comp, LinearMap.comp_id, Submodule.subtype_comp_inclusion]

theorem univLinkPf_LamLA_le (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  refine Submodule.comap_mono ?_
  rw [univLinkPf_toLA_eq W T π' c S]
  exact LinearMap.range_comp_le_range _ _

theorem univLinkPf_InvL_le (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ InvL W T Pt π' Eπ h' c ⊤ := by
  unfold InvL
  exact inf_le_inf_right _ (univLinkPf_LamLA_le W T π' Eπ h' c S)

theorem univLinkPf_basis [StrongRankCondition O] (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c))
    [Module.Finite O (IIrest W T Pt π' Eπ h' c S)] [Module.Free O (IIrest W T Pt π' Eπ h' c S)] :
    ∃ xb : Fin (finrank O (IIrest W T Pt π' Eπ h' c S)) → ↥(InvL W T Pt π' Eπ h' c S),
      ∀ x : ↥(InvL W T Pt π' Eπ h' c S), ∃ o : Fin (finrank O (IIrest W T Pt π' Eπ h' c S)) → O,
        (x : LA W T π' c) - ∑ i, o i • (xb i : LA W T π' c) ∈ piNL W T Pt π' Eπ h' c 1 := by
  classical
  let b := Module.finBasis O (IIrest W T Pt π' Eπ h' c S)
  choose xb hxb using fun i => Submodule.Quotient.mk_surjective _ (b i)
  refine ⟨xb, fun x => ⟨fun i => b.repr (Submodule.Quotient.mk x) i, ?_⟩⟩
  have h : (Submodule.Quotient.mk x : IIrest W T Pt π' Eπ h' c S) =
      Submodule.Quotient.mk (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) := by
    rw [show (Submodule.Quotient.mk (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) :
        IIrest W T Pt π' Eπ h' c S) =
        Submodule.mkQ _ (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) from rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.mkQ_apply, hxb]
    exact (b.sum_repr _).symm
  rw [Submodule.Quotient.eq] at h
  simpa using h

theorem univLinkPf_JP {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M : ℕ}
    {c : ZMod n} {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (y : ↥(LamPS W T Eπ h' c))
    (hJ : Submodule.Quotient.mk y = (0 : QLamP W T π' Eπ h' M c)) : (y : W.DD T) ∈ PiNS W T π' M := by
  refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) y.1 y.2 ?_ (Submodule.zero_mem _)
  show α T 0 = _
  rw [map_zero]
  exact hJ.symm

theorem univLinkPf_transport {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M : ℕ}
    {c : ZMod n} {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM : 1 ≤ M) {k r : ℕ}
    (X : ↥(LamLA W T π' Eπ h' c ⊤)) (Y : ↥(LamPS W T Eπ h' c))
    (hX : α T X = Submodule.Quotient.mk Y)
    (Xj : Fin k → ↥(LamLA W T π' Eπ h' c ⊤)) (Yj : Fin k → ↥(LamPS W T Eπ h' c))
    (hXj : ∀ j, α T (Xj j) = Submodule.Quotient.mk (Yj j))
    (Xb : Fin r → ↥(LamLA W T π' Eπ h' c ⊤)) (Yb : Fin r → ↥(LamPS W T Eπ h' c))
    (hXb : ∀ i, α T (Xb i) = Submodule.Quotient.mk (Yb i)) (o : Fin r → O)
    (hrel : (X : LA W T π' c) - ∑ j, (Xj j : LA W T π' c) - ∑ i, o i • (Xb i : LA W T π' c) ∈
      piNL W T Pt π' Eπ h' c 1) :
    (Y : W.DD T) - ∑ j, (Yj j : W.DD T) - ∑ i, o i • (Yb i : W.DD T) ∈ PiNS W T π' 1 := by
  have h3 := (hMF.2.2.1 1 le_rfl hM).1
  have hαx : α T (X - ∑ j, Xj j - ∑ i, o i • Xb i) =
      Submodule.Quotient.mk (Y - ∑ j, Yj j - ∑ i, o i • Yb i) := by
    rw [show (Submodule.Quotient.mk (Y - ∑ j, Yj j - ∑ i, o i • Yb i) : QLamP W T π' Eπ h' M c) =
      Submodule.mkQ _ (Y - ∑ j, Yj j - ∑ i, o i • Yb i) from rfl]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, Submodule.mkQ_apply, hX, hXj, hXb]
  have hmem := h3 ((X - ∑ j, Xj j - ∑ i, o i • Xb i : ↥(LamLA W T π' Eπ h' c ⊤)) : LA W T π' c)
    (X - ∑ j, Xj j - ∑ i, o i • Xb i).2
    ((Y - ∑ j, Yj j - ∑ i, o i • Yb i : ↥(LamPS W T Eπ h' c)) : W.DD T)
    (Y - ∑ j, Yj j - ∑ i, o i • Yb i).2 hαx (by simpa using hrel)
  simpa using hmem

end Frame

end Local

end Formalism.MainNotions.N.Ln34.UnivLinkPf

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.RankLinkProof
noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankLink

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem toLA_range_le (T : LocLat G Qp LL O) (π' : LetA O n) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) :
    LinearMap.range (toLA W T π' c S) ≤ LinearMap.range (toLA W T π' c ⊤) := by
  have e : toLA W T π' c S =
      toLA W T π' c ⊤ ∘ₗ TensorProduct.map LinearMap.id (Submodule.inclusion le_top) := by
    apply TensorProduct.ext'
    intro x s
    simp [toLA, TensorProduct.map_tmul]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem lamLA_le (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (S : Submodule O (LcQ W T π' c)) : LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  exact Submodule.comap_mono (toLA_range_le W T π' c S)

theorem invL_le (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold InvL
  exact le_trans inf_le_left (lamLA_le W T π' Eπ h' c S)

def iota (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    IIrest W T Pt π' Eπ h' c S →ₗ[O] Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c :=
  Submodule.mapQ _ _ (Submodule.inclusion (invL_le W T Pt π' Eπ h' c S)) (fun x hx => by
    simpa [Submodule.mem_comap] using hx)

theorem iota_inj (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    Function.Injective (iota W T Pt π' Eπ h' c S) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker] at hy
  unfold iota at hy
  rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  simpa [Submodule.mem_comap] using hy

theorem rank_link_of_model [IsDomain O] [IsPrincipalIdealRing O] (T : LocLat G Qp LL O)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    (hQ : ModelQ W T Pt π' Eπ h' c) (hR : SecondRankCount W T Pt π' Eπ h' c) : SecondPropositionFree W T Pt π' Eπ h' c := by
  intro S
  obtain ⟨hfin, htf⟩ := hQ
  have hinj := iota_inj W T Pt π' Eπ h' c S
  haveI : Module.Finite O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := hfin
  haveI : IsNoetherian O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) :=
    isNoetherian_of_isNoetherianRing_of_finite O _
  haveI hfinI : Module.Finite O (IIrest W T Pt π' Eπ h' c S) :=
    Module.Finite.of_injective (iota W T Pt π' Eπ h' c S) hinj
  haveI : NoZeroSMulDivisors O (Formalism.MainNotions.N.Ln34.QL W T Pt π' Eπ h' c) := by
    refine ⟨fun {a q} h => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr (htf a q ha h)
  haveI : NoZeroSMulDivisors O (IIrest W T Pt π' Eπ h' c S) :=
    Function.Injective.noZeroSMulDivisors _ hinj (map_zero _) (fun a x => map_smul _ a x)
  exact ⟨hfinI, Module.free_of_finite_type_torsion_free', hR S⟩

end Local

set_option maxHeartbeats 1000000 in
theorem rank_link_holds : Formalism.MainNotions.N.Ln34.SecondPropositionOfRank := by
  intro D HW hM hR l _ hl K LL hG π' E hp T h' hh hC hJ c
  haveI := Formalism.MainNotions.N.Ln34.GenPf.isDVR (D.loc l) LL
  exact rank_link_of_model _ T _ π' _ h' c (hM l hl K LL hG π' E hp h' hh T hC hJ c)
    (hR l hl K LL hG π' E hp T h' hh hC hJ c)

end Formalism.MainNotions.N.Ln34.RankLink

end
end
