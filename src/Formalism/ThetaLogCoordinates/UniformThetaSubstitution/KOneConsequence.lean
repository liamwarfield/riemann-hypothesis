module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.GaussElementarySymmetric
public import Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.FinsuppStepInduction
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MinorProdBlockDegree
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormNatCastLeOfDvd
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EDecomp
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLeOfDvd
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EntryATwoAndB
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EJoint
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MPlaces

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EntryAOneParity
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace ValuationParity

def par (ν : ℕ) : ZMod (2 * ν) →+* ZMod 2 := ZMod.castHom (Dvd.intro ν rfl) (ZMod 2)

lemma par_eq {ν : ℕ} [NeZero ν] (x : ZMod (2 * ν)) : par ν x = ((x.val : ℕ) : ZMod 2) := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  show ZMod.cast x = _
  exact ZMod.cast_eq_val x

lemma val_mod_two {ν : ℕ} [NeZero ν] (x : ZMod (2 * ν)) : x.val % 2 = (par ν x).val := by
  rw [par_eq, ZMod.val_natCast]

lemma par_odd {ν : ℕ} (y : ZMod (2 * ν)) : par ν (1 + 2 * y) = 1 := by
  rw [map_add (f := _), map_one, map_mul]
  have h2 : par ν 2 = 0 := by
    rw [map_ofNat]
    rfl
  rw [h2, zero_mul, add_zero]

lemma val_odd {ν : ℕ} [NeZero ν] {x y : ZMod (2 * ν)} (h : x = 1 + 2 * y) : x.val % 2 = 1 := by
  rw [val_mod_two, h, par_odd]
  rfl

lemma parity_ne {ν : ℕ} [NeZero ν] {s s' y : ZMod (2 * ν)} (h : s' - s = 1 + 2 * y) :
    s'.val % 2 ≠ s.val % 2 := by
  rw [val_mod_two, val_mod_two]
  have hs : par ν s' = par ν s + 1 := by
    rw [show s' = s + (1 + 2 * y) by rw [← h]; ring, map_add (f := _), par_odd]
  rw [hs]
  generalize par ν s = a
  revert a
  decide

lemma isLeast_val {n : ℕ} [NeZero n] (s s' : ZMod n) (h : 1 ≤ (s' - s).val) :
    IsLeast {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} (s' - s).val := by
  refine ⟨⟨h, by rw [ZMod.natCast_zmod_val]; ring⟩, ?_⟩
  rintro e ⟨_, he⟩
  have he' : ((e : ℕ) : ZMod n) = s' - s := by rw [← he]; ring
  rw [← he', ZMod.val_natCast]
  exact Nat.mod_le _ _

lemma charge_exists (hL : ChargeLemma) {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (hp : 1 ≤ p)
    (φ : PhiI ν r0 r1 E) :
    ∃ s s' : ZMod (2 * ν), ((s = pairFirst φ ∧ s' = pairSecond φ) ∨ (s = pairSecond φ ∧ s' = pairFirst φ)) ∧
      (s' - s).val % 2 = 1 ∧ s'.val % 2 ≠ s.val % 2 ∧
      p ^ (s' - s).val ≤ dAof p φ (s, φ.2.2.2.2) := by
  haveI : NeZero (2 * ν) := ⟨by have := NeZero.ne ν; omega⟩
  have hA1 : p ^ (1 + 2 * φ.2.1.val) ≤ dAof p φ (pairFirst φ, φ.2.2.2.2) := by
    simp only [dAof, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_right _ _
  have hA2 : p ^ (2 * φ.2.2.1.val) ≤ dAof p φ (pairSecond φ, φ.2.2.2.2) := by
    simp only [dAof, Finsupp.add_apply, Finsupp.single_eq_same]
    exact Nat.le_add_left _ _
  by_cases hij : φ.2.2.1.val ≤ φ.2.1.val
  · have hodd : pairSecond φ - pairFirst φ = 1 + 2 * ((φ.2.1.val : ZMod (2 * ν)) - (φ.2.2.1.val : ZMod (2 * ν))) := by
      unfold pairFirst pairSecond
      ring
    have hv := val_odd hodd
    have heq : pairFirst φ + ((1 + 2 * φ.2.1.val : ℕ) : ZMod (2 * ν)) =
        pairSecond φ + ((2 * φ.2.2.1.val : ℕ) : ZMod (2 * ν)) := by
      unfold pairFirst pairSecond
      push_cast
      ring
    have hd := hL (2 * ν) (pairFirst φ) (pairSecond φ) (1 + 2 * φ.2.1.val) (2 * φ.2.2.1.val) _ (by omega) heq
      (isLeast_val (pairFirst φ) (pairSecond φ) (by omega))
    exact ⟨pairFirst φ, pairSecond φ, Or.inl ⟨rfl, rfl⟩, hv, parity_ne hodd,
      le_trans (Nat.pow_le_pow_right hp hd) hA1⟩
  · have hodd : pairFirst φ - pairSecond φ =
        1 + 2 * ((φ.2.2.1.val : ZMod (2 * ν)) - (φ.2.1.val : ZMod (2 * ν)) - 1) := by
      unfold pairFirst pairSecond
      ring
    have hv := val_odd hodd
    have heq : pairSecond φ + ((2 * φ.2.2.1.val : ℕ) : ZMod (2 * ν)) =
        pairFirst φ + ((1 + 2 * φ.2.1.val : ℕ) : ZMod (2 * ν)) := by
      unfold pairFirst pairSecond
      push_cast
      ring
    have hd := hL (2 * ν) (pairSecond φ) (pairFirst φ) (2 * φ.2.2.1.val) (1 + 2 * φ.2.1.val) _ (by omega) heq
      (isLeast_val (pairSecond φ) (pairFirst φ) (by omega))
    exact ⟨pairSecond φ, pairFirst φ, Or.inr ⟨rfl, rfl⟩, hv, parity_ne hodd,
      le_trans (Nat.pow_le_pow_right hp hd) hA2⟩

lemma sum_charge {Φ S : Type} [Fintype Φ] [DecidableEq S] (TT : Finset S) (R : Finset ℕ)
    (c : Φ → S × ℕ) (w : Φ → ℕ) (h : ∀ φ, w φ ≠ 0 → (c φ).1 ∈ TT ∧ (c φ).2 ∈ R) :
    ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0) = ∑ φ, w φ := by
  calc ∑ s ∈ TT, ∑ e ∈ R, ∑ φ, (if c φ = (s, e) then w φ else 0)
      = ∑ s ∈ TT, ∑ φ, ∑ e ∈ R, (if c φ = (s, e) then w φ else 0) :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ φ, ∑ s ∈ TT, ∑ e ∈ R, (if c φ = (s, e) then w φ else 0) := Finset.sum_comm
    _ = ∑ φ, w φ := by
      refine Finset.sum_congr rfl fun φ _ => ?_
      by_cases hw : w φ = 0
      · simp [hw]
      obtain ⟨h1, h2⟩ := h φ hw
      rw [Finset.sum_eq_single (c φ).1]
      · rw [Finset.sum_eq_single (c φ).2]
        · simp
        · intro e _ he
          rw [if_neg]
          intro hc
          apply he
          rw [hc]
        · intro h'
          exact absurd h2 h'
      · intro s _ hs
        refine Finset.sum_eq_zero fun e _ => ?_
        rw [if_neg]
        intro hc
        apply hs
        rw [hc]
      · intro h'
        exact absurd h1 h'

lemma level_le {ν r0 r1 E : ℕ} [NeZero ν] (p : ℕ) (e : TpV ν r1 → ℕ) (α : PhiI ν r0 r1 E → ℕ)
    (β : KapI ν r1 E →₀ ℕ)
    (hτ : ∀ τ, ∑ φ, α φ * dAof p φ τ + ∑ k, β k * dBof p k τ ≤ e τ)
    (c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ)
    (hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2)) (s : ZMod (2 * ν)) (e' : ℕ) :
    p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
      ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0) ≤ alN e s := by
  have hφ : ∀ φ, (if c φ = (s, e') then p ^ (2 * e' + 1) * α φ else 0) ≤
      ∑ b, α φ * dAof p φ (s, b) := by
    intro φ
    split_ifs with h
    · have h1 := hc φ
      simp only [h] at h1
      calc p ^ (2 * e' + 1) * α φ = α φ * p ^ (2 * e' + 1) := mul_comm _ _
        _ ≤ α φ * dAof p φ (s, φ.2.2.2.2) := Nat.mul_le_mul_left _ h1
        _ ≤ ∑ b, α φ * dAof p φ (s, b) :=
          Finset.single_le_sum (f := fun b => α φ * dAof p φ (s, b)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    · exact Nat.zero_le _
  have hk : ∀ k : KapI ν r1 E, (if (k.1, k.2.1.val) = (s, e') then p ^ (2 * e' + 1) * β k else 0) ≤
      ∑ b, β k * dBof p k (s, b) := by
    intro k
    split_ifs with h
    · simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      calc p ^ (2 * e' + 1) * β k = β k * dBof p k (s, k.2.2) := by
            rw [← h1, ← h2]
            simp [dBof, mul_comm]
        _ ≤ ∑ b, β k * dBof p k (s, b) :=
          Finset.single_le_sum (f := fun b => β k * dBof p k (s, b)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ _)
    · exact Nat.zero_le _
  calc p ^ (2 * e' + 1) * ((∑ φ, if c φ = (s, e') then α φ else 0) +
        ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0)
      = (∑ φ, if c φ = (s, e') then p ^ (2 * e' + 1) * α φ else 0) +
        ∑ k : KapI ν r1 E, (if (k.1, k.2.1.val) = (s, e') then p ^ (2 * e' + 1) * β k else 0) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_ite, mul_zero]
    _ ≤ (∑ φ, ∑ b, α φ * dAof p φ (s, b)) + ∑ k : KapI ν r1 E, ∑ b, β k * dBof p k (s, b) :=
        add_le_add (Finset.sum_le_sum fun φ _ => hφ φ) (Finset.sum_le_sum fun k _ => hk k)
    _ = ∑ b, ((∑ φ, α φ * dAof p φ (s, b)) + ∑ k, β k * dBof p k (s, b)) := by
        rw [Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
    _ ≤ ∑ b, e (s, b) := Finset.sum_le_sum fun b _ => hτ (s, b)
    _ = alN e s := rfl

end ValuationParity


open ValuationParity in
theorem entryExcessBound_of (hS : EntryStar) (hC : HitsCapPos) (hA : ExcessGainBound) (hL : ChargeLemma) : EntryExcessBound := by
  intro K _ _ p ν r0 r1 C _ u F TT ξ e l sf T I hyp
  rcases hS K p ν r0 r1 C u F TT ξ e l sf T I hyp with h0 | ⟨E, α, β, hαTT, hβTT, hτ, hhasse, hbound⟩
  · rw [h0, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  classical
  have hp : 2 < p := hyp.2.1
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hcharge : ∀ φ : PhiI ν r0 r1 E, ∃ s s' : ZMod (2 * ν),
      ((s = pairFirst φ ∧ s' = pairSecond φ) ∨ (s = pairSecond φ ∧ s' = pairFirst φ)) ∧
      (s' - s).val % 2 = 1 ∧ s'.val % 2 ≠ s.val % 2 ∧
      p ^ (s' - s).val ≤ dAof p φ (s, φ.2.2.2.2) :=
    fun φ => ValuationParity.charge_exists hL p (by omega) φ
  choose sφ s'φ hor hodd hpar hle using hcharge
  obtain ⟨c, hcdef⟩ : ∃ c : PhiI ν r0 r1 E → ZMod (2 * ν) × ℕ,
      ∀ φ, c φ = (sφ φ, ((s'φ φ - sφ φ).val - 1) / 2) := ⟨_, fun _ => rfl⟩
  have hc2 : ∀ φ, 2 * (c φ).2 + 1 = (s'φ φ - sφ φ).val := by
    intro φ
    have := hodd φ
    rw [hcdef]
    omega
  have hc1 : ∀ φ, (c φ).1 = sφ φ := fun φ => by rw [hcdef]
  have hc : ∀ φ, p ^ (2 * (c φ).2 + 1) ≤ dAof p φ ((c φ).1, φ.2.2.2.2) := fun φ => by
    rw [hc2, hc1]
    exact hle φ
  have hsTT : ∀ φ, α φ ≠ 0 → sφ φ ∈ TT ∧ s'φ φ ∈ TT := by
    intro φ hα
    obtain ⟨h1, h2⟩ := hαTT φ hα
    rcases hor φ with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · exact ⟨hs1 ▸ h1, hs2 ▸ h2⟩
    · exact ⟨hs1 ▸ h2, hs2 ▸ h1⟩
  obtain ⟨Ee, hEe⟩ : ∃ Ee : Finset ℕ, Ee = (Finset.univ.image fun φ => (c φ).2) ∪
      (Finset.univ.image fun k : KapI ν r1 E => k.2.1.val) := ⟨_, rfl⟩
  obtain ⟨chN, hchN⟩ : ∃ chN : ZMod (2 * ν) → ℕ → ℕ,
      ∀ s e', chN s e' = ∑ φ, if c φ = (s, e') then α φ else 0 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨iN, hiN⟩ : ∃ iN : ZMod (2 * ν) → ℕ → ℕ,
      ∀ s e', iN s e' = ∑ k : KapI ν r1 E, if (k.1, k.2.1.val) = (s, e') then β k else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hlev : ∀ s e', p ^ (2 * e' + 1) * (chN s e' + iN s e') ≤ alN e s := fun s e' => by
    rw [hchN, hiN]
    exact ValuationParity.level_le p e α β hτ c hc s e'
  have hcapN : ∀ s e', iN s e' ≤ capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) := by
    intro s e'
    by_contra hlt
    push_neg at hlt
    apply hhasse
    refine hC K (ZMod (2 * ν)) (KapI ν r1 E) r0 r1 C l sf T I
      (fun k => k.1 + ((2 * k.2.1.val + 1 : ℕ) : ZMod (2 * ν)))
      (fun k a => ξ k.1 a ^ (p ^ (2 * k.2.1.val + 1))) (fun k => k.2.2)
      (Finset.univ.filter fun k : KapI ν r1 E => (k.1, k.2.1.val) = (s, e'))
      (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) ?_ ?_ β ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hk
      rw [hk.1, hk.2]
    · intro k hk k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hk hk'
      funext a
      rw [hk.1, hk.2, hk'.1, hk'.2]
    · rw [hiN, ← Finset.sum_filter] at hlt
      exact hlt
  have hcoreA := hA (2 * ν) (p : ℝ) TT (dSet TT) (fun s => (alN e s : ℝ)) (fun s => (capN sf s : ℝ))
    (deLoss p r0 r1 TT (alN e) (lsN l sf))
    (gamP p * ∑ s ∈ TT, (alN e s : ℝ) - (∑ φ, (α φ : ℝ)) - (∑ k, (β k : ℝ)) -
      deLoss p r0 r1 TT (alN e) (lsN l sf))
    (fun s e' => (iN s e' : ℝ)) (fun s e' => (chN s e' : ℝ)) Ee hp1
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (fun _ _ => Nat.cast_nonneg _) ?hE ?hD ?hmain ?h6 ?h7
  case hE =>
    intro s e' he'
    constructor
    · show (iN s e' : ℝ) = 0
      rw [hiN, Nat.cast_eq_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg]
      intro hk
      apply he'
      simp only [Prod.mk.injEq] at hk
      rw [hEe, ← hk.2]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · show (chN s e' : ℝ) = 0
      rw [hchN, Nat.cast_eq_zero]
      refine Finset.sum_eq_zero fun φ _ => ?_
      rw [if_neg]
      intro hφ
      apply he'
      have he2 : (c φ).2 = e' := by rw [hφ]
      rw [hEe, ← he2]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  case hD =>
    intro s e' hn
    show (chN s e' : ℝ) = 0
    rw [hchN, Nat.cast_eq_zero]
    refine Finset.sum_eq_zero fun φ _ => ?_
    split_ifs with hφ
    · by_contra hα
      apply hn
      obtain ⟨h1, h2⟩ := hsTT φ hα
      have hs : sφ φ = s := by rw [← hc1, hφ]
      have he : (c φ).2 = e' := by rw [hφ]
      rw [dSet, Finset.mem_image]
      refine ⟨s'φ φ, Finset.mem_filter.mpr ⟨h2, ?_⟩, ?_⟩
      · rw [← hs]
        exact hpar φ
      · rw [← hs, ← hc2, he]
    · rfl
  case hmain =>
    have hsumch : ∑ s ∈ TT, ∑ e' ∈ Ee, (chN s e' : ℝ) = ∑ φ, (α φ : ℝ) := by
      have h := ValuationParity.sum_charge TT Ee c (fun φ => α φ) (fun φ hα => ⟨by rw [hc1]; exact (hsTT φ hα).1,
        by rw [hEe]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩)
      simp only [← hchN] at h
      exact_mod_cast h
    have hsumi : ∑ s ∈ TT, ∑ e' ∈ Ee, (iN s e' : ℝ) = ∑ k, (β k : ℝ) := by
      have h := ValuationParity.sum_charge TT Ee (fun k : KapI ν r1 E => (k.1, k.2.1.val)) (fun k => β k)
        (fun k hk => ⟨hβTT k hk, by
          rw [hEe]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩)
      simp only [← hiN] at h
      exact_mod_cast h
    show gamP (p : ℝ) * ∑ s ∈ TT, (alN e s : ℝ) - ∑ s ∈ TT, ∑ e' ∈ Ee, (chN s e' : ℝ) -
      ∑ s ∈ TT, ∑ e' ∈ Ee, (iN s e' : ℝ) - deLoss p r0 r1 TT (alN e) (lsN l sf) ≤ _
    rw [hsumch, hsumi]
  case h6 =>
    intro s _ e' _
    show (chN s e' : ℝ) + (iN s e' : ℝ) ≤ (alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1)
    rw [le_div_iff₀ (pow_pos (by positivity) _)]
    have h := hlev s e'
    rw [mul_comm] at h
    exact_mod_cast h
  case h7 =>
    intro s _ e' _
    show (iN s e' : ℝ) ≤ min ((alN e s : ℝ) / (p : ℝ) ^ (2 * e' + 1))
      ((capN sf (s + ((2 * e' + 1 : ℕ) : ZMod (2 * ν))) : ℝ))
    apply le_min
    · rw [le_div_iff₀ (pow_pos (by positivity) _)]
      have h := hlev s e'
      have h' : iN s e' * p ^ (2 * e' + 1) ≤ alN e s := by
        rw [mul_comm]
        exact le_trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) h
      exact_mod_cast h'
    · exact_mod_cast hcapN s e'
  refine le_trans hbound (Real.rpow_le_rpow_of_exponent_le hp1.le ?_)
  linarith [hcoreA]

end Formalism.InvariantFactorPaths.G7
end
end

section -- merged from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ABArith
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.GrowthSums (gamP rhoP gainG excessGain)

theorem lgN_mono (p : ℕ) {x y : ℕ} (h : x ≤ y) : lgN p x ≤ lgN p y := by
  unfold lgN
  split_ifs with h1 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.succ_le_succ (Nat.log_mono_right h)

theorem digits_sum_le_lgN (p m : ℕ) (hp : 1 < p) :
    (Nat.digits p m).sum ≤ (p - 1) * lgN p m := by
  have hlen : (Nat.digits p m).length = lgN p m := by
    unfold lgN
    split_ifs with h
    · simp [h]
    · exact Nat.length_digits p m hp h
  have h := List.sum_le_card_nsmul (Nat.digits p m) (p - 1)
    (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp hd))
  rw [hlen, smul_eq_mul, mul_comm] at h
  exact h

theorem factorialValuationLowerBound : FactorialLg := by
  intro p m hp
  have : Fact p.Prime := ⟨hp⟩
  have h1 := hp.sub_one_mul_multiplicity_factorial (n := m)
  have h2 := Nat.digit_sum_le p m
  have h3 := digits_sum_le_lgN p m hp.one_lt
  have h4 : m ≤ (p - 1) * (padicValNat p m.factorial + lgN p m) := by
    rw [Nat.padicValNat_def, mul_add, h1]
    omega
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    linarith
  have h5 : (m : ℝ) ≤ ((p : ℝ) - 1) * ((padicValNat p m.factorial : ℝ) + lgN p m) := by
    have h6 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    rw [← h6]
    exact_mod_cast h4
  rw [sub_le_iff_le_add, div_le_iff₀ hp1]
  linarith

theorem sum_lgN_le (p : ℕ) (hp : 1 < p) (A : ℕ) (f : ℕ → ℕ) (E : Finset ℕ)
    (h : ∀ e', p ^ (2 * e' + 1) * f e' ≤ A) :
    ∑ e' ∈ E, lgN p (f e') ≤ lgN p A ^ 2 := by
  have hle : ∀ e', f e' ≤ A := fun e' =>
    le_trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) (h e')
  have hsupp : ∀ e' ∈ E, lgN p (f e') ≠ 0 → e' < lgN p A := by
    intro e' _ hne
    have hf : f e' ≠ 0 := by
      intro h0
      apply hne
      simp [lgN, h0]
    have h1 : p ^ (2 * e' + 1) ≤ A :=
      le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hf)) (h e')
    have hA : A ≠ 0 := by
      have : 0 < p ^ (2 * e' + 1) := pow_pos (by omega) _
      omega
    have h2 := Nat.le_log_of_pow_le hp h1
    simp only [lgN, hA, if_false]
    omega
  rw [← Finset.sum_filter_of_ne hsupp]
  calc ∑ e' ∈ E.filter (fun e' => e' < lgN p A), lgN p (f e')
      ≤ ∑ _e' ∈ E.filter (fun e' => e' < lgN p A), lgN p A :=
        Finset.sum_le_sum (fun e' _ => lgN_mono p (hle e'))
    _ = (E.filter (fun e' => e' < lgN p A)).card * lgN p A := by rw [sum_const, smul_eq_mul]
    _ ≤ lgN p A * lgN p A := by
        apply Nat.mul_le_mul_right
        calc (E.filter (fun e' => e' < lgN p A)).card ≤ (range (lgN p A)).card :=
              card_le_card (fun x hx => by
                simp only [mem_filter, mem_range] at hx ⊢
                exact hx.2)
          _ = lgN p A := card_range _
    _ = lgN p A ^ 2 := (sq _).symm

theorem sum_factorial_ge {ι : Type} (p : ℕ) (hp : p.Prime) (T : Finset ι) (f : ι → ℕ) (B : ℕ)
    (hB : ∀ x ∈ T, f x ≤ B) :
    ((∑ x ∈ T, f x : ℕ) : ℝ) / ((p : ℝ) - 1) - (T.card : ℝ) * lgN p B ≤
      ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ) := by
  have h1 : ∑ x ∈ T, ((f x : ℝ) / ((p : ℝ) - 1) - lgN p B) ≤
      ∑ x ∈ T, (padicValNat p (f x).factorial : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    have h := factorialValuationLowerBound p (f x) hp
    have h' : (lgN p (f x) : ℝ) ≤ lgN p B := by exact_mod_cast lgN_mono p (hB x hx)
    linarith
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, sum_const, nsmul_eq_mul] at h1
  rw [Nat.cast_sum]
  exact h1

theorem gainFactorialInequality : StarArith := by
  intro S _ p r0 r1 TT al ls e a i E i0 i2 hp halT he ha hiE hiT hpi htot hi2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨-, hgam⟩ := Formalism.GrowthSums.oddPowerInvSumIdentity (p : ℝ) hp1
  set c : ℝ := 1 / ((p : ℝ) - 1) with hc

  have H1 : ∀ s, (al s : ℝ) * c - (r1 : ℝ) * lgN p (al s) ≤
      ∑ b, (padicValNat p (e s b).factorial : ℝ) := by
    intro s
    have h := sum_factorial_ge p hp univ (e s) (al s)
      (fun x _ => by rw [← he s]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x))
    rw [he s, card_univ, Fintype.card_fin] at h
    rw [hc, mul_one_div]
    exact h

  have H3 : ∀ s, ((∑ x, a s x : ℕ) : ℝ) * c - (r0 : ℝ) * r1 * lgN p (ls s) ≤
      ∑ x, (padicValNat p (a s x).factorial : ℝ) := by
    intro s
    have h := sum_factorial_ge p hp univ (a s) (ls s)
      (fun x _ => le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ x)) (ha s))
    rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul] at h
    rw [hc, mul_one_div]
    exact h

  have H2 : ∀ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) * c - ((lgN p (al s) : ℝ)) ^ 2 ≤
      ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ) := by
    intro s
    have h1 : ∑ e' ∈ E, ((i s e' : ℝ) / ((p : ℝ) - 1) - lgN p (i s e')) ≤
        ∑ e' ∈ E, (padicValNat p (i s e').factorial : ℝ) :=
      Finset.sum_le_sum (fun e' _ => factorialValuationLowerBound p (i s e') hp)
    have h2 : ((∑ e' ∈ E, lgN p (i s e') : ℕ) : ℝ) ≤ ((lgN p (al s) : ℝ)) ^ 2 := by
      exact_mod_cast sum_lgN_le p hp.one_lt (al s) (i s) E (hpi s)
    rw [Finset.sum_sub_distrib, ← Finset.sum_div] at h1
    rw [Nat.cast_sum] at h2
    rw [hc, mul_one_div, Nat.cast_sum]
    linarith
  have hlg0 : ∀ s, s ∉ TT → ((lgN p (al s) : ℝ)) ^ 2 = 0 := by
    intro s hs
    simp [lgN, halT s hs]
  have hTT_lg : ∑ s ∈ TT, ((lgN p (al s) : ℝ)) ^ 2 = ∑ s, ((lgN p (al s) : ℝ)) ^ 2 :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => hlg0 s hs)
  have hTT_al : ∑ s ∈ TT, (al s : ℝ) = ∑ s, (al s : ℝ) :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => by rw [halT s hs, Nat.cast_zero])
  have hTT_i : ∑ s ∈ TT, ∑ e' ∈ E, (i s e' : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ) :=
    Finset.sum_subset (subset_univ _) (fun s _ hs => by simp [hiT s hs])
  have S1 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H1 s)
  have S2 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H2 s)
  have S3 := Finset.sum_le_sum (fun s (_ : s ∈ (univ : Finset S)) => H3 s)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at S1 S2 S3
  have htotR : (∑ s, ((∑ x, a s x : ℕ) : ℝ)) + ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) =
      ∑ s, (ls s : ℝ) := by
    exact_mod_cast htot
  have hiR : ∑ s, ((∑ e' ∈ E, i s e' : ℕ) : ℝ) = ∑ s, ∑ e' ∈ E, (i s e' : ℝ) := by
    push_cast
    rfl
  have hi2R : (p : ℝ) * i2 ≤ ∑ s, (ls s : ℝ) := by exact_mod_cast hi2
  have hL0 : (0 : ℝ) ≤ ∑ s, (ls s : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

  have hgp : 1 / (p : ℝ) ≤ gamP p := by
    unfold gamP rhoP
    have hpp : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [mul_one_div, div_le_div_iff₀ hp0 hpp]
    nlinarith
  have hi2g : (i2 : ℝ) ≤ gamP p * ∑ s, (ls s : ℝ) := by
    have h1 : (i2 : ℝ) ≤ 1 / (p : ℝ) * ∑ s, (ls s : ℝ) := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hp0]
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hgp hL0)
  have hcg : c = gamP p + rhoP p := by rw [hgam]; ring
  unfold deLoss
  rw [hTT_lg, hTT_al, hTT_i, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hcg] at S1 S2 S3
  rw [hiR] at S2 htotR
  set A : ℝ := ∑ s, (al s : ℝ)
  set L : ℝ := ∑ s, (ls s : ℝ)
  set I : ℝ := ∑ s, ∑ e' ∈ E, (i s e' : ℝ)
  set Aa : ℝ := ∑ s, ((∑ x, a s x : ℕ) : ℝ)
  have hAa : Aa = L - I := by linarith
  rw [hAa] at S3
  nlinarith [S1, S2, S3, hi2g]

theorem cyclicShiftLeast : ChargeLemma := by
  intro n s s' a a' d haa h hd
  have hmem : a - a' ∈ {e : ℕ | 1 ≤ e ∧ s + (e : ZMod n) = s'} := by
    refine ⟨by omega, ?_⟩
    rw [Nat.cast_sub haa.le]
    linear_combination h
  exact (hd.2 hmem).trans (Nat.sub_le _ _)

theorem excessGainBound : ExcessGainBound := by
  intro n p TT D al cap de v i ch E hp hal hcap hi0 hch0 hE hchD hv hD hnD
  have hp0 : 0 < p := by linarith
  obtain ⟨hgs, -⟩ := Formalism.GrowthSums.oddPowerInvSumIdentity p hp
  have key : ∀ s ∈ TT, (∑' e : ℕ, (if 2 * e + 1 ∈ D s then 0 else
      max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) ≤
      gamP p * al s - ∑ e ∈ E, ch s e - ∑ e ∈ E, i s e := by
    intro s hs
    have hA : HasSum (fun e : ℕ => al s / p ^ (2 * e + 1)) (gamP p * al s) := by
      have h := hgs.mul_right (al s)
      have hf : (fun e : ℕ => al s / p ^ (2 * e + 1)) =
          fun e : ℕ => (p ^ (2 * e + 1))⁻¹ * al s := by
        funext e
        rw [div_eq_mul_inv, mul_comm]
      rw [hf]
      exact h
    have hC : HasSum (fun e : ℕ => ch s e) (∑ e ∈ E, ch s e) :=
      hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).2)
    have hI : HasSum (fun e : ℕ => i s e) (∑ e ∈ E, i s e) :=
      hasSum_sum_of_ne_finset_zero (fun e he => (hE s e he).1)
    have hR := (hA.sub hC).sub hI
    have hpos : ∀ e : ℕ, 0 ≤ al s / p ^ (2 * e + 1) :=
      fun e => div_nonneg (hal s) (pow_nonneg hp0.le _)
    have hsum : Summable (fun e : ℕ => (if 2 * e + 1 ∈ D s then (0 : ℝ) else
        max (al s / p ^ (2 * e + 1) - cap (s + ((2 * e + 1 : ℕ) : ZMod n))) 0)) := by
      refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hA.summable
      · split_ifs
        · exact le_rfl
        · exact le_max_right _ _
      · split_ifs
        · exact hpos e
        · exact max_le (by linarith [hcap (s + ((2 * e + 1 : ℕ) : ZMod n))]) (hpos e)
    refine hasSum_le (fun e => ?_) hsum.hasSum hR
    split_ifs with h
    · have := hD s hs e h
      linarith
    · have h1 := hnD s hs e h
      have h2 := hchD s e h
      have h3 := le_trans h1 (min_le_left _ _)
      have h4 := le_trans h1 (min_le_right _ _)
      rw [h2]
      exact max_le (by linarith) (by linarith)
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  unfold excessGain
  linarith

theorem cappedGainBound : BCore := by
  intro n p TT TTodd al cap de v paid i E hp hsub hal hcap hi0 hiE hv hpaid hodd
  have hp0 : 0 < p := by linarith
  have hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e =
      ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e :=
    (Finset.sum_sdiff hsub).symm
  have hodd' : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤
      ∑ s ∈ TTodd, ∑' e : ℕ,
        min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) := by
    apply Finset.sum_le_sum
    intro s hs
    have hsum := Formalism.GrowthSums.summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s
    calc ∑ e ∈ E, i s e
        ≤ ∑ e ∈ E, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) :=
          Finset.sum_le_sum (fun e _ => hodd s hs e)
      _ ≤ _ := hsum.sum_le_tsum E
          (fun e _ => le_min (div_nonneg (hal s) (pow_nonneg hp0.le _)) (hcap _))
  unfold gainG
  linarith

end Formalism.InvariantFactorPaths.G7
end
end

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem e_one_identity : JetPairingHasseIdentity := e_one_identity_of
theorem e_one_integral : HasseDerivIntegralHomogeneous := e_one_integral_of
theorem e_one_vanish : HasseDerivProdVanish := e_one_vanish_of
theorem minorHits : MinorHits := minor_hits
theorem starArith : StarArith := gainFactorialInequality
theorem chargeLemma : ChargeLemma := cyclicShiftLeast
theorem entry_a_one_bound : ExcessGainBound := excessGainBound
theorem bCore : BCore := cappedGainBound
theorem hitsCapPos : HitsCapPos := HitsCapPos_of e_one_vanish minorHits
theorem hitsColumnsPos : HitsColumnsPos := HitsColumnsPos_of e_one_vanish minorHits
theorem hasseDegree : HasseDegree := hasseDerivSupport
theorem minorProdDegree : MinorProdDegree := minorProdBlockDegree
theorem termBound : TermBound := TermBound_of e_one_identity e_one_integral
theorem hhDecomp : HhDecomp := decomposition_of_hh
theorem entryStar : EntryStar :=
  EntryStar_of termBound hhDecomp classSubst Formalism.DworkPowerSeriesWeights.jet_pair_linearity starArith hasseDegree
    minorProdDegree

theorem entry_a_one : EntryExcessBound := entryExcessBound_of entryStar hitsCapPos entry_a_one_bound chargeLemma
theorem entry_a_two : EntryCappedBound := entryCappedBound_of entryStar hitsCapPos Formalism.GrowthSums.cappedGainSubLE
theorem entryB : EntryB := EntryB_of entryStar hitsCapPos hitsColumnsPos bCore

end Formalism.InvariantFactorPaths.G7.Top
