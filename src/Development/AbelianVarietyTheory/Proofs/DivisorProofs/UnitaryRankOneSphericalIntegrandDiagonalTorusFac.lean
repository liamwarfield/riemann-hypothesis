module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimFieldBaseChangeLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegralityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFac
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

noncomputable section

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem swap_rev_comm {n : ℕ} (a i : Fin n) :
    Equiv.swap a a.rev i.rev = (Equiv.swap a a.rev i).rev := by
  rcases eq_or_ne i a with rfl | h1
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rcases eq_or_ne i a.rev with rfl | h2
  · simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne]
  · exact fun h => h2 (by rw [← h, Fin.rev_rev])
  · exact fun h => h1 (Fin.rev_injective h)

theorem conj_diag_apply {R : Type} [CommRing R] {n : ℕ} (s : Equiv.Perm (Fin n))
    (Y Yi T : Matrix (Fin n) (Fin n) R) (hinv : Yi * Y = 1)
    (hY : ∀ i j, i ≠ s j → Y i j = 0) (hYi : ∀ i j, j ≠ s i → Yi i j = 0)
    (hT : ∀ i j, i ≠ j → T i j = 0) (i j : Fin n) :
    (Yi * T * Y) i j = if i = j then T (s i) (s i) else 0 := by
  have e1 : (Yi * T * Y) i j = Yi i (s j) * T (s j) (s j) * Y (s j) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
      · intro p _ hp; rw [hT p (s j) hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r _ hr; rw [hY r j hr, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e1]
  split_ifs with hij
  · subst hij
    have e2 : (Yi * Y) i i = Yi i (s i) * Y (s i) i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
      · intro p _ hp; rw [hY p i hp, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hinv, Matrix.one_apply_eq] at e2
    calc Yi i (s i) * T (s i) (s i) * Y (s i) i = T (s i) (s i) * (Yi i (s i) * Y (s i) i) := by ring
      _ = T (s i) (s i) := by rw [← e2, mul_one]
  · rw [hYi i (s j) (fun h => hij (s.injective h).symm), zero_mul, zero_mul]

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_inv (z : L) : ordL z⁻¹ = -ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [ordL]
  have h1 := GlobalTheory.BorelUMod.v_eq_exp (inv_ne_zero hz)
  rw [map_inv₀, GlobalTheory.BorelUMod.v_eq_exp hz, ← WithZero.exp_neg, WithZero.exp_inj] at h1
  linarith

theorem ordL_map {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (z : L) : ordL (σ z) = ordL z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hz' : σ z ≠ 0 := (map_ne_zero σ).2 hz
  have h1 := hσ z
  rw [GlobalTheory.BorelUMod.v_eq_exp hz, GlobalTheory.BorelUMod.v_eq_exp hz', WithZero.exp_inj] at h1
  linarith

end GlobalTheory.WeylCell.U21TorusFactor

namespace GlobalTheory.WeylCell.U21TorusFactor

open Formalism.UG

theorem torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw α φ hφ t ht w x
  have hσv : ∀ z, Valued.v (σ z) = Valued.v z := hU.2.1
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by
    rw [simpleU, if_neg hk]
  set a : Fin n := lo k with ha
  have hkv : k.val = n / 2 - 1 := by have := k.2; omega
  have hodd : n % 2 = 1 := by
    rcases Nat.even_or_odd n with h | h
    · exact absurd h hn
    · exact Nat.odd_iff.1 h
  have hav : a.val = k.val := rfl
  have hrv : (a.rev).val = n - 1 - k.val := by rw [Fin.val_rev, hav]; omega

  set Y : Matrix (Fin n) (Fin n) L := (((y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYd
  set Yi : Matrix (Fin n) (Fin n) L := ((((y : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hYid
  set T : Matrix (Fin n) (Fin n) L := (((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTd
  have hinv : Yi * Y = 1 := by
    rw [hYid, hYd, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hYw : ∀ i j, i ≠ Equiv.swap a a.rev j → Y i j = 0 := by
    intro i j h; rw [← hs] at h; exact hw i j h
  have hYi : ∀ i j, j ≠ Equiv.swap a a.rev i → Yi i j = 0 := by
    intro i j h
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (y : GU σ n).2 i j
    rw [hYid, hm]
    have : j.rev ≠ Equiv.swap a a.rev i.rev := by
      rw [swap_rev_comm]; exact fun h' => h (Fin.rev_injective h')
    exact (congrArg σ (hYw _ _ this)).trans (map_zero σ)
  set b : GU σ n := y⁻¹ * t * y with hbd
  have hb : ∀ i j, (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      if i = j then T (Equiv.swap a a.rev i) (Equiv.swap a a.rev i) else 0 := by
    intro i j
    have : (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Yi * T * Y := by
      simp [hbd, hYid, hYd, hTd, Units.val_mul]
    rw [this]
    exact conj_diag_apply _ Y Yi T hinv hYw hYi ht i j
  have hB : IsBorelU b := by
    intro i j hij
    rw [hb, if_neg (ne_of_gt hij)]
  have hsph := hφ b (y⁻¹ * w * x) 1 hB (one_mem _)
  have hprod : y⁻¹ * t * w * x = b * (y⁻¹ * w * x) * 1 := by
    rw [hbd]; group

  have hTa : T a a ≠ 0 ∧ ordL (T a.rev a.rev) = -ordL (T a a) := by
    set Ti : Matrix (Fin n) (Fin n) L := ((((t : GU σ n) : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hTid
    have h1 : T * Ti = 1 := by
      rw [hTid, hTd, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : (T * Ti) a a = T a a * Ti a a := by
      rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · intro p _ hp; rw [ht a p (Ne.symm hp), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, Matrix.one_apply_eq] at h2
    have hne : T a a ≠ 0 := by intro h0; rw [h0, zero_mul] at h2; exact one_ne_zero h2
    have hTi : Ti a a = (T a a)⁻¹ := by
      exact eq_inv_of_mul_eq_one_right h2.symm
    have hm := (GlobalTheory.LGrp.mem_GU_iff σ n _).1 (t : GU σ n).2 a a
    rw [← hTid, hTi] at hm
    refine ⟨hne, ?_⟩
    rw [← ordL_map hσv (T a.rev a.rev)]
    exact (congrArg ordL hm.symm).trans (ordL_inv _)

  have e : ∀ (β : Fin (n / 2) → ℂ) (g : GU σ n), chiDeltaU q β g =
      ∏ i : Fin (n / 2), β i ^ ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
        (q : ℂ) ^ (-(ordL ((((g : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
    intro β g
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [dite_eq_left (by have := i.2; omega)]
    rfl
  have hact : ∀ i, (actU k α i : ℂ) = if i = k then (α k : ℂ)⁻¹ else α i := by
    intro i
    unfold actU
    rw [dite_eq_right hk]
    by_cases hi : i = k
    · subst hi; simp [Function.update_self, Units.val_inv_eq_inv_val]
    · simp [Function.update_of_ne hi, hi]
  have key : chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
    rw [e, e, Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
    have hrest : ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (α i : ℂ) ^ ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) =
        ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ))) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hik : i ≠ k := by simpa using hi
      have hfix : Equiv.swap a a.rev (lo i) = lo i := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; apply hik; ext; have := congrArg Fin.val h; simpa [ha] using this
        · intro h; have := congrArg Fin.val h; rw [hrv] at this
          have h3 : (lo i : Fin n).val = i.val := rfl
          have := i.2; omega
      rw [hb, if_pos rfl, hfix, hact, if_neg hik]
    rw [hrest, hb, if_pos rfl, ← ha, Equiv.swap_apply_left, hTa.2, hact, if_pos rfl]
    have hE : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 2 := by omega
    rw [hE]
    set o := ordL (T a a)
    set R := ∏ i ∈ ({k}ᶜ : Finset (Fin (n / 2))),
        (actU k α i : ℂ) ^ ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i)) *
          (q : ℂ) ^ (-(ordL ((((t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo i) (lo i))) *
            ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    have hqq : (q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o) = (q : ℂ) ^ (-o * 2) := by
      rw [← zpow_add₀ hq]; ring_nf
    have hα : (α k : ℂ) ^ (-o) = ((α k : ℂ)⁻¹) ^ o := by rw [zpow_neg, inv_zpow]
    calc (α k : ℂ) ^ (-o) * (q : ℂ) ^ (-(-o) * 2) * R * (q : ℂ) ^ (-4 * o)
        = (α k : ℂ) ^ (-o) * ((q : ℂ) ^ (-(-o) * 2) * (q : ℂ) ^ (-4 * o)) * R := by ring
      _ = ((α k : ℂ)⁻¹) ^ o * (q : ℂ) ^ (-o * 2) * R := by rw [hqq, hα]
  rw [hprod, hsph]
  calc chiDeltaU q (fun i => (α i : ℂ)) b * φ (y⁻¹ * w * x) * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))
      = (chiDeltaU q (fun i => (α i : ℂ)) b * (q : ℂ) ^ (-4 * ordL (T (lo k) (lo k)))) * φ (y⁻¹ * w * x) := by ring
    _ = _ := by rw [key]

end GlobalTheory.WeylCell.U21TorusFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankOneSphericalIntegrandDiagonalTorusFacStatement
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankOne_sphericalIntegrand_diagonal_torus_factor : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂˣ) (φ : GU σ n → ℂ), IsSphericalU q (fun i => (α i : ℂ)) φ →
    ∀ t : GU σ n, (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) → ∀ w x : GU σ n,
      φ (y⁻¹ * t * w * x) * (q : ℂ) ^ (-4 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
        chiDeltaU q (fun i => (actU k α i : ℂ)) t * φ (y⁻¹ * w * x) := by
  first | exact @GlobalTheory.WeylCell.U21TorusFactor.torus_factor | exact GlobalTheory.WeylCell.U21TorusFactor.torus_factor | (intros; apply GlobalTheory.WeylCell.U21TorusFactor.torus_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylCellStabilizerMeasure
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.ShellU

section Balls

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ball (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (j : ℤ) : AddSubgroup L where
  carrier := {b | Valued.v b ≤ WithZero.exp j}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by
    show Valued.v (-a) ≤ _
    rwa [Valuation.map_neg]

def antiBall (σ : L →+* L) (j : ℤ) : AddSubgroup L where
  carrier := {b | σ b = -b ∧ Valued.v b ≤ WithZero.exp j}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add (f := _), ha, hb, neg_add], (Valuation.map_add _ a b).trans (max_le ha' hb')⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_neg, ha], by rwa [Valuation.map_neg]⟩

def fixBall (σ : L →+* L) (j : ℤ) : AddSubgroup L where
  carrier := {f | σ f = f ∧ Valued.v f ≤ WithZero.exp j}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add (f := _), ha, hb], (Valuation.map_add _ a b).trans (max_le ha' hb')⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_neg, ha], by rwa [Valuation.map_neg]⟩

theorem mem_ball {j : ℤ} {b : L} : b ∈ ball L j ↔ Valued.v b ≤ WithZero.exp j := Iff.rfl

theorem mem_antiBall {σ : L →+* L} {j : ℤ} {b : L} :
    b ∈ antiBall σ j ↔ σ b = -b ∧ Valued.v b ≤ WithZero.exp j := Iff.rfl

theorem mem_fixBall {σ : L →+* L} {j : ℤ} {f : L} :
    f ∈ fixBall σ j ↔ σ f = f ∧ Valued.v f ≤ WithZero.exp j := Iff.rfl


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem relIndex_eq_of_mul {c : L} (hc : c ≠ 0) {A B A' B' : AddSubgroup L}
    (hA : ∀ x, x ∈ A ↔ c * x ∈ A') (hB : ∀ x, x ∈ B ↔ c * x ∈ B') : A.relIndex B = A'.relIndex B' := by
  have e1 : A = A'.comap (AddMonoidHom.mulLeft c) := AddSubgroup.ext hA
  have e2 : B = B'.comap (AddMonoidHom.mulLeft c) := AddSubgroup.ext hB
  rw [e1, AddSubgroup.relIndex_comap, e2, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨c⁻¹ * y, mul_inv_cancel_left₀ hc y⟩

theorem le_exp_neg_one_of_lt_one {y : WithZero (Multiplicative ℤ)} (h : y < 1) : y ≤ WithZero.exp (-1 : ℤ) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem relIndex_ball {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (ball L (-1)).relIndex (ball L 0) = q ^ 2 := by
  obtain ⟨-, -, -, -, -, -, hcard⟩ := hU
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hv
  let f : v.valuationSubring →+ L := v.valuationSubring.subtype.toAddMonoidHom
  have e1 : (IsLocalRing.maximalIdeal v.valuationSubring).toAddSubgroup = (ball L (-1)).comap f := by
    ext x
    show x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ v (x : L) ≤ WithZero.exp (-1 : ℤ)
    rw [Valuation.mem_maximalIdeal_iff]
    refine ⟨le_exp_neg_one_of_lt_one, fun h => h.trans_lt ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have e2 : (⊤ : AddSubgroup v.valuationSubring).map f = ball L 0 := by
    ext x
    rw [mem_ball, WithZero.exp_zero]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Valuation.mem_valuationSubring_iff _ _).1 y.2
    · intro h
      exact ⟨⟨x, (Valuation.mem_valuationSubring_iff _ _).2 h⟩, trivial, rfl⟩
  rw [← e2, ← AddSubgroup.relIndex_comap, ← e1, AddSubgroup.relIndex_top_right, AddSubgroup.index_eq_card]
  exact hcard

theorem relIndex_anti_eq_fix {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (j : ℤ) :
    (antiBall σ j).relIndex (antiBall σ (j + 1)) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
  obtain ⟨hσ, -, hϖ, hv, ⟨x, -, hx⟩, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hv'; exact WithZero.exp_ne_zero hv'.symm
  have hc : δ * ϖ ^ (j + 1) ≠ 0 := mul_ne_zero hδ0 (zpow_ne_zero _ hϖ0)
  have key : ∀ (i : ℤ) (z : L), z ∈ antiBall σ (i + (j + 1)) ↔ δ * ϖ ^ (j + 1) * z ∈ fixBall σ i := by
    intro i z
    rw [mem_antiBall, mem_fixBall]
    refine and_congr ?_ ?_
    · rw [map_mul, map_mul, map_zpow₀, hϖ, hσδ]
      constructor
      · intro h; rw [h]; ring
      · intro h
        apply mul_left_cancel₀ hc
        linear_combination -h
    · rw [map_mul, map_mul, map_zpow₀, hx, hv', one_mul, ← WithZero.exp_zsmul, WithZero.exp_add,
        smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_comm]
  refine relIndex_eq_of_mul hc (fun z => ?_) (fun z => ?_)
  · rw [← key]; congr! 2; ring
  · rw [← key]; congr! 2; ring

theorem relIndex_antiBall {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (j : ℤ) :
    (antiBall σ j).relIndex (antiBall σ (j + 1)) = q := by
  have h0 := relIndex_ball hU
  have h1 := relIndex_anti_eq_fix hU (-1)
  rw [relIndex_anti_eq_fix hU j]
  obtain ⟨hσ, hvσ, -, -, ⟨x, hxO, hx⟩, -, -⟩ := hU
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  set e := -x / δ with he
  have he1 : e + σ e = 1 := by
    rw [he, map_div₀, map_neg, hσδ]; field_simp; rw [hδ]; ring
  have hve : Valued.v e ≤ 1 := by
    rw [he, map_div₀, hx, div_one, Valuation.map_neg]
    exact (Valuation.mem_integer_iff _ _).1 hxO
  let t : L →+ L := AddMonoidHom.id L - σ.toAddMonoidHom
  have ht : ∀ z, t z = z - σ z := fun z => rfl
  have hte : ∀ b, σ b = -b → t (e * b) = b := fun b hb => by
    rw [ht, map_mul, hb]; linear_combination b * he1
  have hσt : ∀ z, σ (t z) = -t z := fun z => by rw [ht, map_sub, hσ]; ring
  have hvt : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (t z) ≤ WithZero.exp (i : ℤ) := fun z i h =>
    (Valuation.map_sub _ _ _).trans (max_le h ((hvσ z).le.trans h))
  have hve' : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (e * z) ≤ WithZero.exp (i : ℤ) := fun z i h => by
    rw [map_mul]; exact (mul_le_mul' hve h).trans (one_mul _).le
  have hle : WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.2 (by norm_num)
  have a1 : (ball L 0).map t = antiBall σ 0 := by
    ext b
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hσt z, hvt z 0 hz⟩
    · rintro ⟨hb, hb'⟩
      exact ⟨e * b, hve' b 0 hb', hte b hb⟩
  have a2 : (antiBall σ (-1)).comap t ⊓ ball L 0 = fixBall σ 0 ⊔ ball L (-1) := by
    apply le_antisymm
    · rintro z ⟨⟨-, hz⟩, hz'⟩
      refine AddSubgroup.mem_sup.2 ⟨z - e * t z, ⟨?_, ?_⟩, e * t z, hve' _ _ hz, by ring⟩
      · have : t (z - e * t z) = 0 := by rw [map_sub, hte _ (hσt z), sub_self]
        rw [ht] at this
        exact (sub_eq_zero.1 this).symm
      · exact (Valuation.map_sub _ _ _).trans (max_le hz' ((hve' _ _ hz).trans hle))
    · refine sup_le (fun z hz => ⟨⟨hσt z, ?_⟩, hz.2⟩) (fun z hz => ⟨⟨hσt z, hvt z _ hz⟩, le_trans hz hle⟩)
      rw [ht, hz.1, sub_self, map_zero]; exact zero_le'
  have a3 : ball L (-1) ⊓ fixBall σ 0 = fixBall σ (-1) :=
    le_antisymm (fun z hz => ⟨hz.2.1, hz.1⟩) (fun z hz => ⟨hz.2, hz.1, hz.2.trans hle⟩)
  have b1 : (fixBall σ 0 ⊔ ball L (-1)).relIndex (ball L 0) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
    rw [← a2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, a1, ← h1]; norm_num
  have b2 : (ball L (-1)).relIndex (fixBall σ 0 ⊔ ball L (-1)) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
    rw [AddSubgroup.relIndex_sup_right, ← a3, AddSubgroup.inf_relIndex_right]
  have b3 := AddSubgroup.relIndex_mul_relIndex (ball L (-1)) (fixBall σ 0 ⊔ ball L (-1)) (ball L 0) le_sup_right
    (by rw [← a2]; exact inf_le_right)
  rw [b1, b2, h0, ← sq] at b3
  exact Nat.pow_left_injective two_ne_zero b3

end Balls

theorem measure_eq_relIndex_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H K : Subgroup G) (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (hle : H ≤ K)
    (hi : H.relIndex K ≠ 0) : μ K = (H.relIndex K : ENNReal) * μ H := by
  have hemb : MeasurableEmbedding (K.subtype : K → G) := MeasurableEmbedding.subtype_coe hK
  haveI : (μ.comap (K.subtype : K → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hi⟩
  have key := (H.subgroupOf K).index_mul_measure (hemb.measurable hH) (μ.comap (K.subtype : K → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (K.subtype : K → G) '' Set.univ = (K : Set G) := by
    ext x; simp
  have e2 : (K.subtype : K → G) '' ((H.subgroupOf K : Subgroup K) : Set K) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  exact key.symm

theorem measure_chain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H : ℤ → Subgroup G) {q : ℕ} (hq : q ≠ 0)
    (hm : ∀ j, MeasurableSet (H j : Set G)) (hle : ∀ j, H j ≤ H (j + 1))
    (hi : ∀ j, (H j).relIndex (H (j + 1)) = q) (h0 : μ (H 0) = 1) (j : ℤ) : μ (H j) = (q : ENNReal) ^ j := by
  have hq0 : (q : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have step : ∀ j, μ (H (j + 1)) = q * μ (H j) := fun j => by
    rw [measure_eq_relIndex_mul μ (H j) (H (j + 1)) (hm _) (hm _) (hle j) (by rw [hi]; exact hq), hi]
  induction j using Int.induction_on with
  | zero => rw [h0, zpow_zero]
  | succ i ih => rw [step, ih, ENNReal.zpow_add hq0 hqt, zpow_one, mul_comm]
  | pred i ih =>
    have h := step (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    apply (ENNReal.mul_right_inj hq0 hqt).1
    rw [← h]
    conv_lhs => rw [show -(i : ℤ) = 1 + (-(i : ℤ) - 1) by ring, ENNReal.zpow_add hq0 hqt, zpow_one]

theorem isOpen_ball {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : IsOpen {x : L | Valued.v x ≤ WithZero.exp j} := by
  have e : {x : L | Valued.v x ≤ WithZero.exp j} = (fun x => ϖ ^ j * x) ⁻¹' (intL L : Set L) := by
    ext x
    show _ ↔ Valued.v (ϖ ^ j * x) ≤ 1
    rw [map_mul, map_zpow₀, hv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg,
      inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    rfl
  rw [e]
  exact (Valued.isOpen_integer L).preimage (continuous_const.mul continuous_id)

end GlobalTheory.ShellU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDegreeOfNormBound
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open Polynomial

end GlobalTheory.DegCmp
end

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree
open scoped ENNReal

namespace GlobalTheory.DegTop

theorem growth_mono (D : ℕ) {s s' : ℕ → ℕ∞} (h : ∀ k, 1 ≤ k → s k ≤ s' k) : growth D s ≤ growth D s' :=
  Filter.limsup_le_limsup ((Filter.eventually_ge_atTop 1).mono fun k hk => ENNReal.div_le_div_right
    (mul_le_mul_right (ENat.toENNReal_le.2 (h k hk)) _) _)

theorem growth_top (D : ℕ) : growth D (fun _ => ⊤) = ⊤ := by
  rw [growth, ← Filter.limsup_const (f := (Filter.atTop : Filter ℕ)) (⊤ : ℝ≥0∞)]
  refine Filter.limsup_congr (Filter.Eventually.of_forall fun k => ?_)
  rw [ENat.toENNReal_top, ENNReal.mul_top (Nat.cast_ne_zero.2 D.factorial_ne_zero)]
  exact ENNReal.top_div_of_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top k))

theorem of_not_finiteDimensional {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : ¬ FiniteDimensional K V) :
    (∃ v : V, v ≠ 0) ∧ Cardinal.aleph0 ≤ Module.rank K V := by
  refine ⟨?_, not_lt.1 fun h2 => h (Module.rank_lt_aleph0_iff.1 h2)⟩
  by_contra h0
  push Not at h0
  have : Subsingleton V := subsingleton_of_forall_eq 0 h0
  exact h inferInstance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem mem_holSub_iff {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) :
    P ∈ holSub X la ↔ ∀ k, P k ∈ (X k).SS (la k) := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem eq_zero_of_genVal {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) :
    f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1 hZ hf.2

theorem mul_mem_cuspOn {Z : Comp Xo c} {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {f g : Rul Xo c}
    (hf : f ∈ cuspOn U Z G) (hg : g ∈ cuspW Xo c U G') : f * g ∈ cuspOn U Z (G + G') := by
  refine ⟨?_, by rw [mul_comm]; exact mul_mem_suppOn _ hf.2⟩
  have hf' := mem_cuspW.1 hf.1
  rw [mem_cuspW] at hg
  refine mem_cuspW.2 ⟨?_, fun σ hσ => ?_⟩
  · have e : exZ Dw (G + G') = exZ Dw G + exZ Dw G' := funext fun i => exZ_add _ _ _
    rw [e]
    exact mul_mem_secZ hf'.1 hg.1
  · rw [AllWt.rdU_mul, mem_holSub_iff]
    intro k
    rw [modelWt_add (U σ) hG hG' k]
    exact (siegelSpaceAlgebra_holds (E := E) r _ _ _ 0).2.1 _ ((mem_holSub_iff _ _ _).1 (hf'.2 σ hσ) k) _
      ((mem_holSub_iff _ _ _).1 (hg.2 σ hσ) k).1


omit [NumberField E] [IsCMField E] in
theorem even_nsmul {G : WTZ E} (hG : Even G.2) (n : ℕ) : Even (n • G).2 := by
  rw [Prod.smul_snd, nsmul_eq_mul]; exact hG.mul_left n

section

set_option synthInstance.maxHeartbeats 100000

theorem range_pow_le {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) (n : ℕ) :
    (LinearMap.range (genPoint Z (cuspOn U Z G))) ^ (n + 1) ≤
      (cuspOn U Z ((n + 1) • G)).map (genVal Z).toLinearMap := by
  induction n with
  | zero =>
    rintro _ hy
    rw [zero_add, pow_one] at hy
    obtain ⟨v, rfl⟩ := hy
    exact ⟨v, by simp, rfl⟩
  | succ n ih =>
    rw [pow_succ]
    refine Submodule.mul_le.2 fun a ha b hb => ?_
    obtain ⟨f, hf, rfl⟩ := ih ha
    obtain ⟨v, rfl⟩ := hb
    refine ⟨f * v, ?_, map_mul (genVal Z) _ _⟩
    rw [succ_nsmul]
    exact mul_mem_cuspOn (even_nsmul hG _) hG hf v.2.1

theorem hilb_le {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) {τ : ℕ} (hτ : 1 ≤ τ) :
    hilb (genPoint Z (cuspOn U Z G)) τ ≤ Cardinal.toENat (Module.rank c.F (cuspOn U Z (τ • G))) := by
  obtain ⟨n, rfl⟩ : ∃ n, τ = n + 1 := ⟨τ - 1, by omega⟩
  exact OrderHomClass.mono Cardinal.toENat ((Submodule.rank_mono (range_pow_le hG n)).trans (rank_map_le _ _))

theorem rank_map_mul {Z : Comp Xo c} {G : WTZ E} {θ : Rul Xo c} (hθ : genVal Z θ ≠ 0) :
    Module.rank c.F ((cuspOn U Z G).map ((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F θ)) =
      Module.rank c.F (cuspOn U Z G) := by
  have hi : Function.Injective (((genVal Z).toLinearMap ∘ₗ LinearMap.mulLeft c.F θ) ∘ₗ (cuspOn U Z G).subtype) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : genVal Z (θ * f) = 0 := hf
    rw [map_mul] at h1
    exact Subtype.ext (eq_zero_of_genVal f.2 ((mul_eq_zero.1 h1).resolve_left hθ))
  rw [← rank_range_of_injective _ hi, LinearMap.range_comp, Submodule.range_subtype]

theorem finiteDimensional_of_growthOn {Z : Comp Xo c} {G : WTZ E} (hG : Even G.2) (h : growthOn U Z G ≠ ⊤) :
    FiniteDimensional c.F (cuspOn U Z G) := by
  by_contra hfd
  obtain ⟨⟨v, hv⟩, hr⟩ := of_not_finiteDimensional hfd
  have hv' : genVal Z (v : Rul Xo c) ≠ 0 := fun h0 => hv (Subtype.ext (eq_zero_of_genVal v.2 h0))
  have key : ∀ n : ℕ, ∀ f ∈ cuspOn U Z G, (v : Rul Xo c) ^ n * f ∈ cuspOn U Z ((n + 1) • G) := fun n f hf => by
    induction n with
    | zero => simpa using hf
    | succ n ih =>
      rw [succ_nsmul, pow_succ, mul_right_comm]
      exact mul_mem_cuspOn (even_nsmul hG _) hG ih v.2.1
  refine h (top_le_iff.1 ((growth_top (dimFlag Dw)).symm.trans_le (growth_mono _ fun k hk => ?_)))
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h1 : Module.rank c.F (cuspOn U Z G) ≤ Module.rank c.F (cuspOn U Z ((n + 1) • G)) := by
    rw [← rank_map_mul (U := U) (G := G) (θ := (v : Rul Xo c) ^ n) (by rw [map_pow]; exact pow_ne_zero _ hv')]
    refine (Submodule.rank_mono ?_).trans (rank_map_le (genVal Z).toLinearMap _)
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨_, key n f hf, rfl⟩
  rw [top_le_iff, Cardinal.toENat_eq_top]
  exact hr.trans h1

theorem topDeg_nonneg (Z : Comp Xo c) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) : 0 ≤ topDeg U Z u :=
  mul_nonneg (vZero_nonneg U Z) (Int.cast_pos.2 (vdm_pos hu)).le

theorem growth_mul_eq (hP : Proport U) (Z : Comp Xo c) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {a : ℕ}
    (ha : 1 ≤ a) : growth (dimFlag Dw) (fun k => Cardinal.toENat (Module.rank c.F (cuspOn U Z ((a * k) • wtOf Dw u 0)))) =
      ENNReal.ofReal ((a : ℝ) ^ dimFlag Dw * topDeg U Z u) := by
  have h1 : ∀ τ, StrictAnti ((a • u) τ) := fun τ i j hij => by
    have := hu τ hij
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left this (by exact_mod_cast ha)
  have h2 := hP Z (a • u) h1
  have h3 : wtOf Dw (a • u) 0 = a • wtOf Dw u 0 := by rw [nsmul_wtOf, smul_zero]
  have h4 : topDeg U Z (a • u) = (a : ℝ) ^ dimFlag Dw * topDeg U Z u := by
    rw [topDeg, topDeg, ← Nat.cast_smul_eq_nsmul ℤ a u, vdm_smul, dimFlag]
    push_cast; ring
  rw [← h4, ← h2, growthOn, h3]
  exact congrArg _ (funext fun k => by rw [mul_nsmul])

theorem finiteDimensional_cuspOn (hP : Proport U) (Z : Comp Xo c) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    FiniteDimensional c.F (cuspOn U Z (wtOf Dw u 0)) :=
  finiteDimensional_of_growthOn (even_wtOf u 0) (by rw [hP Z u hu]; exact ENNReal.ofReal_ne_top)

theorem growth_hilb_le (hP : Proport U) (Z : Comp Xo c) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) {a : ℕ}
    (ha : 1 ≤ a) : growth (dimFlag Dw) (fun k => hilb (genPoint Z (cuspOn U Z (wtOf Dw u 0))) (a * k)) ≤
      ENNReal.ofReal ((a : ℝ) ^ dimFlag Dw * topDeg U Z u) :=
  (growth_mono _ fun _ hk => hilb_le (even_wtOf u 0) (Nat.mul_pos ha hk)).trans_eq (growth_mul_eq hP Z hu ha)

theorem compDeg_le (hP : Proport U) (Z : Comp Xo c) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ topDeg U Z u := by
  rcases (compDeg U Z (wtOf Dw u 0)).eq_zero_or_pos with h0 | h0
  · rw [h0, Nat.cast_zero]; exact topDeg_nonneg Z hu
  · have := finiteDimensional_cuspOn hP Z hu
    have h1 := GlobalTheory.T.cone_degree_growth_chowForm_integrality.1 c.F _ _ _ _ 1 le_rfl _ ((imageDeg_pos_iff _ _).1 h0)
    have h2 := growth_hilb_le hP Z hu le_rfl
    rw [h1, Nat.cast_one, Nat.cast_one, one_pow, one_pow, one_mul, one_mul, ← ENNReal.ofReal_natCast] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (topDeg_nonneg Z hu)).1 h2

end

def normFac {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ) (G : WTZ E) (z : Σ k, Frame (U.X k).Ψ r) : ℝ :=
  lieFacZ Dw x G * (U.X z.1).nfac (modelWt U G z.1) z.2

section Fac

variable {σ : c.F →+* ℂ} (U₁ : Unf Xo c σ r) (x)

theorem homN_eq (G : WTZ E) (f : Rul Xo c) (z : Σ k, Frame (U₁.X k).Ψ r) :
    homN U₁ x G f z = normFac U₁ x G z * ‖rdU U₁ f z.1 z.2‖ := by
  show _ * (‖rdU U₁ f z.1 z.2‖ * (U₁.X z.1).nfac (modelWt U₁ G z.1) z.2) = _
  rw [normFac]; ring

theorem normFac_pos (G : WTZ E) {z : Σ k, Frame (U₁.X k).Ψ r} (hz : z.2 ∈ (U₁.X z.1).dom) : 0 < normFac U₁ x G z := by
  have hd : ∀ τ i, dmin (U₁.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  exact mul_pos (lieFacZ_pos _ _) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _)

theorem normFac_add {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) {z : Σ k, Frame (U₁.X k).Ψ r}
    (hz : z.2 ∈ (U₁.X z.1).dom) : normFac U₁ x (G + G') z = normFac U₁ x G z * normFac U₁ x G' z := by
  have hd : ∀ τ i, dmin (U₁.X z.1).Gm z.2 τ i ≠ 0 := fun τ i h0 => by
    have := (hz τ).2 i
    rw [h0] at this; simp at this
  have key : ∀ la la' : Wt (U₁.X z.1).Ψ r, (U₁.X z.1).nfac (la + la') z.2 =
      (U₁.X z.1).nfac la z.2 * (U₁.X z.1).nfac la' z.2 := fun la la' => by
    unfold Data.nfac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_add (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _)))]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  rw [normFac, normFac, normFac, modelWt_add U₁ hG hG', key, lieFacZ_add]
  ring

theorem normFac_nsmul {G : WTZ E} (hG : Even G.2) {z : Σ k, Frame (U₁.X k).Ψ r} (hz : z.2 ∈ (U₁.X z.1).dom) (n : ℕ) :
    normFac U₁ x (n • G) z = normFac U₁ x G z ^ n := by
  induction n with
  | zero =>
    have h := normFac_add x U₁ (G := 0) (G' := 0) Even.zero Even.zero hz
    rw [add_zero] at h
    rw [zero_nsmul, pow_zero]
    exact (mul_left_cancel₀ (normFac_pos x U₁ 0 hz).ne' (h.symm.trans (mul_one _).symm))
  | succ n ih => rw [succ_nsmul, normFac_add x U₁ (even_nsmul hG n) hG hz, ih, pow_succ]

end Fac

end GlobalTheory.DegTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SepClosedDiv

theorem exists_section_of_etale {Ω : Type} [Field Ω] [IsSepClosed Ω] {X : Scheme.{0}} (f : X ⟶ Sp Ω)
    [Etale f] (x : X) : ∃ s : Sp Ω ⟶ X, s ≫ f = 𝟙 _ := by
  let i := X.affineCover.idx x
  obtain ⟨y, -⟩ := X.affineCover.covers x
  obtain ⟨R, e⟩ : ∃ R : CommRingCat, X.affineCover.X i = Spec R := ⟨_, rfl⟩
  let φ : CommRingCat.of Ω ⟶ R := Spec.preimage (eqToHom e.symm ≫ X.affineCover.f i ≫ f)
  have hφ : Spec.map φ = eqToHom e.symm ≫ X.affineCover.f i ≫ f := Spec.map_preimage _
  have hg : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  have hr : φ.hom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).1 hg
  letI := φ.hom.toAlgebra
  have : Algebra.Etale Ω R := hr
  let q : PrimeSpectrum R := (eqToHom e).base y
  obtain ⟨ψ⟩ := GlobalTheory.nonempty_algHom_of_etale_of_isSepClosed (R := Ω) (A := R) (K := Ω) q.asIdeal
    (by
      rw [(Ideal.comap (algebraMap Ω R) q.asIdeal).eq_bot_of_prime]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap Ω Ω).injective).symm)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ eqToHom e.symm ≫ X.affineCover.f i, ?_⟩
  simp only [Category.assoc]
  rw [← hφ, ← Spec.map_comp]
  rw [← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a

theorem exists_pow_eq : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  intro K Ω _ _ _ _ A _ _ hA n hn x
  have := hA.smooth
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have he : Etale (mulN A n).left := GlobalTheory.GrpTangent.etale_mulN A hu
  have hs : Surjective (mulN A n).left := GlobalTheory.surjective_mulN_of_isAbelianScheme K A hA n hn
  let m := (mulN A n).left
  have he' : Etale (pullback.snd m x.left) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd m x.left).surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨s, hs'⟩ := exists_section_of_etale (pullback.snd m x.left) z
  have h : (s ≫ pullback.fst m x.left) ≫ m = x.left := by
    rw [Category.assoc, pullback.condition, reassoc_of% hs']
  refine ⟨Over.homMk (s ≫ pullback.fst m x.left) ?_, ?_⟩
  · change (s ≫ pullback.fst m x.left) ≫ A.hom = _
    rw [← Over.w (mulN A n), ← Category.assoc, h]
    exact Over.w x
  · rw [← GlobalTheory.GrpTangent.comp_mulN]
    exact Over.OverMorphism.ext h

end GlobalTheory.SepClosedDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietySepClosedPointDivisibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_sepClosed_point_divisible : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ n : ℕ, (n : K) ≠ 0 → ∀ x : ptOver K Ω ⟶ A, ∃ y, y ^ n = x := by
  first | exact @GlobalTheory.SepClosedDiv.exists_pow_eq | exact GlobalTheory.SepClosedDiv.exists_pow_eq | (intros; apply GlobalTheory.SepClosedDiv.exists_pow_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramified
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRed

theorem natCast_ne_zero_of_residue {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {m : ℕ} (h : (m : ResidueField R) ≠ 0) : (m : K) ≠ 0 := by
  intro h0
  apply h
  have h1 : (m : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h0])
  rw [← map_natCast (residue R), h1, map_zero]

theorem torsionUnramified_pow_of_tateUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    {V : ValuationSubring Ω} {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {l : ℕ} [Fact l.Prime] (hl : (l : K) ≠ 0) (h : TateUnramified A V l) (n : ℕ) :
    TorsionUnramified A V (l ^ n) := by
  intro σ hσ x hx
  obtain ⟨t, rfl⟩ := GlobalTheory.T.tateModule_level_surjective_of_divisible l (ptOver K Ω ⟶ A) (GlobalTheory.T.abelianVariety_sepClosed_point_divisible K Ω A hA l hl) n x hx
  rw [← lev_galTate, h σ hσ]
  rfl

theorem infinite_torsionUnramified_of_tateUnramified :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
      [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (V : ValuationSubring Ω), IsAbove R K V.toSubring →
      ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l →
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _ A _ _ hA l hp hl h
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hp.out.two_le) fun n => ⟨?_, ?_⟩
  · rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  · exact torsionUnramified_pow_of_tateUnramified hA (natCast_ne_zero_of_residue hl) h n

end GlobalTheory.AbVarRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramifiedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_torsionUnramified_of_tateModuleUnramified : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l → {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  first | exact @GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | exact GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified | (intros; apply GlobalTheory.AbVarRed.infinite_torsionUnramified_of_tateUnramified <;> assumption)
end
end
