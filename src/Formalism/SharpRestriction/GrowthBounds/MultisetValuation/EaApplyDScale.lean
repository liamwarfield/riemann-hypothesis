module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaDegreeMapDomain
section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GainOfCapacityLoss
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section Idx

variable {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

theorem ea_eS_val (s : Fin n') : (ea_eS hn s).val = s.val := by
  show (((s.val : ℕ) : ZMod (2 * ν))).val = s.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hn ▸ s.isLt)]

theorem ea_eS_posAdd (s : Fin n') (k : ℕ) : ea_eS hn (posAdd s k) = ea_eS hn s + (k : ZMod (2 * ν)) := by
  subst hn
  show (((s.val + k) % (2 * ν) : ℕ) : ZMod (2 * ν)) = (s.val : ZMod (2 * ν)) + k
  rw [ZMod.natCast_mod, Nat.cast_add]

theorem ea_eS_sub_val (s s' : Fin n') : (ea_eS hn s' - ea_eS hn s).val = (s'.val + n' - s.val) % n' := by
  subst hn
  have hle : s.val ≤ s'.val + 2 * ν := by have := s.isLt; omega
  show (((s'.val : ℕ) : ZMod (2 * ν)) - ((s.val : ℕ) : ZMod (2 * ν))).val = _
  rw [← ZMod.val_natCast (n := 2 * ν) (s'.val + 2 * ν - s.val)]
  congr 1
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]

end Idx

theorem ea_card_fin (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun c : Fin N => P c.val).card = ((range N).filter P).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.isLt, hc⟩
  · rintro ⟨hx, hP⟩
    exact ⟨⟨x, hx⟩, hP, rfl⟩

theorem ea_lg (p x : ℕ) : Formalism.InvariantFactorPaths.G7.lgN p x = lgp p (x : ℤ) := by
  unfold Formalism.InvariantFactorPaths.G7.lgN lgp
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ} {ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

def ea_cN (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : ZMod (2 * ν)) : ℕ :=
  (nu t lam0 w J ((ea_eS hn).symm s) 1).toNat

def ea_hT (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : ZMod (2 * ν))
    (x : Fin (ea_cN hn t lam0 w J s)) : ℕ := ea_colH t lam0 w J ((ea_eS hn).symm s) x.val

def ea_tT (TT : Finset (Fin n')) : Finset (ZMod (2 * ν)) := TT.map (ea_eS hn).toEmbedding

theorem ea_mem_tT (s : ZMod (2 * ν)) : s ∈ ea_tT hn TT ↔ (ea_eS hn).symm s ∈ TT := by
  unfold ea_tT
  rw [Finset.mem_map_equiv]

variable (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m)

include h hJ1 hJ

theorem ea_alG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      al TT lam0 ((ea_eS hn).symm s) := by
  unfold Formalism.InvariantFactorPaths.G7.alG al
  by_cases hs : (ea_eS hn).symm s ∈ TT
  · rw [if_pos ((ea_mem_tT hn s).2 hs), if_pos hs]
    have e := ea_card_fin (ea_cN hn t lam0 w J s) (fun x => ea_colH t lam0 w J ((ea_eS hn).symm s) x = 1)
    unfold ea_hT
    rw [e]
    exact ea_card_one h hJ1 hJ _
  · rw [if_neg (fun h' => hs ((ea_mem_tT hn s).1 h')), if_neg hs]
    rfl

theorem ea_cN_cast (s : ZMod (2 * ν)) :
    ((ea_cN hn t lam0 w J s : ℕ) : ℤ) = nu t lam0 w J ((ea_eS hn).symm s) 1 :=
  Int.toNat_of_nonneg (ea_nu_nonneg h hJ1 hJ _ 1)

theorem ea_al_eq (s : Fin n') (hs : s ∈ TT) : al TT lam0 s = nu t lam0 w J s 1 - nu t lam0 w J s 2 := by
  have hk : 2 ≤ k1 + 1 := by
    have := h.two_r
    have := h.r_pos
    omega
  unfold al
  rw [if_pos hs, ea_nu_head J s le_rfl (by omega), ea_nu_head J s (by omega : 1 ≤ 2) hk]
  ring

theorem ea_capG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      cap t TT lam0 w J ((ea_eS hn).symm s) := by
  have hA := ea_alG hn h hJ1 hJ s
  have hC := ea_cN_cast hn h hJ1 hJ s
  unfold Formalism.InvariantFactorPaths.G7.capG cap
  by_cases hs : (ea_eS hn).symm s ∈ TT
  · rw [if_pos hs]
    have hal := ea_al_eq h hJ1 hJ _ hs
    have h2 := ea_nu_nonneg h hJ1 hJ ((ea_eS hn).symm s) 2
    have hle : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s ≤
        ea_cN hn t lam0 w J s := by
      have : ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) ≤
          ((ea_cN hn t lam0 w J s : ℕ) : ℤ) := by rw [hA, hC, hal]; omega
      exact_mod_cast this
    rw [Nat.cast_sub hle, hA, hC, hal]
    ring
  · rw [if_neg hs]
    have h0 : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s = 0 := by
      unfold Formalism.InvariantFactorPaths.G7.alG
      rw [if_neg (mt (ea_mem_tT hn s).1 hs)]
    rw [h0, Nat.sub_zero, hC]

theorem ea_lsG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      lsz t TT lam0 w J ((ea_eS hn).symm s) := by
  have hle : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s ≤
      ∑ c : Fin (ea_cN hn t lam0 w J s), ea_hT hn t lam0 w J s c := by
    unfold Formalism.InvariantFactorPaths.G7.alG
    split_ifs
    · rw [Finset.card_filter]
      exact Finset.sum_le_sum fun c _ => by split_ifs with h1 <;> omega
    · exact Nat.zero_le _
  unfold Formalism.InvariantFactorPaths.G7.lsG lsz
  rw [Nat.cast_sub hle, ea_alG hn h hJ1 hJ s, ← ea_sum_colH h hJ1 hJ]
  congr 2
  unfold ea_hT ea_cN
  exact Fin.sum_univ_eq_sum_range (fun x => ea_colH t lam0 w J ((ea_eS hn).symm s) x) _

end Num

section Num2

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ} {ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

theorem ea_dSet (s : Fin n') : Formalism.InvariantFactorPaths.G7.dSet (ea_tT hn TT) (ea_eS hn s) = dSet TT s := by
  unfold Formalism.InvariantFactorPaths.G7.dSet dSet ea_tT
  rw [Finset.filter_map, Finset.map_eq_image, Finset.image_image]
  congr 1
  · funext s'
    simp only [Function.comp_apply, Equiv.coe_toEmbedding]
    rw [ea_eS_sub_val]
  · ext s'
    simp only [Finset.mem_filter, Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]

theorem ea_sum_tT {M : Type} [AddCommMonoid M] (f : ZMod (2 * ν) → M) :
    ∑ s ∈ ea_tT hn TT, f s = ∑ s ∈ TT, f (ea_eS hn s) := Finset.sum_map _ _ _

variable (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m)

include h hJ1 hJ

theorem ea_alG_R (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℝ) =
      (al TT lam0 ((ea_eS hn).symm s) : ℝ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (ea_alG hn h hJ1 hJ s)

theorem ea_capG_R (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℝ) =
      (cap t TT lam0 w J ((ea_eS hn).symm s) : ℝ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (ea_capG hn h hJ1 hJ s)

theorem ea_deLoss :
    Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
      (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
      (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J)) = de p t TT lam0 w J := by
  have hal : ∀ s, ((Formalism.InvariantFactorPaths.G7.lgN p (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J)
      (ea_hT hn t lam0 w J) s) : ℕ) : ℝ) = (lgp p (al TT lam0 ((ea_eS hn).symm s)) : ℝ) := by
    intro s; rw [ea_lg, ea_alG hn h hJ1 hJ s]
  have hls : ∀ s, ((Formalism.InvariantFactorPaths.G7.lgN p (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J)
      (ea_hT hn t lam0 w J) s) : ℕ) : ℝ) = (lgp p (lsz t TT lam0 w J ((ea_eS hn).symm s)) : ℝ) := by
    intro s; rw [ea_lg, ea_lsG hn h hJ1 hJ s]
  unfold Formalism.InvariantFactorPaths.G7.deLoss de
  congr 1
  · rw [← (ea_eS hn).sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hal, hls, Equiv.symm_apply_apply]
  · rw [ea_sum_tT hn]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hal, Equiv.symm_apply_apply]

theorem gain_of_capacity_loss :
    Formalism.GrowthSums.excessGain (p : ℝ) (ea_tT hn TT) (Formalism.InvariantFactorPaths.G7.dSet (ea_tT hn TT))
      (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
        (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
        (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))) = gA p t TT lam0 w J := by
  unfold Formalism.GrowthSums.excessGain gA
  rw [ea_deLoss hn h hJ1 hJ, ea_sum_tT hn]
  simp only [← ea_eS_posAdd hn, ea_dSet hn, ea_alG_R hn h hJ1 hJ, ea_capG_R hn h hJ1 hJ,
    Equiv.symm_apply_apply]

theorem ea_gainG :
    Formalism.GrowthSums.gainG (p : ℝ) (ea_tT hn TT) (Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT))
      (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
        (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
        (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))) = gB p t TT lam0 w J := by
  have hodd : Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) = (TT.filter fun s => IsOddPos s).map (ea_eS hn).toEmbedding := by
    unfold Formalism.InvariantFactorPaths.G7.oddT ea_tT
    rw [Finset.filter_map]
    congr 1
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]
    exact Iff.rfl
  have hg : Formalism.GrowthSums.gamP (p : ℝ) = gam p := by
    unfold Formalism.GrowthSums.gamP Formalism.GrowthSums.rhoP gam; ring
  unfold Formalism.GrowthSums.gainG gB
  rw [ea_deLoss hn h hJ1 hJ, ea_sum_tT hn, hodd, Finset.sum_map, hg]
  simp only [Equiv.coe_toEmbedding, ← ea_eS_posAdd hn, ea_alG_R hn h hJ1 hJ, ea_capG_R hn h hJ1 hJ,
    Equiv.symm_apply_apply]

theorem ea_sumEven :
    ∑ s ∈ ea_tT hn TT \ Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT),
      (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ) =
      ((∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), al TT lam0 s : ℤ) : ℝ) := by
  have hodd : Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) = (TT.filter fun s => IsOddPos s).map (ea_eS hn).toEmbedding := by
    unfold Formalism.InvariantFactorPaths.G7.oddT ea_tT
    rw [Finset.filter_map]
    congr 1
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]
    exact Iff.rfl
  have hev : ea_tT hn TT \ Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) =
      (TT.filter fun s => ¬ IsOddPos s).map (ea_eS hn).toEmbedding := by
    rw [hodd]
    unfold ea_tT
    rw [← Finset.map_sdiff]
    congr 1
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hev, Finset.sum_map, Int.cast_sum]
  simp only [Equiv.coe_toEmbedding, ea_alG_R hn h hJ1 hJ, Equiv.symm_apply_apply]

end Num2

theorem ea_brNum {p : ℕ} [Fact p.Prime] (X : Sys p) : ea_BrNum X := by
  intro v j hj
  exact ⟨gain_of_capacity_loss (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj,
    ea_gainG (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj,
    ea_sumEven (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Res

variable {ι κ R : Type} [CommRing R] (f : κ → ι)

theorem ea_coeff_resV (a : MvPowerSeries ι R) (n : κ →₀ ℕ) :
    MvPowerSeries.coeff n (resV f a) = MvPowerSeries.coeff (n.mapDomain f) a := rfl

variable {f} (hf : Function.Injective f)

include hf

theorem ea_resV_mul (a b : MvPowerSeries ι R) : resV f (a * b) = resV f a * resV f b := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  simp_rw [ea_coeff_resV]
  symm
  refine Finset.sum_nbij' (fun q => (q.1.mapDomain f, q.2.mapDomain f))
    (fun q => (q.1.comapDomain f hf.injOn, q.2.comapDomain f hf.injOn)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.mapDomain_add, hq]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.comapDomain_add_of_injective hf, hq, Finsupp.comapDomain_mapDomain f hf]
  · intro q _
    simp only [Finsupp.comapDomain_mapDomain f hf]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hs : ∀ m : ι →₀ ℕ, m ≤ n.mapDomain f → (↑m.support : Set ι) ⊆ Set.range f := by
      intro m hm x hx
      have hx' : x ∈ (n.mapDomain f).support := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff] at hx
        rw [Finsupp.mem_support_iff]
        have := hm x
        omega
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx')
      exact ⟨y, rfl⟩
    have h1 : q.1 ≤ n.mapDomain f := hq ▸ le_self_add
    have h2 : q.2 ≤ n.mapDomain f := hq ▸ le_add_self
    ext1
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h1)
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h2)
  · intro q _
    rfl

theorem ea_resV_C (c : R) : resV f (MvPowerSeries.C c : MvPowerSeries ι R) = MvPowerSeries.C c := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  have h : n.mapDomain f = 0 ↔ n = 0 := by
    constructor
    · intro h
      exact Finsupp.mapDomain_injective hf (by rw [h, Finsupp.mapDomain_zero])
    · rintro rfl
      exact Finsupp.mapDomain_zero
  by_cases hn : n = 0
  · rw [if_pos (h.2 hn), if_pos hn]
  · rw [if_neg (mt h.1 hn), if_neg hn]

def ea_resHom : MvPowerSeries ι R →+* MvPowerSeries κ R where
  toFun := resV f
  map_one' := by
    have := ea_resV_C hf (1 : R)
    rwa [map_one, map_one] at this
  map_mul' := ea_resV_mul hf
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ea_resHom_apply (a : MvPowerSeries ι R) : ea_resHom hf a = resV f a := rfl

omit hf in
theorem ea_resV_atPi (vp : R) (a : MvPowerSeries ι R) : resV f (atPi vp a) = atPi vp (resV f a) := by
  ext n
  rw [ea_coeff_resV]
  simp only [atPi, MvPowerSeries.coeff_apply, resV, Finsupp.degree_mapDomain]

end Res

theorem ea_atPi_subst {σ R : Type} [CommRing R] (vp : R) (a : MvPowerSeries σ R) :
    MvPowerSeries.subst (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) a = atPi vp a := by
  have h : (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) =
      (Function.const σ vp) • MvPowerSeries.X := by
    funext x
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst]
  ext n
  rw [MvPowerSeries.coeff_rescale]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, atPi,
    MvPowerSeries.coeff_apply, Finsupp.degree]
  rfl

theorem ea_eS_posSub {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν) (s : Fin n') (d : ℕ) :
    ea_eS hn (posSub s d) = ea_eS hn s - (d : ZMod (2 * ν)) := by
  subst hn
  have hd : d ≤ (s : ℕ) + 2 * ν * d :=
    le_add_left (Nat.le_mul_of_pos_left d (by have := NeZero.pos ν; omega))
  show ((((s : ℕ) + 2 * ν * d - d) % (2 * ν) : ℕ) : ZMod (2 * ν)) = ((s : ℕ) : ZMod (2 * ν)) - (d : ZMod (2 * ν))
  have h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0 := ZMod.natCast_self _
  rw [ZMod.natCast_mod, Nat.cast_sub hd]
  push_cast at h0 ⊢
  rw [h0]
  ring

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  intro y z h
  simp only [ea_eps, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext ((ea_e X v).symm.injective h1) (Prod.ext h2 h3)

theorem ea_res_sSA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) :
    resV (ea_eps X v j) (X.sSA K' j v s a b) = Formalism.InvariantFactorPaths.G7.sPos p (ea_e X v s) (a, b) := by
  classical
  have key : ∀ l : ℕ, ea_eps X v j (ea_e X v s - 2 * (l : ZMod _), a, b) =
      (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) := by
    intro l
    simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true]
    rw [Equiv.symm_apply_eq]
    simp only [ea_e]
    rw [ea_eS_posSub]
    push_cast
    ring
  ext n
  rw [ea_coeff_resV]
  simp only [Sys.sSA, Formalism.InvariantFactorPaths.G7.sPos, MvPowerSeries.coeff_apply, Finsupp.degree_mapDomain]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs : (Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))) =
      Finsupp.mapDomain (ea_eps X v j) (Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)) := by
    rw [Finsupp.mapDomain_single, key l, pow_mul]
  have hiff : Finsupp.mapDomain (ea_eps X v j) n = Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l)) ↔
      n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l) := by
    rw [hs]
    exact (Finsupp.mapDomain_injective (ea_eps_inj X v j)).eq_iff
  by_cases h : n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

theorem ea_res_hhA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (u : Fin (X.G.P.n' v) → K') :
    resV (ea_eps X v j) (X.hhA K' j v u) = Formalism.InvariantFactorPaths.G7.hhS p fun s => u ((ea_e X v).symm s) := by
  rw [← ea_resHom_apply (ea_eps_inj X v j)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sys.hhA, map_sum, map_mul, map_pow, ea_resHom_apply, ea_resV_C (ea_eps_inj X v j),
    ea_res_sSA]
  simp only [Formalism.InvariantFactorPaths.G7.hhS, Fintype.sum_prod_type]
  refine Fintype.sum_equiv (ea_e X v) _ _ (fun s => ?_)
  rw [Equiv.symm_apply_apply]
  simp only [ea_e, ea_eS_posAdd, Nat.cast_one]

theorem ea_brClass : ea_BrClass X := by
  intro v j K' _ _ vp u F hF
  obtain ⟨g, hg, hc⟩ := hF
  rw [ea_atPi_subst, ← ea_resV_atPi, ← ea_res_hhA]
  refine ⟨fun i => resV (ea_eps X v j) (g i), fun i n => ?_, fun n => ?_⟩
  · rw [ea_coeff_resV]
    exact hg i _
  · rw [ea_coeff_resV, hc, Finsupp.degree_mapDomain]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← ea_resHom_apply (ea_eps_inj X v j), ← map_pow, ← map_mul]
    rw [ea_resHom_apply, ea_coeff_resV]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem ea_applyD_scale {σ τ K : Type} [Field K] (q E : ℕ) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) f = ((q : K) ^ E) • applyD P f := by
  classical
  have hc : ∀ n, AddMonoidAlgebra.coeff ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) n =
      (q : MvPolynomial τ ℤ) ^ E * AddMonoidAlgebra.coeff P n := by
    intro n
    have : (q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E = MvPolynomial.C ((q : MvPolynomial τ ℤ) ^ E) := by
      rw [map_pow, map_natCast]
    rw [this, MvPolynomial.coeff_C_mul]
  have hsub : ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P).support ⊆ P.support := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, hc] at hn
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, mul_zero] at hn
    exact hn rfl
  unfold applyD
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.notMem_support_iff.1 hn, map_zero, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc, map_mul, map_pow, map_natCast, smul_comm]
  congr 1
  rw [MvPolynomial.smul_eq_C_mul, map_pow, map_natCast]

theorem ea_applyD_zero {σ τ K : Type} [Field K] (f : MvPowerSeries σ K) :
    applyD (0 : MvPolynomial σ (MvPolynomial τ ℤ)) f = 0 := by
  unfold applyD
  rw [MvPolynomial.support_zero, Finset.sum_empty]

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_PIvS_eq (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^
      (∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I i0 v s c) * X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem ea_colFac_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ)
    (h : ¬ Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) : X.colFac j I v s c = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨x, y, hxy, hne⟩ := h
  unfold Sys.colFac
  refine Matrix.det_zero_of_column_eq hne fun k => ?_
  show (∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c x.val)⟩ : X.ZA j)) =
    ∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c y.val)⟩ : X.ZA j)
  have hxy' : I v s c x.val = I v s c y.val := hxy
  rw [hxy']

theorem ea_card_img {H N : ℕ} (g : Fin H → Fin N) (hg : Function.Injective g) (i : ℕ) :
    ((univ.image g) ∩ univ.filter (fun b : Fin N => b.val < i)).card =
      (univ.filter fun x : Fin H => (g x).val < i).card := by
  rw [← Finset.card_image_of_injective _ hg]
  congr 1
  ext b
  simp only [mem_inter, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, rfl⟩, hb⟩
    exact ⟨x, hb, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩

theorem ea_Exp_eq (v : X.Pl) (j i : ℕ) (I : X.ColCh j)
    (h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) :
    ∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I (fun _ => i) v s c =
      ea_Exp X v j i I := by
  unfold ea_Exp
  refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
  rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := ea_card_img (ea_Ic X v j I s' c) (h ((ea_e X v).symm s') c.val) i
  have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
    (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
  have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
      univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
      ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
        fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
  rw [e3]
  unfold Sys.colExp
  have hv : ((ea_e X v).symm s').val = s'.val := rfl
  by_cases hodd : s'.val % 2 = 0
  · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
    rfl
  · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]

theorem ea_brScale : ea_BrScale X := by
  intro v j i K' _ F I n
  by_cases h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), c ∈ range (X.nuv v (j + 1) s 1).toNat →
      X.colFac j I v s c ≠ 0
  · by_cases h2 : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ),
        Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val
    · right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul, ea_Exp_eq X v j i I h2]
    ·
      right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul]
      congr 2
      unfold ea_Exp
      refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
      rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hinj : Function.Injective fun i' : Fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) =>
          I v ((ea_e X v).symm s') c.val i'.val := by
        by_contra hni
        exact h _ c.val (mem_range.2 c.isLt) (ea_colFac_zero X j I v _ _ hni)
      have e1 := ea_card_img (ea_Ic X v j I s' c) hinj i
      have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
        (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
      have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
          univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
          ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
            fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
      rw [e3]
      unfold Sys.colExp
      have hv : ((ea_e X v).symm s').val = s'.val := rfl
      by_cases hodd : s'.val % 2 = 0
      · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
        rfl
      · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]
  · left
    push Not at h
    obtain ⟨s, c, hc, h0⟩ := h
    have hz : PIvS X j I (fun _ => i) v = 0 := by
      unfold PIvS
      refine Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero hc ?_)
      rw [h0, mul_zero]
    rw [hz, ea_applyD_zero, MvPolynomial.coeff_zero]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
