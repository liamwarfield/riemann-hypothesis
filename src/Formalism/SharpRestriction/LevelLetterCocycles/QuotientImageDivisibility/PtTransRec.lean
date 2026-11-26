module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc


set_option maxHeartbeats 800000 in
theorem ptTrans_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => PtTrans ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA hl5
  set W := (HW l).W K 1 LL hA.2.2 with hW
  intro ζ ζ' hζ hζ'
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at hζ hζ'
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA
  have hv : (D.loc l).v LL ((l : ℕ) : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hvO := (D.loc l).v_O LL
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h; rw [h, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv

  have hcong : ∀ δ : ↥W.DelF, ∃ a : ℕ,
      ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL
        (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (a : ↥LL.1)) := by
    intro δ
    obtain ⟨g, hg⟩ := W.resΓ_onto δ
    obtain ⟨a, ha, -⟩ := (D.loc l).χQ_cyc (g : GQ l) 1 ((D.loc l).ζQ 1)
      (by rw [pow_one]; exact (Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l).pow_eq_one)
    refine ⟨a, ?_⟩
    have hres := W.χΓ_res g
    have hPD := (D.loc l).PD_χ K g
    rw [← hg, hres, hPD]
    set t : ℚ_[l] := ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l]) with ht
    have hlQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    have e : algebraMap ℚ_[l] ↥LL.1 ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ↥LL.1) =
        ((l : ℕ) : ↥LL.1) * algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) := by
      rw [map_div₀, map_natCast, mul_div_cancel₀ _ hl0, ht, map_sub, map_natCast]
    rw [e, AddValuation.map_mul, hv]
    have hz : ‖t / (l : ℚ_[l])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one (by positivity)]
      have := ha
      simpa [zpow_neg, zpow_one] using this
    have hint : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) ∈ OL LL := by
      have e2 : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) =
          algebraMap ℤ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l]) :=
        (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).symm
      rw [e2]
      exact (algebraMap ℤ_[l] ↥(OL LL) (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).2
    exact le_add_of_nonneg_right ((hvO _).2 hint)
  choose aδ haδ using hcong

  have hvunit : ∀ w : (↥(OL LL))ˣ, (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 := by
    intro w
    have h1 := (hvO (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2
    have h2 := (hvO (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2
      ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
    have h3 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1
  have hne : ∀ δ, ((aδ δ : ℕ) : ZMod l) ≠ 0 := by
    intro δ h
    rw [ZMod.natCast_eq_zero_iff] at h
    obtain ⟨c, hc⟩ := h
    have hva : (1 : WithTop ℚ) ≤ (D.loc l).v LL ((aδ δ : ℕ) : ↥LL.1) := by
      rw [hc, Nat.cast_mul, AddValuation.map_mul, hv]
      exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
    have hsum := AddValuation.map_add ((D.loc l).v LL)
      (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (aδ δ : ↥LL.1))
      ((aδ δ : ℕ) : ↥LL.1)
    rw [sub_add_cancel, hvunit] at hsum
    have h1 := haδ δ
    rw [Nat.cast_one] at h1
    exact absurd hsum (not_le.2 (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_min h1 hva)))
  let U : ↥W.DelF → (ZMod l)ˣ := fun δ => Units.mk0 _ (hne δ)
  have hUinj : Function.Injective U := by
    intro δ δ' h
    have h1 : ((aδ δ : ℕ) : ZMod l) = ((aδ δ' : ℕ) : ZMod l) := congrArg Units.val h
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    set χd := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL))
    set χd' := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ' : ↥(OL LL))

    have hdiff : (1 : WithTop ℚ) ≤ (D.loc l).v LL (χd - χd') := by
      have e : χd - χd' = (χd - (aδ δ : ↥LL.1)) - (χd' - (aδ δ' : ↥LL.1)) +
          ((aδ δ : ↥LL.1) - (aδ δ' : ↥LL.1)) := by ring
      rw [e]
      have hA1 := haδ δ
      have hA2 := haδ δ'
      rw [Nat.cast_one] at hA1 hA2
      refine le_trans (le_min (le_trans (le_min hA1 hA2) (AddValuation.map_sub ((D.loc l).v LL) _ _)) ?_)
        (AddValuation.map_add ((D.loc l).v LL) _ _)

      rcases le_total (aδ δ') (aδ δ) with hle | hle
      · have hd : l ∣ aδ δ - aδ δ' := (Nat.modEq_iff_dvd' hle).1 h1.symm
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = ((aδ δ - aδ δ' : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]
        rw [e2, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
      · have hd : l ∣ aδ δ' - aδ δ := (Nat.modEq_iff_dvd' hle).1 h1
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = -((aδ δ' - aδ δ : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]; ring
        rw [e2, AddValuation.map_neg, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)

    set g := (δ : W.Gam) * (δ' : W.Gam)⁻¹
    have hξ : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = χd * χd'⁻¹ := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      rw [eq_mul_inv_iff_mul_eq₀ hχ'0]
      simp only [χd, χd', g, ← map_mul, ← Units.val_mul, ← map_mul (W.χΓ), inv_mul_cancel_right]
    have hξ1 : (1 : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      have e : χd * χd'⁻¹ - 1 = (χd - χd') * χd'⁻¹ := by field_simp
      rw [hξ, e, AddValuation.map_mul]
      have hinv : (D.loc l).v LL χd'⁻¹ = 0 := by
        have := hvunit (W.χΓ δ')⁻¹
        simpa [χd', map_inv₀] using this
      rw [hinv, add_zero]
      exact hdiff

    obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 δ.2
    obtain ⟨k', hk', hδk'⟩ := (W.DelF_def δ').1 δ'.2
    have hgk : g ^ (k * k') = 1 := by
      simp only [g, mul_pow, inv_pow]
      rw [pow_mul, hδk, one_pow, one_mul, mul_comm k k', pow_mul, hδk', one_pow, inv_one]
    have hξk : (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) ^ (k * k') = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hgk, map_one, Units.val_one, map_one]
    have hl3 : 3 ≤ l := by omega
    have hξeq : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = 1 := by
      by_contra hne1
      exact Formalism.MainNotions.N.Pv.LocalLengthBound.Val.pow_ne_one_of_close ((D.loc l).v LL) (Fact.out : l.Prime) hv hl3
        (k * k') _ (Nat.mul_pos hk hk') hξ1 hne1 hξk
    have hg1 : g = 1 := by
      apply W.χΓ_inj
      rw [map_one]
      apply Units.ext
      apply Subtype.val_injective
      simpa using hξeq
    exact Subtype.ext (mul_inv_eq_one.1 hg1)
  have hUbij : Function.Bijective U := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hUinj, by rw [Fintype.card_coe, hcard, ZMod.card_units]⟩

  obtain ⟨b, hb, hζb⟩ := hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hb0 : ((b : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : b = 0 := Nat.eq_zero_of_dvd_of_lt hd hb
    subst this
    rw [pow_zero] at hζb
    exact hζ'.ne_one (Fact.out : l.Prime).one_lt hζb.symm
  obtain ⟨δ, hδ⟩ := hUbij.2 (Units.mk0 _ hb0)
  have h1 : ((aδ δ : ℕ) : ZMod l) = ((b : ℕ) : ZMod l) := congrArg Units.val hδ
  rw [ZMod.natCast_eq_natCast_iff] at h1
  have hpowmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % l) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m l, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  refine ⟨δ, δ.2, aδ δ, ?_, haδ δ⟩
  rw [hpowmod, h1, ← hpowmod, hζb]

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSZeroSplit
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section LemK

variable {LL' : Type} [Field LL'] {V : Type} [AddCommGroup V] [Module LL' V]

theorem smulS_zero_split {Fil : ℤ → Submodule LL' V} (hFa : Antitone Fil) {M : ℤ} {f : ℤ → V}
    (hf : LB M f) (hneg : ∀ k : ℤ, k < 0 → f k ∈ Fil (-k)) (g : PowerSeries LL') :
    smulS g f 0 - PowerSeries.constantCoeff g • f 0 ∈ Fil 1 := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (0 : ℤ) - M < (N + 1 : ℕ) :=
    ⟨(0 - M).toNat, by have := Int.self_le_toNat (0 - M); push_cast; omega⟩
  rw [smulS_eq_sum hf g 0 (N + 1) hN, Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    add_sub_cancel_right]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have h := hneg ((0 : ℤ) - ((i + 1 : ℕ) : ℤ)) (by push_cast; omega)
  exact hFa (show (1 : ℤ) ≤ -((0 : ℤ) - ((i + 1 : ℕ) : ℤ)) by push_cast; omega) h

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem chi_zpow_ne_one (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (k : ℤ) (hk : k ≠ 0) :
    (algebraMap O LL (W.χΓ W.gam : O)) ^ k ≠ 1 := by
  have hs : W.s = 1 := hA.2.1
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  have h1 : (1 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1) := le_of_eq hg.symm
  have hne : algebraMap O LL (W.χΓ W.gam : O) ≠ 1 := by
    intro h
    rw [h, sub_self, AddValuation.map_zero] at hg
    exact WithTop.top_ne_coe hg
  have hp3 : 3 ≤ PD.p := by have := PD.hp.two_le; have := hA.2.2; omega
  exact Val.zpow_ne_one_of_close v PD.hp W.v_l hp3 _ h1 hne k hk

theorem lemK_of [NeZero n] (hdom : IsDomain O) (hFr : IsFractionRing O LL)
    (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hN : GamN W) (hA' : GamA W) (hΓ : GamNΔ W) (hΔ : PtTrans W) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := by
  intro hA T hT i ζ hζ x d hDL hd ⟨j, hj⟩
  have hp := p_ne_zero_LL W
  obtain ⟨-, -, hAdd, hO, -, hGam, -⟩ := expRules_of W h4 hN hA' hA T hT i ζ hζ
  have hCr := expCritN_of W hA hdom hFr h1 h3 h4 h5 hD hR hΓ hΔ T hT i ζ hζ x d hDL hd
  have hLv1 : ∀ (z : ↥(W.N T)) (k : ℤ), W.levN T i ζ z k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k) :=
    (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1
  have hFl : Antitone (Formalism.MainNotions.WachCoordinates.FilLev W T i 0) := Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0
  have hcoef : ∀ k : ℤ, k ≠ 0 → d k ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k) := by
    intro k hk
    have hE := hO (((PD.p : ℕ) : O) ^ j) _ _ (hAdd _ _ _ _ (hGam x d hd) (hO (-1) x d hd))
    have hz : ((PD.p : ℕ) : O) ^ j • (W.γ T x + (-1 : O) • x) ∈ W.N T := by
      rw [neg_one_smul, ← sub_eq_add_neg]; exact hj
    have huq := congrFun (isExp_unique W T i ζ hE (isExp_self W T i ζ hz)) k
    have hmem := hLv1 ⟨_, hz⟩ k
    rw [← huq] at hmem
    simp only [Pi.add_apply] at hmem
    have e : algebraMap O LL (((PD.p : ℕ) : O) ^ j) •
        ((algebraMap O LL (W.χΓ W.gam : O)) ^ k • d k + algebraMap O LL (-1) • d k) =
        (algebraMap O LL (((PD.p : ℕ) : O) ^ j) * ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1)) •
          d k := by
      rw [map_neg, map_one, neg_one_smul, ← sub_eq_add_neg, mul_smul, sub_smul, one_smul]
    have hc0 : algebraMap O LL (((PD.p : ℕ) : O) ^ j) *
        ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1) ≠ 0 := by
      refine mul_ne_zero ?_ (sub_ne_zero.2 (chi_zpow_ne_one W hA k hk))
      rw [map_pow, map_natCast]; exact pow_ne_zero _ hp
    rw [e] at hmem
    have := (Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-k)).smul_mem
      (algebraMap O LL (((PD.p : ℕ) : O) ^ j) * ((algebraMap O LL (W.χΓ W.gam : O)) ^ k - 1))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine ⟨hcoef, fun y hy => ⟨?_, ?_⟩⟩
  · obtain ⟨u, hu, hlq⟩ := (expRing_of W hR hA i ζ hζ).1
    obtain ⟨m, hm⟩ := hd.1
    have hEq := isExp_unique W T i ζ (isExp_self W T i ζ hy) (isExp_smulA W T i ζ hd _)
    have hc := hLv1 ⟨_, hy⟩ (y : ℤ)
    rw [hEq, map_pow, hlq, mul_pow, mul_comm, smulS_mul hm, smulS_X_pow (LB_smulS hm _)] at hc
    simp only [sub_self] at hc
    have hsplit := smulS_zero_split hFl hm (fun k hk => hcoef k (by omega)) (u ^ y)
    have h2 : PowerSeries.constantCoeff (u ^ y) • d 0 ∈ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-(y : ℤ)) := by
      have := Submodule.sub_mem _ hc (hFl (show -(y : ℤ) ≤ 1 by omega) hsplit)
      rwa [sub_sub_cancel] at this
    have hcu : PowerSeries.constantCoeff (u ^ y) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero
    have := (Formalism.MainNotions.WachCoordinates.FilLev W T i 0 (-(y : ℤ))).smul_mem
      (PowerSeries.constantCoeff (u ^ y))⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hcu, one_smul] at this
  · constructor
    · intro hx
      have := (hCr ⟨y, hy⟩).1 hx 0
      simpa using this
    · intro h0
      refine (hCr ⟨y, hy⟩).2 fun k => ?_
      by_cases hk : k = 0
      · subst hk; simpa using h0
      · exact hcoef k hk

end LemK

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
