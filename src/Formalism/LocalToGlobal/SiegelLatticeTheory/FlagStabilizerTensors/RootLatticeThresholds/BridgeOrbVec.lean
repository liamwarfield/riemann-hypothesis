module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelFifth

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVec
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

section Std

variable {K : Type} [Field K] (σ : K →+* ℂ) (r : ℕ) (g : ℝ)

theorem blk_std (s o : ℕ) (hs : 1 ≤ s) (hos : o + s ≤ r + 1) :
    blkF (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o (o + s - 1) * (-1) ^ (r + 1 - (o + 1 + s - 1)) =
      (((g / (2 * Real.pi)) ^ Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) := by
  set a : ℝ := g / (2 * Real.pi)
  set m := (r - o) + (r - (o + s - 1)) with hm
  set e := r + 1 - (o + 1 + s - 1) with he
  have hnu : Formalism.FourierDecayAlt.S6.nuBlock (r : ℤ) ((o + 1 : ℕ) : ℤ) (s : ℤ) = (m : ℤ) := by
    unfold Formalism.FourierDecayAlt.S6.nuBlock; rw [hm]; push_cast; omega
  have hme : m = 2 * e + (s - 1) := by rw [hm, he]; omega
  rw [hnu, zpow_natCast]
  unfold blkF
  rw [← hm, mul_pow, ← mul_assoc, ← mul_pow, neg_mul, one_mul, neg_neg, Complex.ofReal_pow, hme, pow_add, pow_mul,
    Complex.I_sq]
  have h1 : ((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e) = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have h2 : ((-1 : ℂ) ^ e) = (-1) ^ e := rfl
  calc (-1 : ℂ) ^ e * Complex.I ^ (s - 1) * (a : ℂ) ^ (2 * e + (s - 1)) * (-1) ^ e
      = (((-1 : ℂ) ^ e) * ((-1 : ℂ) ^ e)) * ((a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1)) := by ring
    _ = (a : ℂ) ^ (2 * e + (s - 1)) * Complex.I ^ (s - 1) := by rw [h1, one_mul]

theorem lptOf_toStd : ∀ (L : Formalism.FourierDecayAlt.TB.Pt K) (o : ℕ), (∀ b ∈ L, 1 ≤ b.1) → o + (L.map Prod.fst).sum ≤ r + 1 →
    lptOf σ (-Complex.I * ((g / (2 * Real.pi) : ℝ) : ℂ)) r o ((Formalism.L2.SG.DataInst.signAux r (o + 1) L).map Prod.swap) =
      Formalism.FourierDecayAlt.D.toStd r g (o + 1) (Formalism.FourierDecayAlt.C.loc σ L)
  | [], _, _, _ => rfl
  | (s, t) :: rest, o, hL, ho => by
    simp only [List.map_cons, List.sum_cons] at ho
    have hs : 1 ≤ s := hL (s, t) (List.mem_cons_self)
    simp only [Formalism.L2.SG.DataInst.signAux, List.map_cons, Prod.swap_prod_mk, lptOf, Formalism.FourierDecayAlt.C.loc,
      Formalism.FourierDecayAlt.D.toStd, List.cons.injEq, true_and]
    constructor
    · rw [map_mul, map_pow, map_neg, map_one, ← mul_assoc, blk_std r g s o hs (by omega)]
    · have := lptOf_toStd rest (o + s) (fun b hb => hL b (List.mem_cons_of_mem _ hb)) (by omega)
      rw [show o + s + 1 = o + 1 + s by omega] at this
      exact this

end Std

end Formalism.L2.SG.Pf.Bridge
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMS
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain

namespace Formalism.L2.SG.Pf.Carrier.EnergyMS

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.Carrier.EnergyConst Formalism.L2.SG.Pf.Carrier.EnergyConst2 Formalism.L2.SG.TypedSets Function

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def dN (v : PlX X) : ℝ := ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ)


open Classical in
def nT (v : PlX X) : ℝ :=
  if TypAt X v then ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1

end Defs

def MSOrd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, ¬ TypAt X v → localVolumeUnit X ψ v = dN X v ^ e1 D * ZZX X u u' ψ v

def MSTyp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ → IsStdChar ψ →
    ∀ v : PlX X, TypAt X v → 0 < ZZX X u u' ψ v →
      localVolumeUnit X ψ v = dN X v ^ e1 D * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) *
        ZZX X u u' ψ v

def DiffProd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    HasFiniteMulSupport (dN X) ∧ ∏ᶠ v, dN X v = |((NumberField.discr X.B.I.F : ℤ) : ℝ)|

def DiscRd : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), |((NumberField.discr X.B.I.F : ℤ) : ℝ)| = D.host.rdE ^ D.R.f

def TypNorm : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    ∏ p : TypX X, ((Ideal.absNorm p.1.asIdeal : ℕ) : ℝ) = ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ D.R.f

theorem lemmaMSStd_of (hO : MSOrd) (hT : MSTyp) (hD : DiffProd) (hR : DiscRd) (hN : TypNorm)
    {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : LemmaMSStd X u u' ψ := by
  classical
  intro hψ hstd hC
  set k := (D.R.rS + 1) * (2 * D.R.rS + 3) with hk
  have hZpos : ∀ v, 0 < ZZX X u u' ψ v := fun v => (hC.1 v).2.2.1
  have hU00m : Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) := hC.2.2.2.1
  have hZm : Multipliable (ZZX X u u' ψ) := hC.2.2.2.2.2.1
  have hloc : ∀ v, localVolumeUnit X ψ v = (dN X v ^ e1 D * nT X v) * ZZX X u u' ψ v := by
    intro v
    by_cases hv : TypAt X v
    · rw [hT D X u u' ψ hψ hstd v hv (hZpos v)]
      simp only [nT, if_pos hv]
    · rw [hO D X u u' ψ hψ hstd v hv]
      simp only [nT, if_neg hv, mul_one]
  obtain ⟨hDf, hDp⟩ := hD D X

  set s : Set (PlX X) := ↑(Formalism.L2.SG.TypedSets.typSet X.B.I.F (D.host.g 0) (D.host.g 1)) with hs
  have hnTs : Function.mulSupport (nT X) ⊆ s := by
    intro v hv
    by_contra h
    exact hv (by unfold nT; exact if_neg (show ¬ TypAt X v from h))
  have hnTf : HasFiniteMulSupport (nT X) := (Finset.finite_toSet _).subset hnTs
  have hAf : HasFiniteMulSupport (fun v => dN X v ^ e1 D * nT X v) := (hDf.pow _).mul hnTf

  have h1 : (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = ∏' v, localVolumeUnit X ψ v := by
    have hsm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : s → PlX X)) := Multipliable.of_finite
    have hscm : Multipliable ((localVolumeUnit X ψ) ∘ ((↑) : ↑sᶜ → PlX X)) := hU00m
    rw [← Multipliable.tprod_mul_tprod_compl hsm hscm, mul_comm]
    congr 1
    rw [tprod_fintype]
    rfl

  have h2 : ∏' v, localVolumeUnit X ψ v = (∏ᶠ v, (dN X v ^ e1 D * nT X v)) * ∏' v, ZZX X u u' ψ v := by
    rw [tprod_congr hloc, Multipliable.tprod_mul (multipliable_of_hasFiniteMulSupport hAf) hZm,
      tprod_eq_finprod hAf]

  have h3 : (∏ᶠ v, (dN X v ^ e1 D * nT X v)) =
      D.host.rdE ^ (D.R.f * e1 D) * ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) ^ (D.R.f * k) := by
    have hDpow : HasFiniteMulSupport (fun v => dN X v ^ e1 D) := hDf.pow _
    rw [finprod_mul_distrib hDpow hnTf, ← finprod_pow hDf, hDp, hR D X, ← pow_mul]
    congr 1
    rw [finprod_eq_prod_of_mulSupport_subset (nT X) hnTs, pow_mul, ← hN D X, ← Finset.prod_pow]
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun p _ => ?_
    unfold nT
    exact if_pos (show TypAt X p.1 from p.2)
  unfold LemmaMS
  show (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 = _ * (∏' v : PlX X, ZZX X u u' ψ v)
  rw [h1, h2, h3]

end Formalism.L2.SG.Pf.Carrier.EnergyMS
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyKM
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.Pf.Carrier

namespace Formalism.L2.SG.Pf.Carrier.EnergyKM

theorem gam_eq (k r : ℕ) (κ δ : ℝ) : Formalism.FourierDecayAlt.D.GamLev k r κ δ 0 =
    (∏ a : Fin r, κ ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ))) / δ ^ (r + 1) := by
  have hI : ∀ f : ℕ → ℝ, ∏ l ∈ Finset.Ioc 0 r, f l = ∏ i : Fin r, f (i.val + 1) := by
    intro f
    have hset : Finset.Ioc 0 r = Finset.Ico (0 + 1) (r + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) r, Finset.range_eq_Ico,
      Finset.prod_Ico_add' f 0 r 1, hset]
  unfold Formalism.FourierDecayAlt.D.GamLev
  rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Ioc, Nat.sub_zero,
    Finset.prod_Ioc_succ_top (Nat.zero_le r), hI]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, sub_self, mul_zero, zero_mul, neg_zero, zpow_zero, mul_one]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  have ha : a.val ≤ r := a.isLt.le
  simp only [Formalism.FourierDecayAlt.C.Mlev]
  push_cast [Nat.cast_sub ha]
  congr 1
  ring

theorem level_constant_mul_gamma (r k : ℕ) (g rd : ℝ) (hg : 0 < g) (hrd : 0 < rd) :
    (2 : ℝ) ^ (r + 1) * (∏ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^
      (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹) * Formalism.FourierDecayAlt.D.GamLev k r (Formalism.FourierDecayAlt.D.kapG g rd) (Formalism.FourierDecayAlt.D.deG g rd) 0 =
    rd ^ ((r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k)) * g ^ (3 * (r + 1)) := by
  rw [gam_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hper : ∀ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ *
      Formalism.FourierDecayAlt.D.kapG g rd ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ)) =
      rd ^ (4 * (r - a.val) * (2 * (r - a.val) + k)) := by
    intro a
    have hM : 2 * (r - a.val) * (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)) = 4 * (r - a.val) * (2 * (r - a.val) + k) := by
      unfold Formalism.QuantumDeterminants.Mdim
      rw [Nat.add_sub_cancel]
      ring
    rw [← pow_mul, hM, zpow_neg, zpow_natCast, ← mul_inv, ← mul_pow]
    unfold Formalism.FourierDecayAlt.D.kapG
    rw [show g / (2 * Real.pi) * (2 * Real.pi / (g * rd)) = rd⁻¹ by field_simp, inv_pow, inv_inv]
  rw [mul_div_assoc', mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun a _ => hper a),
    Finset.prod_pow_eq_pow_sum]
  unfold Formalism.FourierDecayAlt.D.deG
  rw [div_pow, div_div_eq_mul_div, pow_add]
  field_simp
  ring

theorem three_dvd (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, r = 3 * q ∨ r = 3 * q + 1 ∨ r = 3 * q + 2 := ⟨r / 3, by omega⟩
  · subst hq
    exact ⟨(3 * q + 1) * (24 * q ^ 2 + 10 * q + 1), by ring⟩
  · subst hq
    exact ⟨(3 * q + 2) * (2 * q + 1) * (12 * q + 7), by ring⟩
  · subst hq
    exact ⟨(q + 1) * (8 * (3 * q + 2) ^ 2 + 10 * (3 * q + 2) + 3), by ring⟩

theorem sum_closed (r k : ℕ) :
    3 * ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) = 4 * r * (r + 1) * (2 * r + 1) + 6 * k * r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem exp_eq (r k : ℕ) (hk : 1 ≤ k) :
    (r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      2 * r * (r + 1) * (k - 1) + (r + 1) * (8 * r ^ 2 + 10 * r + 3) / 3 := by
  have hs : ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 4 * (r - i) * (2 * (r - i) + k)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hj' : r - (r - 1 - j) = j + 1 := by omega
    simp only [hj']
  have h3 := sum_closed r k
  obtain ⟨W, hW⟩ := three_dvd r
  rw [hs, hW, Nat.mul_div_cancel_left W (by norm_num : 0 < 3)]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith [h3, hW]

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem kMatch_holds (P : Parts X u u') : EnergyPlace.KMatch P := by
  intro hg hrd hr hk hgpos hk1
  have hrdpos : 0 < Formalism.FourierDecayAlt.S6.rd D.host.E := by rw [hrd]; exact EnergyConst.rdE_pos'
  have hgpos' : (0 : ℝ) < P.S.g := by exact_mod_cast hgpos
  have hκ : 0 < Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.kapG]; positivity
  have hδ : 0 < Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.deG]; positivity
  have hG : P.Gam0 ≠ 0 := by
    rw [Parts.Gam0, gam_eq]
    exact ne_of_gt (div_pos (Finset.prod_pos fun a _ => zpow_pos hκ _) (pow_pos hδ _))
  have key := level_constant_mul_gamma P.S.G.r P.S.G.k P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) hgpos' hrdpos
  rw [exp_eq _ _ hk1] at key
  rw [EnergyConst.Kexp, eq_div_iff hG]
  refine key.trans ?_
  rw [hrd, hg, hr, hk]
  rfl

end Formalism.L2.SG.Pf.Carrier.EnergyKM
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeRel
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section RelGen

theorem mulVec_single_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) :
    (M *ᵥ Pi.single j (1 : ℂ)) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem herm_smul_right' (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v w : Fin (2 * r + k + 1) → ℂ)
    (s : ℂ) : Formalism.QuantumDeterminants.herm H v (s • w) = star s * Formalism.QuantumDeterminants.herm H v w := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_fd_Q (hT : TrHyp F Qm Qim c) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    hJ ε (F.fd a) (Qm *ᵥ v) = c a * v (Formalism.QuantumDeterminants.eI k r a) := by
  have e1 : F.fd a = Qm *ᵥ (Qim *ᵥ F.fd a) := by rw [Matrix.mulVec_mulVec, hT.h2, Matrix.one_mulVec]
  rw [e1, ← herm_Q hT, Qi_f hT, herm_smul_right', star_star, Formalism.L2.SG.Pf.CarrierBase.herm_bvec,
    Formalism.L2.SG.Pf.CarrierBase.hpk_mulVec_esI]

theorem rootCoord_Q (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r) :
    rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a =
      κ * (if h : a.val + 1 < r then ρ (Formalism.QuantumDeterminants.eI k r a) (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩)
        else (ρ *ᵥ (Qim *ᵥ F.z)) (Formalism.QuantumDeterminants.eI k r a)) := by
  unfold rootCoord nxt
  by_cases h : a.val + 1 < r
  · rw [dite_eq_left h, dite_eq_left h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Qi_e hT, Matrix.mulVec_smul,
      Matrix.mulVec_smul, PtRepPf.hJ_smul_right, hJ_fd_Q hT, hc, hc]
    unfold Formalism.QuantumDeterminants.bvec
    rw [mulVec_single_apply]
    have he : r - a.val = (r - (a.val + 1)) + 1 := by omega
    simp only
    rw [he, pow_succ]
    field_simp
  · rw [dite_eq_right h, dite_eq_right h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hJ_fd_Q hT, hc]
    have he : r - a.val = 1 := by have := a.2; omega
    rw [he, pow_one]

theorem sum_rootCoord (hT : TrHyp F Qm Qim c) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val)) (hκ0 : κ ≠ 0)
    (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∑ a, rootCoord ε F.e F.fd F.z (Qm * ρ * Qim) a = κ * Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ := by
  simp only [rootCoord_Q hT hc hκ0, ← Finset.mul_sum]
  rfl

theorem psiR_Q (hT : TrHyp F Qm Qim c) (gg : ℕ) (hgg : 0 < gg) {κ : ℂ} (hc : ∀ a : Fin r, c a = κ ^ (r - a.val))
    (hκ : κ = -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ)) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psiR ε gg F.e F.fd F.z (Qm * ρ * Qim) = Formalism.QuantumDeterminants.psi k r (Qim *ᵥ F.z) Formalism.QuantumDeterminants.cStd ρ := by
  have hg : (0 : ℝ) < gg := by exact_mod_cast hgg
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    refine mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    have : (0 : ℝ) < (gg : ℝ) / (2 * Real.pi) := div_pos hg (by positivity)
    exact_mod_cast this.ne'
  unfold psiR Formalism.QuantumDeterminants.psi
  congr 1
  rw [Finset.sum_add_distrib, ← star_sum, sum_rootCoord hT hc hκ0]
  set ℓ := Formalism.QuantumDeterminants.ell k r (Qim *ᵥ F.z) ρ
  rw [show star (κ * ℓ) = (starRingEnd ℂ) (κ * ℓ) from rfl, Complex.add_conj]
  rw [hκ]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Formalism.QuantumDeterminants.cStd, Complex.div_re, Complex.div_im] <;>
    field_simp <;> ring

theorem psiR_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHf : ∀ a, H *ᵥ F.fd a = F.fd a) (hHz : H *ᵥ F.z = F.z)
    (gg : ℕ) : psiR ε gg F.e F.fd F.z (H * g * Hi) = psiR ε gg F.e F.fd F.z g := by
  have hHi : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hrc : ∀ a, rootCoord ε F.e F.fd F.z (H * g * Hi) a = rootCoord ε F.e F.fd F.z g a := by
    intro a
    unfold rootCoord
    have hn : H *ᵥ nxt F.e F.z a = nxt F.e F.z a := by
      unfold nxt; split_ifs; · exact hHe _
      · exact hHz
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hHi _ hn, fixed_left hH (hHf a)]
  unfold psiR
  simp only [hrc]

theorem spanLt_map {H : Matrix (Fin n) (Fin n) ℂ} (hHe : ∀ a, H *ᵥ F.e a = F.e a) (m : ℕ) {x : Fin n → ℂ}
    (hx : x ∈ spanLt F.e m) : H *ᵥ x ∈ spanLt F.e m := by
  have hle : spanLt F.e m ≤ (spanLt F.e m).comap (Matrix.mulVecLin H) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply, hHe]
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  exact hle hx

theorem span_range_le (hT : TrHyp F Qm Qim c) : Submodule.span ℂ (Set.range F.e) ≤ spanLt F.e r := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a, a.2, rfl⟩

theorem inN_Q (hT : TrHyp F Qm Qim c) {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hρ : ρ ∈ Formalism.QuantumDeterminants.Nset k r) : InN ε F.e F.z (Qm * ρ * Qim) := by
  have hsub : ∀ x, (Qm * ρ * Qim - 1) *ᵥ x = Qm *ᵥ ((ρ - 1) *ᵥ (Qim *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qm Qim, hT.h2, Matrix.one_mulVec]
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, Qi_e hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ ?_
    set v := (ρ - 1) *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) with hv
    have hva : ∀ i : Fin (2 * r + k + 1), a.val ≤ i.val → v i = 0 := by
      intro i hi
      rw [hv, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
      unfold Formalism.QuantumDeterminants.bvec
      rw [mulVec_single_apply, hρ.2.1 a i hi, sub_eq_zero]
      simp [Pi.single_apply]
    have hvX : IsXv v := fun i hi => hva i (by have := a.2; omega)
    rw [isXv_eq v hvX, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b.val < a.val
    · rw [Matrix.mulVec_smul, hT.he, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hva _ (by simp only [Formalism.QuantumDeterminants.eI]; omega), zero_smul, Matrix.mulVec_zero]
      exact Submodule.zero_mem _
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT F.z F.ez)))
  · rw [hsub]
    exact span_range_le hT (Q_X hT _ (N_sub_X hρ _ (Qi_noXs hT y hy)))

theorem inN_conj {H Hi g : Matrix (Fin n) (Fin n) ℂ} (hH : Hᴴ * Formalism.REAL.Jm ε * H = Formalism.REAL.Jm ε)
    (hHi : H * Hi = 1) (hiH : Hi * H = 1) (hHe : ∀ a, H *ᵥ F.e a = F.e a) (hHz : H *ᵥ F.z = F.z)
    (hg : InN ε F.e F.z g) : InN ε F.e F.z (H * g * Hi) := by
  have hHi' : ∀ x, H *ᵥ x = x → Hi *ᵥ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    rw [Matrix.mulVec_mulVec, hiH, Matrix.one_mulVec]
  have hsub : ∀ x, (H * g * Hi - 1) *ᵥ x = H *ᵥ ((g - 1) *ᵥ (Hi *ᵥ x)) := fun x => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ H Hi, hHi, Matrix.one_mulVec]
  obtain ⟨⟨h1, h2⟩, h3⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hsub, hHi' _ (hHe a)]; exact spanLt_map hHe _ (h1 a)
  · rw [hsub, hHi' _ hHz]; exact spanLt_map hHe _ h2
  · rw [hsub]
    refine spanLt_map hHe _ (h3 _ fun a => ?_)
    rw [← fixed_left hH (hHe a), Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec, hy a]

end RelGen

end Formalism.L2.SG.Pf.Bridge
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelMeasure
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.ModelMeasure

open Formalism.MainNotions.BigCellDensity

theorem mp_modelK {r k : ℕ} (pN : Formalism.MainNotions.S.Point ℂ (r + 1)) {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    {δ : Formalism.FourierDecayAlt.B.Mat k r} (hδ : δ ∈ Formalism.FourierDecayAlt.B.GV k r) {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx (wPt pN), ‖d (wPt pN q.1.1)‖ = ‖d (wPt pN q.1.2)‖)
    (hZ : Zhat k r Ds.z Ds.z' δ = Formalism.FourierDecayAlt.C2.monoP (wPt pN) d) (μ : Measure (Mt k r))
    (hconc : μ {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset δ} = 0) (c : ℝ≥0∞)
    (hmap : μ.map (fun x => Formalism.MainNotions.S.rootCoords k r Ds.z' pN (Matrix.of.symm (δ⁻¹ * Matrix.of x * δ))) = c • volume) :
    μ = c • Formalism.FourierDecayAlt.D.muR Ds δ (wPt pN) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt Ds.k_pos)
  exact Formalism.L2.SG.flagStabilizerModel.mp_model pN Ds hδ hd hdm hZ μ hconc c hmap

end Formalism.L2.SG.ModelMeasure

end
end
