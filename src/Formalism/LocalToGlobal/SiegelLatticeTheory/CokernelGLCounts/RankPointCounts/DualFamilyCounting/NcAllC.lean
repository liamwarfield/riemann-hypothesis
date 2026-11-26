module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSSplitPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWitt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataVolumesS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXMasses
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTHoldsX
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.RealBracketHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.IndexTypC
noncomputable section

namespace Formalism.L2.SG.Pf.NcIdx

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

def IndexTypC : Prop :=
  ∀ p : TypX X,
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
      (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
        aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)

end Formalism.L2.SG.Pf.NcIdx
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXConditions
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets Formalism.L2.SG.MassDataConc Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Clauses

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem inMass_bCF : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass :=
  inMass_bC X hb hK FdN FdN' u u' X0 _ T sd C Th _ (massH_pos X u).ne'

theorem inMasses_bCF (hX : HypX X hb FdN FdN' u u') :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses := by
  have h := inMassesAt_holds X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX
  exact h

theorem inLevelS_bCF (hX : HypX X hb FdN FdN' u u') :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS := by
  have h := level_s_at_instance X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ hX
  exact h

theorem inVolumes_bCF (hSW : PI.VolStabS.MassDataS.SWXS) (hX : HypX X hb FdN FdN' u u') (hψ : IsCharAF X.B.I.F ψ)
    (hstd : IsStdChar ψ) (hC : MeasCompatψ X ψ) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes := by
  have h := inVolumes_of_compat X hb hK FdN FdN' u u' X0 (locOf X u u' ψ) ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
    (volumes_s_at_instance hSW X hb hK FdN FdN' u u' X0 _ _) hX ⟨ψ, hψ, hstd, hC⟩ hdet
  exact h

theorem inTyped_bCF (hX : HypX X hb FdN FdN' u u') (hP : ProdConv X u u' ψ) (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u')
    (hTF : TypFacts X u u') (hψ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped :=
  inTypedC_loc X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (fun X v => SDL.sdLocX_holds X v) (fun X v _ => Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v) sTypIdx_holds
    hψ hstd hX hP hL hL' hTF

theorem pos_bCF (hSW : PI.VolStabS.MassDataS.SWXS) (hX : HypX X hb FdN FdN' u u') (hP : ProdConv X u u' ψ)
    (hψ : IsCharAF X.B.I.F ψ) (hC : MeasCompatψ X ψ) (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0)
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos := by
  exact Formalism.L2.SG.Pf.MassDataPos.massDataPosC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (locHaarPosC_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (covolPosC_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hψ hC hX.1 hdet)
    hQ
    (recPosC_of_dv X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (fun X v => dvPosC_holds X v) hX)
    hP (Formalism.L2.SG.Pf.MassDataPos.cooOf_pos X u u') (Formalism.L2.SG.WConst.kapN_pos (D := D)) hsd hC0 hTh

end Clauses

end Formalism.L2.SG.Pf.MassDataX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieIdx
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieIdx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_one_sub_inv_pow_pos (q : ℝ) (hq : 1 < q) (s : Finset ℕ) (hs : ∀ j ∈ s, 1 ≤ j) :
    0 < ∏ j ∈ s, (1 - 1 / q ^ j) :=
  Finset.prod_pos fun j hj => by
    have h1 : 1 < q ^ j := one_lt_pow₀ hq (by have := hs j hj; omega)
    have h2 : 1 / q ^ j < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith

theorem cardGL_A (g m : ℕ) [hg : Fact g.Prime] :
    (Nat.card (GL (Fin m) (ZMod g)) : ℝ) = (g : ℝ) ^ (m * m) * ∏ j ∈ Finset.Ioc 0 m, (1 - 1 / (g : ℝ) ^ j) := by
  have hq0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.out.ne_zero
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have hterm : ∀ i : Fin m, (((g ^ m - g ^ (i : ℕ) : ℕ)) : ℝ) = (g : ℝ) ^ m * (1 - 1 / (g : ℝ) ^ (m - i)) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hg.out.pos i.2.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one,
      mul_one_div, div_eq_mul_inv, ← pow_sub₀ _ hq0 (Nat.sub_le m i), Nat.sub_sub_self i.2.le]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 - 1 / (g : ℝ) ^ (m - i)) m]
  have h1 : ∏ i ∈ Finset.range m, (1 - 1 / (g : ℝ) ^ (m - i)) =
      ∏ i ∈ Finset.range m, (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) (m - 1 - i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    show _ = 1 - 1 / (g : ℝ) ^ (m - 1 - i + 1)
    rw [show m - 1 - i + 1 = m - i by omega]
  rw [h1, Finset.prod_range_reflect (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) m, Finset.range_eq_Ico,
    Finset.prod_Ico_add' (fun j => 1 - 1 / (g : ℝ) ^ j) 0 m 1]
  have h2 : Finset.Ico (0 + 1) (m + 1) = Finset.Ioc 0 m := by ext; simp; omega
  rw [h2]

theorem idx_arith (g r k : ℕ) (hg : g.Prime) :
    (glkC k g : ℝ) * (nnC r k g : ℝ) / (ggC r k g : ℝ) =
      (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) /
        ∏ i ∈ Finset.Icc (k + 1) (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ i) := by
  have : Fact g.Prime := ⟨hg⟩
  have hq : (1 : ℝ) < g := by exact_mod_cast hg.one_lt
  have hq0 : (g : ℝ) ≠ 0 := by linarith
  have hc : Fintype.card (Formalism.FourierDecayAlt.S3.Idx r k) = 2 * r + k + 1 := by
    simp only [Formalism.FourierDecayAlt.S3.Idx, Formalism.FourierDecayAlt.S3.Mid, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hG : (ggC r k g : ℝ) = (Nat.card (GL (Fin (2 * r + k + 1)) (ZMod g)) : ℝ) := by
    unfold ggC
    exact_mod_cast Nat.card_congr
      (Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod g) (ZMod g) (Fintype.equivFinOfCardEq hc)).toMulEquiv)
  have hN : (nnC r k g : ℝ) = (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    unfold nnC
    rw [MassDataIdxStIm.card_isN, ZMod.card]
    push_cast
    try rfl
  unfold glkC
  rw [hG, hN, cardGL_A, cardGL_A]
  have hIcc : Finset.Icc (k + 1) (2 * r + k + 1) = Finset.Ioc k (2 * r + k + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.prod_Ioc_consecutive _ (Nat.zero_le k) (by omega : k ≤ 2 * r + k + 1)]
  have hA : 0 < ∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => (Finset.mem_Ioc.1 hj).1)
  have hB : 0 < ∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => by have := (Finset.mem_Ioc.1 hj).1; omega)
  have hpow : (g : ℝ) ^ (k * k) * (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) /
      (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) = (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) := by
    rw [← pow_add, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hq0]
    congr 1
    rcases r with _ | s
    · simp; ring
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  rw [← hpow]
  generalize (∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j)) = A at hA ⊢
  generalize (∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j)) = B at hB ⊢
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hgn : (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  try ring

variable {D : D7} (X : HidaSetting D)

theorem ratio_eq (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal / (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ) := by
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := MassDataIdxSteps.measB_of X MassDataIdxSteps.haarIdx MassDataIdxSteps.redIdx u p
    (MassDataIdxSteps.stTop X p) (Formalism.L2.SG.Pf.MassDataX.stK_holds X p) (Formalism.L2.SG.Pf.MassDataX.stRed_holds X p)
    (Formalism.L2.SG.Pf.MassDataX.stImB_holds X hb u p)
  have h1 : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (j : ℝ) * (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal := by
    rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hpos : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
  rw [h1, ← hj]
  rcases eq_or_ne (j : ℝ) 0 with h0 | h0
  · simp [h0]
  · rw [mul_comm (j : ℝ) (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal, mul_comm (j : ℝ),
      div_mul_eq_div_div, div_self hpos, div_mul_eq_div_div, div_self hj0]

theorem gAt_eq (p : TypX X) : gAt X p.1 = gOf p := by
  unfold gAt gOf
  split_ifs <;> rfl

theorem aP_typed (u : D.what₂.Word) (p : TypX X) :
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) =
      ∏ i ∈ Finset.Icc (D.R.k + 1) (2 * D.R.rS + D.R.k + 1), (1 - 1 / (gOf p : ℝ) ^ i) := by
  obtain ⟨hN, hη⟩ := Formalism.L2.SG.Pf.gSplitX_holds X p
  have hT := Formalism.L2.SG.Pf.AlTieFD.T_not_mem X u p
  unfold aP
  rw [if_neg (by unfold Tw; exact hT), X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R, hη, hN, gAt_eq X p]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem indexTypC_holds (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro p
  refine (ratio_eq X hb u p).trans ?_
  rw [idx_arith (gOf p) D.R.rS D.R.k (MassDataIdxSteps.gOf_prime X p), aP_typed X u p, gAt_eq X p]

end Formalism.L2.SG.Pf.AlTieIdx
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcAllS
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcLeaves
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcGlob
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.HasProdFiniteSupport
noncomputable section

namespace Formalism.L2.SG.Pf.HasProdFiniteSupport

open Filter Topology

variable {ι : Type*}

theorem hasProd_inv₀' {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  refine (h.inv₀ ha).congr (fun s => ?_)
  exact (Finset.prod_inv_distrib f).symm

theorem hasProd_rpow' {f : ι → ℝ} {a : ℝ} (p : ℝ) (hf : ∀ i, 0 ≤ f i) (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => f i ^ p) (a ^ p) := by
  unfold HasProd at h ⊢
  refine (h.rpow_const (Or.inl ha)).congr (fun s => ?_)
  exact (Real.finsetProd_rpow s f (fun i _ => hf i) p).symm

theorem hasProd_of_finite_support {f : ι → ℝ} (s : Set ι) (hs : s.Finite) (h1 : ∀ i ∉ s, f i = 1) :
    HasProd f (∏ i ∈ hs.toFinset, f i) :=
  hasProd_prod_of_ne_finset_one (fun i hi => h1 i (by simpa using hi))

theorem hasProd_of_compl' (s : Finset ι) {f : ι → ℝ} {a : ℝ}
    (h : HasProd (fun i : {i // i ∉ s} => f i) a) : HasProd f (a * ∏ i : s, f i) := by
  classical
  have h1 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) a :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mp h
  have h2 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
    (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
  have h3 := h1.mul h2
  convert h3 using 1
  · funext i
    by_cases hp : i ∈ s <;> simp [Set.mulIndicator, hp]

theorem hasProd_compl_of' (s : Finset ι) {f : ι → ℝ} {a : ℝ} (h : HasProd f a) (hf : ∀ i ∈ s, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ s} => f i) (a * (∏ i : s, f i)⁻¹) := by
  classical
  have h2 : HasProd (fun i => ((↑s : Set ι).mulIndicator f i)⁻¹) (∏ i : s, f i)⁻¹ := by
    have h0 : HasProd ((↑s : Set ι).mulIndicator f) (∏ i : s, f i) :=
      (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι))).mp (hasProd_fintype _)
    exact hasProd_inv₀' h0 (Finset.prod_ne_zero_iff.mpr fun i _ => hf i i.2)
  have h3 := h.mul h2
  have h4 : HasProd ((↑s : Set ι)ᶜ.mulIndicator f) (a * (∏ i : s, f i)⁻¹) := by
    convert h3 using 1
    funext i
    by_cases hp : i ∈ s
    · simp [Set.mulIndicator, hp, hf i hp]
    · simp [Set.mulIndicator, hp]
  exact (hasProd_subtype_iff_mulIndicator (s := (↑s : Set ι)ᶜ)).mpr h4

end Formalism.L2.SG.Pf.HasProdFiniteSupport
end
end

noncomputable section

open Classical

namespace Formalism.L2.SG.Pf.NcGlob

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField
  Formalism.L2.SG.Pf.HasProdFiniteSupport Formalism.L2.SG.Pf.NcVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (X : HidaSetting D)

def fac (i : ℕ) (v : PlX X) : ℝ :=
  1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i

def tf (k t : ℕ) (v : PlX X) : ℝ :=
  if ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then fac X k v else 1

theorem absNorm_gt_one (v : PlX X) : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.2 v.isPrime.ne_top
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast this

theorem fac_pos (i : ℕ) (hi : 1 ≤ i) (v : PlX X) : 0 < fac X i v := by
  unfold fac
  have hq := absNorm_gt_one X v
  have hq0 : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have habs : |((etaV (E := X.B.I.E) v : ℤ) : ℝ)| = 1 := by
    unfold etaV; split_ifs <;> simp
  have hη : ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i ≤ 1 := by
    calc ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i ≤ |((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i| := le_abs_self _
      _ = 1 := by rw [abs_pow, habs, one_pow]
  have hqi : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i := one_lt_pow₀ hq (by omega)
  have : ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i < 1 :=
    (div_lt_one (by positivity)).mpr (lt_of_le_of_lt hη hqi)
  linarith

theorem tf_pos (k t : ℕ) (hk : 1 ≤ k) (v : PlX X) : 0 < tf X k t v := by
  unfold tf; split_ifs
  · exact fac_pos X k hk v
  · exact one_pos

theorem aP_split (k N t : ℕ) (hk : k + 1 ≤ N) (v : PlX X) :
    aP (E := X.B.I.E) v k N t = (∏ i ∈ Finset.Icc (k + 1) N, fac X i v) * tf X k t v := by
  unfold aP tf
  by_cases ht : ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
  · rw [if_pos ht, if_pos ht, Finset.Icc_eq_cons_Ioc (show k ≤ N by omega), Finset.prod_cons]
    have hIo : Finset.Ioc k N = Finset.Icc (k + 1) N := by
      ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIo, mul_comm]
    rfl
  · rw [if_neg ht, if_neg ht, mul_one]
    rfl

theorem aPlus_pos (k N t : ℕ) (hk : 1 ≤ k) (v : PlX X) : 0 < aP (E := X.B.I.E) v k N t := by
  unfold aP
  apply Finset.prod_pos
  intro i hi
  have : 1 ≤ i := by
    simp only [Finset.mem_Icc] at hi
    split_ifs at hi <;> omega
  exact fac_pos X i this v

theorem finite_dvd (t : ℕ) (ht : t ≠ 0) :
    {v : PlX X | ((t : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {((t : ℕ) : 𝓞 X.B.I.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast ht
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv

theorem absV_nonneg (v : PlX X) : 0 ≤ absV v (dV v) := by
  unfold absV; split_ifs
  · exact le_rfl
  · positivity

end Loc


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem normalizing_arithmetic_holds : NcArith := by
  intro D X hb hK FdN FdN' u u' X0 ψ τ Rw I H H₁ i1 i2 i3 i4 i5 T sd C Th F0 what₂ vR Q M δ i0 i0' νq a'
    ha hRR hS hR hχ hstd hcong hVo hVt hIx hOm hDP hRMp hFD hPC hP
  obtain ⟨hd, hfc, hEul, hTfac, hvI, hfE, hn, htδ, htaP, hgprod⟩ := hFD
  obtain ⟨hKc, hFc, -⟩ := Formalism.L2.SG.Pf.Cnt.field_dictionary_holds D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm : D.R.m = 2 * (D.R.rS + 1) := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    show D.R.k + D.R.m - 1 = D.R.k + 2 * D.R.rS + 1
    omega

  have hLpos : ∀ i, 2 ≤ i → 0 < Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i := by
    intro i hi
    rw [← Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF hKc hFc i hi]
    exact Formalism.HermitianLattices.Ext.L3.lValEta_pos hKc i hi
  set PiL : ℝ := ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i with hPiL
  have hPiLpos : 0 < PiL := by
    apply Finset.prod_pos
    intro i hi
    exact hLpos i (by simp only [Finset.mem_Icc] at hi; omega)
  have hfacHP : HasProd (fun v : PlX X => ∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, fac X i v) PiL⁻¹ := by
    rw [hPiL, ← Finset.prod_inv_distrib]
    apply hasProd_prod
    intro i hi
    have hi2 : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    have h1 := hasProd_inv₀' (hEul i hi2) (hLpos i hi2).ne'
    convert h1 using 1
    funext v
    simp [fac]

  set PT : ℝ := ∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)
    with hPT
  have hTHP : HasProd (tf X D.R.k (Tw u)) PT := by
    convert hTfac using 1
    funext v
    by_cases hv : (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal <;>
      simp [tf, fac, Tw, hv]
  have hT0 : (Tw u) ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hT0' : (Tw u') ≠ 0 := (D.mem u').A.T_prime.ne_zero
  have hSf := finite_dvd X (Tw u) hT0
  have hSf' := finite_dvd X (Tw u') hT0'
  have hTHPf : HasProd (tf X D.R.k (Tw u)) (∏ v ∈ hSf.toFinset, tf X D.R.k (Tw u) v) :=
    hasProd_of_finite_support _ hSf (fun v hv => by simp only [tf, Set.mem_ofPred_eq] at hv ⊢; rw [if_neg hv])
  have hTHP' : HasProd (tf X D.R.k (Tw u')) (∏ v ∈ hSf'.toFinset, tf X D.R.k (Tw u') v) :=
    hasProd_of_finite_support _ hSf' (fun v hv => by simp only [tf, Set.mem_ofPred_eq] at hv ⊢; rw [if_neg hv])
  have hPTpos : 0 < PT := by
    rw [hTHP.unique hTHPf]
    exact Finset.prod_pos fun v _ => tf_pos X D.R.k (Tw u) (by omega) v
  set PT' : ℝ := ∏ v ∈ hSf'.toFinset, tf X D.R.k (Tw u') v with hPT'
  have hPT'pos : 0 < PT' := Finset.prod_pos fun v _ => tf_pos X D.R.k (Tw u') (by omega) v

  have hn' : X.B.I.n = D.R.r := hn
  have hsplit : ∀ t v, aP (E := X.B.I.E) v D.R.k X.B.I.n t =
      (∏ i ∈ Finset.Icc (D.R.k + 1) D.R.r, fac X i v) * tf X D.R.k t v := by
    intro t v
    rw [aP_split X D.R.k X.B.I.n t (by omega) v, hn']
  set AT : ℝ := PiL⁻¹ * PT with hAT
  set A' : ℝ := PiL⁻¹ * PT' with hA'
  have hATHP : HasProd (fun v : PlX X => aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u)) AT := by
    have := hfacHP.mul hTHP
    convert this using 1
    funext v
    exact hsplit _ v
  have hA'HP : HasProd (fun v : PlX X => aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u')) A' := by
    have := hfacHP.mul hTHP'
    convert this using 1
    funext v
    exact hsplit _ v
  have hATpos : 0 < AT := mul_pos (inv_pos.mpr hPiLpos) hPTpos
  have hA'pos : 0 < A' := mul_pos (inv_pos.mpr hPiLpos) hPT'pos
  set ATyp : ℝ := ∏ p : TypX X, aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) with hATyp
  have hATyppos : 0 < ATyp := Finset.prod_pos fun p _ => aPlus_pos X D.R.k X.B.I.n (Tw u) (by omega) p.1

  have hG5 : AT * PiL = PT := by rw [hAT]; field_simp

  have hal_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al =
      (∏ p : TypX X, alX X u u' p.1) * ∏' v : OrdX X, alX X u u' v.1 := rfl
  have halT : ∀ v : PlX X, TypAt X v → alX X u u' v = aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) := by
    intro v hv; unfold alX; rw [if_pos hv]
  have halO : ∀ v : PlX X, ¬ TypAt X v → alX X u u' v =
      aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u) * aP (E := X.B.I.E) v D.R.k X.B.I.n (Tw u') := by
    intro v hv; unfold alX; rw [if_neg hv]
  have hordHP := hasProd_compl_of' (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) (hATHP.mul hA'HP)
    (fun v _ => (mul_pos (aPlus_pos X D.R.k X.B.I.n (Tw u) (by omega) v)
      (aPlus_pos X D.R.k X.B.I.n (Tw u') (by omega) v)).ne')
  have hord : ∏' v : OrdX X, alX X u u' v.1 = AT * A' *
      (∏ i : TypX X, (aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u) *
        aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u')))⁻¹ := by
    rw [← hordHP.tprod_eq]
    exact tprod_congr (fun v => halO v.1 v.2)
  have hTypProd : (∏ i : TypX X, (aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u) *
        aP (E := X.B.I.E) i.1 D.R.k X.B.I.n (Tw u'))) = ATyp * ATyp := by
    rw [Finset.prod_mul_distrib, Fintype.prod_congr _ _ (fun p : TypX X => htaP p), hATyp]
  have hG4 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).al * ATyp = AT * A' := by
    rw [hal_def, Fintype.prod_congr _ _ (fun p : TypX X => halT p.1 p.2), ← hATyp, hord, hTypProd]
    field_simp

  have hdX : 0 < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hδHP := hasProd_rpow' ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)
    (fun v => absV_nonneg X v) hDP (inv_ne_zero hdX.ne')
  have hωHP := hδHP.mul hA'HP
  have hG3 : (∏' v : PlX X,
        (omAt X.B.I.cm.sig X.B.I.J ψ v
          ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
          {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
            Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal) =
      |(NumberField.discr D.host.F : ℝ)| ^
        (-((D.R.r : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2)) * A' := by
    have hωHP' : HasProd (fun v : PlX X =>
        (omAt X.B.I.cm.sig X.B.I.J ψ v
          ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
          {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
            Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
        ((|(NumberField.discr X.B.I.F : ℝ)|⁻¹) ^
          ((X.B.I.n : ℝ) * (2 * D.R.rS + 1) - ((2 * (D.R.rS : ℝ) + 1) ^ 2) / 2) * A') := by
      convert hωHP using 1
      funext v
      exact hOm hχ hstd v
    rw [hωHP'.tprod_eq, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), hd, hn']

  have hU_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume =
      (∏' v : OrdX X, localVolumeUnit X ψ v.1) * ∏ p : TypX X, localVolumeUnit X ψ p.1 := rfl
  have hZ_def : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      ∏' v : PlX X, ZZX X u u' ψ v := rfl
  obtain ⟨-, -, -, hU00m, -, hZZm, hZZpos, -⟩ := hPC
  have hUHP : HasProd (fun v => localVolumeUnit X ψ v)
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume := by
    rw [hU_def]
    exact hasProd_of_compl' (typSet X.B.I.F (D.host.g 0) (D.host.g 1)) hU00m.hasProd
  have hZHP : HasProd (fun v => ZZX X u u' ψ v)
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ := by
    rw [hZ_def]
    exact hZZm.hasProd
  have hratHP := hUHP.mul (hasProd_inv₀' hZHP (by rw [hZ_def]; exact hZZpos.ne'))
  have hpp : ∀ v : PlX X, localVolumeUnit X ψ v * (ZZX X u u' ψ v)⁻¹ =
      absV v (dV v) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) *
        (if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1) := by
    intro v
    by_cases hv : TypAt X v
    · rw [if_pos hv, ← div_eq_mul_inv, hVt hχ hstd hcong v hv, htδ ⟨v, hv⟩, Real.one_rpow, one_mul]
    · rw [if_neg hv, ← div_eq_mul_inv, hVo hχ hstd v hv, mul_one]
  have hgHP : HasProd (fun v : PlX X => if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1)
      (∏ p : TypX X, (gAt X p.1 : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))) := by
    have h0 := hasProd_of_compl' (typSet X.B.I.F (D.host.g 0) (D.host.g 1))
      (f := fun v : PlX X => if TypAt X v then (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) else 1) (a := 1)
      (by
        convert (hasProd_one : HasProd (fun _ : {i // i ∉ typSet X.B.I.F (D.host.g 0) (D.host.g 1)} => (1 : ℝ)) 1)
          using 1
        funext v
        exact if_neg v.2)
    convert h0 using 1
    rw [one_mul]
    exact Fintype.prod_congr _ _ (fun p => (if_pos p.2).symm)
  have hδX := hasProd_rpow' (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3))
    (fun v => absV_nonneg X v) hDP (inv_ne_zero hdX.ne')
  have hval : HasProd (fun v : PlX X => localVolumeUnit X ψ v * (ZZX X u u' ψ v)⁻¹)
      ((|(NumberField.discr X.B.I.F : ℝ)|⁻¹) ^ (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) *
        ∏ p : TypX X, (gAt X p.1 : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3))) := by
    convert hδX.mul hgHP using 1
    funext v
    exact hpp v
  have hG1 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).unitLevelVolume /
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volZZ =
      |(NumberField.discr D.host.F : ℝ)| ^ (((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3) *
        ((Lat.gS D : ℕ) : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3) * Module.finrank ℚ D.host.F) := by
    rw [div_eq_mul_inv, hratHP.unique hval, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _), neg_neg,
      hd, Finset.prod_pow, hgprod, ← pow_mul, mul_comm (Module.finrank ℚ D.host.F)]

  have hKo := hP.2.1
  have hKp : ∀ p, 0 < (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p :=
    fun p => (hP.1 p).2.2.2.2.2.1
  have hG2 : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnat /
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      ((Lat.gS D : ℕ) : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) * Module.finrank ℚ D.host.F : ℕ) : ℤ)) /
        ATyp := by
    unfold Formalism.FourierDecayAlt.S3.MassData.μKnat Formalism.FourierDecayAlt.S3.MassData.μK
    rw [mul_div_mul_left _ _ hKo.ne', ← Finset.prod_div_distrib, Fintype.prod_congr _ _ hIx,
      Finset.prod_div_distrib, Finset.prod_zpow, hgprod, ← hATyp]
    congr 1
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring

  have hfinE : Module.finrank ℚ D.host.E = 2 * Module.finrank ℚ D.host.F := by
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    ring
  have hng : ngFac D = ((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F * (D.R.k - 1)) := by
    unfold ngFac
    have hcast : (((Lat.gS D : ℕ) : D.host.E)) ^ D.R.m =
        algebraMap ℚ D.host.E (((Lat.gS D : ℕ) : ℚ) ^ D.R.m) := by simp
    rw [hcast, Algebra.norm_algebraMap, hfinE]
    have hg0 : (0 : ℝ) ≤ ((Lat.gS D : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq : |((((((Lat.gS D : ℕ) : ℚ) ^ D.R.m) ^ (2 * Module.finrank ℚ D.host.F) : ℚ)) : ℝ)| =
        (((Lat.gS D : ℕ) : ℝ) ^ (D.R.m * Module.finrank ℚ D.host.F)) ^ 2 := by
      push_cast
      rw [abs_of_nonneg (by positivity), ← pow_mul, ← pow_mul]
      ring_nf
    rw [hsq, Real.sqrt_sq (by positivity), ← pow_mul]

  rw [hd, hfc] at hR
  exact Formalism.L2.SG.Pf.NcArithG.ncValueC_of_global X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    a' _ ATyp A' AT PT hP ha hATyppos hA'pos hPTpos hS hR hG1 hG2 hG3 hG4 hG5
    (hRMp D u u' hcong F0 what₂ hRR) hvI hfE hng

end Formalism.L2.SG.Pf.NcGlob
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcLeaves

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieC_of_leaves (a' : ℝ) (ha : 0 < a')
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hχ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  Formalism.L2.SG.Pf.NcAsm.ncTieC_of' X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (Formalism.L2.SG.Pf.NcGlob.normalizing_arithmetic_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha hRR hS hR
      hχ hstd hcong hVo hVt hIx hOm
      (Formalism.L2.SG.Pf.NcVal.diffProd_holds X) PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass hFD hPC hP)

end Formalism.L2.SG.Pf.NcLeaves
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcAllS

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieAllS_of (hSplit : Formalism.L2.SG.Pf.NcSplitS.SplitOm) (hRB : Formalism.L2.SG.Pf.NcReal.RealBracket)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hSW1 : Formalism.MainNotions.UnusedSlot34.SWa1 X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hSW2 : Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J)
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hTy : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) := by
  obtain ⟨⟨hT1, νH, hOmT, hCT⟩, -⟩ := hMC.1 u'
  have hn : X.B.I.n = D.R.r := hFD.2.2.2.2.2.2.1
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hn2 : 2 * (D.R.rS + 1 + D.R.rS) < X.B.I.n := by rw [hn]; omega

  have hp := hP.1
  have hKo := hP.2.1
  have hprod : 0 < ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal :=
    Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have hKf : 0 < (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal := by
    have h := hKo
    change 0 < (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal / _ at h
    exact (div_pos_iff_of_pos_right hprod).1 h
  obtain ⟨hK0, hKtop⟩ := ENNReal.toReal_pos_iff.1 hKf
  obtain ⟨a', ha, hinf, hfin⟩ := hSplit X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ D.R.rS (frameOf X u')
    X.measG (X.measW u') hT1 νH (X.B.I.L : Set _) hStd hLat hdet hn2 hSW1 hSW2 X.measG_norm (X.measW_norm u')
    hOmT hCT (by exact hK0) (by exact hKtop)
  have hR0 := hRB X hb FdN FdN' u u' ψ hHyp hMC hStd.2.2.2 hT1 a' ha hinf
  have e1 : Formalism.L2.SG.Pf.NcReal.eDF D.R.k D.R.rS =
      -(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3 := by
    unfold Formalism.L2.SG.Pf.NcReal.eDF; ring
  rw [e1] at hR0
  have hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3) := hR0
  have hμK : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK =
      (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal := by
    show (X.measG.μGf (Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _))).toReal /
        (∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal) *
        ∏ p : TypX X, (X.measG.μGv p.1 (Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set _) p.1)).toReal = _
    rw [div_mul_cancel₀ _ hprod.ne']
  have hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal := by
    rw [hμK]
    exact hfin
  exact Formalism.L2.SG.Pf.NcLeaves.ncTieC_of_leaves X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha
    hP hM hMs hL hO hTy hV hVG hStd.2.2.1 hStd.2.2.2 hcong hRR hS hR hVo hVt hIx hOm hFD hPC

set_option maxHeartbeats 4000000 in
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTie0All_of (hRB : Formalism.L2.SG.Pf.NcReal.RealBracket) (hSW : PI.VolStabS.MassDataS.SWXS)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet' : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) (hPC : ProdConv X u u' ψ)
    (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u') (hTF : TypFacts X u u')
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  ncTieAllS_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (Formalism.L2.SG.Pf.NcS.SplitPf.splitOm_of_intWitt Formalism.L2.SG.Pf.NcS.IntWittPf.integral_witt_almost_everywhere) hRB hHyp hMC hStd hLat
    hdet' (hSW X).1 (hSW X).2
    (Formalism.L2.SG.Pf.MassDataX.pos_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hHyp hPC hStd.2.2.1 hMC
      hdet hQ hsd hC0 hTh)
    (Formalism.L2.SG.Pf.MassDataX.inMass_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (Formalism.L2.SG.Pf.MassDataX.inMasses_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp)
    (Formalism.L2.SG.Pf.MassDataX.inLevelS_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp)
    (Formalism.L2.SG.MassDataConc.inOrdinary_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hPC)
    (Formalism.L2.SG.Pf.MassDataX.inTyped_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hHyp hPC hL hL' hTF
      hStd.2.2.1 hStd.2.2.2)
    (Formalism.L2.SG.Pf.MassDataX.inVolumes_bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hHyp hStd.2.2.1
      hStd.2.2.2 hMC hdet)
    (Formalism.L2.SG.Pf.MassDataX.volHa'_eq X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hSW hStd.2.2.1 hMC)
    hcong hRR (Formalism.L2.SG.Pf.NcVal.volOrdV_holds X u u' ψ) (Formalism.L2.SG.Pf.NcVal.volTypV_holds X u u' ψ)
    (Formalism.L2.SG.Pf.AlTieIdx.indexTypC_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (Formalism.L2.SG.Pf.NcVal.OmVSt.OmVZ.omV_holdsX X u' ψ) (Formalism.L2.SG.Pf.AlTieLG.fieldDict_holds X u u') hPC

end Formalism.L2.SG.Pf.NcAllS
end
end

noncomputable section

namespace Formalism.L2.SG.Pf.NcAllC

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

set_option maxHeartbeats 4000000 in
variable [Fact PI.AprimeInfW.GaugeVolUD] [Fact Formalism.L2.SG.Pf.WB.RhsWLim] [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieC_of_closed (hCov : Formalism.L2.SG.Pf.NcReal.JX.CovolRef) (hSW : PI.VolStabS.MassDataS.SWXS)
    (hHyp : HypX X hb FdN FdN' u u') (hMC : MeasCompatψ X ψ) (hStd : StdHyp X.B.I.cm.sig X.B.I.J ψ)
    (hLat : ∃ L : Submodule (NumberField.RingOfIntegers X.B.I.E) (Fin X.B.I.n → X.B.I.E),
      Submodule.IsFullLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))
    (hdet' : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det ≠ 0)
    (hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0) (hPC : ProdConv X u u' ψ)
    (hL : LocTieX X ψ u) (hL' : LocTieX X ψ u') (hTF : TypFacts X u u')
    (hQ : Formalism.L2.SG.Pf.MassDataPos.QuotVolPosC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hsd : 0 ≤ sd) (hC0 : 0 ≤ C) (hTh : 0 < Th)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  Formalism.L2.SG.Pf.NcAllS.ncTie0All_of X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq
    (Formalism.L2.SG.Closed.RealBracket_holds hCov) hSW hHyp hMC hStd hLat hdet' hdet hPC hL hL' hTF hQ hsd hC0 hTh hcong hRR

end Formalism.L2.SG.Pf.NcAllC
