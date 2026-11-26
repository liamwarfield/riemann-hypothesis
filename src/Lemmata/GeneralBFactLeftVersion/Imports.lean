module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

@[expose] public section

namespace Bl.general_b_fact_left_version

theorem goal1 :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module (Formalism.MainNotions.G.KK O) V] [inst_4 : _root_.Module O V]
      [inst_5 : IsScalarTower O (Formalism.MainNotions.G.KK O) V] (M : Submodule O V),
      Formalism.MainNotions.G.MQ (K := Formalism.MainNotions.G.KK O) M = ⊤ → ∀ (x : V), ∃ (a : O), a ≠ 0 ∧ a • x ∈ M := by
  intro O _ _ V _ _ _ _ M hM x
  have hx : x ∈ Submodule.span (Formalism.MainNotions.G.KK O) (M : Set V) := by
    have h : x ∈ (⊤ : Submodule (Formalism.MainNotions.G.KK O) V) := Submodule.mem_top
    rw [← hM] at h
    exact h
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
    have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨b * d, mul_ne_zero hb hd, ?_⟩
    have key : (d : O) • (IsLocalization.mk' (Formalism.MainNotions.G.KK O) n d • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, IsLocalization.mk'_spec', algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact M.smul_mem n hby

end Bl.general_b_fact_left_version
