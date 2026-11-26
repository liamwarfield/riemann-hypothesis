module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAddCharConjEqProdPlaceResidueChars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeArgumentResidueEqWeightedSymmetricFrameSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EwZero

variable {D : D7}


open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in
theorem Wq_le_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Wq X.B.I (wB X w) ≤ GlobalTheory.Mem.SymChar.wInt X w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, by simp⟩, rfl⟩


open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in
theorem Lq_le_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Lq X.B.I (wB X w) ≤ wLf X w := by
  show Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat0 X.B.I (wB X w)) ≤ Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat X w)
  rw [wLat_eq]

theorem ew_mem_wInt (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hw : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  obtain ⟨ob, h1, -⟩ := Formalism.L2.SG.Pf.KppFwdPf.ew_res X kv
  cases ob with
  | false =>
    simp only [Bool.false_eq_true, if_false, sub_zero] at h1
    exact Wq_le_wInt X _ h1
  | true =>
    simp only [if_true] at h1
    exfalso
    apply hw
    intro y hy
    have h2 : 1 - X.ew ∈ Formalism.L2.SG.Pf.KppRedW.Wq X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2)) := by
      have := neg_mem h1
      rwa [neg_sub] at this
    exact Lq_le_wLf X _ (Formalism.L2.SG.Pf.KppRedW.Wq_smul h2 hy)

end GlobalTheory.Mem.SymChar.EwZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMemPlaceIdealSpanOfNeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  first | exact @GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt | exact GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt | (intros; apply GlobalTheory.Mem.SymChar.EwZero.ew_mem_wInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EdgeReindex

theorem sum_edge {Q : Type} [AddCommMonoid Q] {r t : ℕ} (ht : t < r) (P : Fin r → Prop) [DecidablePred P]
    (hP : ∀ j, P j ↔ j.val = t) (f : Fin r → Q) : (∑ j, if P j then f j else 0) = f ⟨t, ht⟩ := by
  rw [Finset.sum_eq_single ⟨t, ht⟩]
  · rw [if_pos ((hP _).2 rfl)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext ((hP b).1 h))
  · simp

def extF {Q : Type} [AddCommGroup Q] {r : ℕ} (F : Fin r → Fin r → Q) (a b : ℕ) : Q :=
  if h : a < r ∧ b < r then F ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

def termAt {Q : Type} [AddCommGroup Q] (ρ k : ℕ) (s : Bool) {r : ℕ} (F : Fin r → Fin r → Q) (n : ℕ) : Q :=
  if n < ρ then extF F n (if n + 1 < ρ then n + 1 else ρ + k)
  else if n + 1 < ρ + k then (if s then extF F n (n + 1) else 0) else 0

theorem inner_eq {Q : Type} [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool)
    (F : Fin r → Fin r → Q) (i : Fin r) :
    (∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) =
      termAt ρ k s F i.1 := by
  have hi := i.2
  unfold termAt
  by_cases h1 : i.1 < ρ
  · by_cases h2 : i.1 + 1 < ρ
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_pos h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
    · rw [sum_edge (t := ρ + k) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_pos h1, if_neg h2, extF, dite_eq_left ⟨i.2, by omega⟩]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_pos h1, one_smul]
  · by_cases h2 : i.1 + 1 < ρ + k
    · rw [sum_edge (t := i.1 + 1) (by omega) _ (fun j => by
        simp only [symEdge]; constructor <;> intro h <;> omega)]
      rw [if_neg h1, if_pos h2]
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_pos h2]
      cases s
      · simp
      · rw [extF, dite_eq_left ⟨i.2, by omega⟩]
        simp
    · rw [if_neg h1, if_neg h2]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [GlobalTheory.Mem.SymChar.wtA, if_neg h1, if_neg h2, zero_smul, ite_self]

theorem sum_symEdge_wtA : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  intro Q _ ρ k r hr s F
  rw [Finset.sum_congr rfl (fun i _ => inner_eq ρ k r hr s F i)]
  rw [Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) r]
  have e : Finset.range r = Finset.range (ρ + (k + (ρ + 1))) := congrArg Finset.range (by omega)
  rw [e, Finset.sum_range_add, Finset.sum_range_add]
  have h3 : (∑ x ∈ Finset.range (ρ + 1), termAt ρ k s F (ρ + (k + x))) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    unfold termAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [h3, add_zero]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F n) ρ]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha := a.2
    unfold termAt extF
    rw [if_pos ha, dite_eq_left ⟨by omega, by split_ifs <;> omega⟩]
  · rw [← Fin.sum_univ_eq_sum_range (fun n => termAt ρ k s F (ρ + n)) k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi := i.2
    by_cases h : i.1 + 1 < k
    · rw [dite_eq_left h]
      unfold termAt
      rw [if_neg (by omega), if_pos (by omega)]
      cases s
      · rfl
      · simp only [if_true]
        unfold extF
        rw [dite_eq_left ⟨by omega, by omega⟩]
    · rw [dite_eq_right h]
      unfold termAt
      rw [if_neg (by omega), if_neg (by omega)]

end GlobalTheory.Mem.SymChar.EdgeReindex
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFrameWeightedEdgeSumReindexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex : ∀ (Q : Type) [AddCommGroup Q] (ρ k r : ℕ) (hr : r = k + 2 * ρ + 1) (s : Bool) (F : Fin r → Fin r → Q), (∑ i : Fin r, ∑ j : Fin r, if symEdge ρ k i j then GlobalTheory.Mem.SymChar.wtA ρ k s i j • F i j else 0) = (∑ a : Fin ρ, F ⟨a.1, by have := a.2; omega⟩ ⟨if a.1 + 1 < ρ then a.1 + 1 else ρ + k, by have := a.2; split_ifs <;> omega⟩) + ∑ i : Fin k, if h : i.1 + 1 < k then (if s then F ⟨ρ + i.1, by omega⟩ ⟨ρ + i.1 + 1, by omega⟩ else 0) else 0 := by
  first | exact @GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | exact GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA | (intros; apply GlobalTheory.Mem.SymChar.EdgeReindex.sum_symEdge_wtA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeArgumentResidueEqWeightedSymmetricFrameSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar


open GlobalTheory.Mem.SymChar.Resid in
theorem resid_at_w : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k N → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymChar.argS X k) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) := by
  intro D X _h _hE hgw kv k hk N hN
  classical
  have hg : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := hgw kv
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  set w := D.naut.plGw kv.1 kv.2 with hwdef
  let S : AddSubgroup (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := (wInt X w).toAddSubgroup
  let mk := QuotientAddGroup.mk' S
  have hmk : ∀ a b, a - b ∈ wInt X w → mk a = mk b := fun a b hab =>
    (QuotientAddGroup.eq_iff_sub_mem).2 hab
  let f0 : ℤ →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    mk.comp (Int.castAddHom (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
  have hf0 : f0 (D.host.g kv.1 : ℤ) = 0 := by
    show mk ((((D.host.g kv.1 : ℕ) : ℤ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) = 0
    rw [Int.cast_natCast]
    exact (QuotientAddGroup.eq_zero_iff _).2 (natCast_g_mem X kv.1 hg)
  let φ : ZMod (D.host.g kv.1) →+ (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ S :=
    ZMod.lift (D.host.g kv.1) ⟨f0, hf0⟩
  have hφ : ∀ t : ZMod (D.host.g kv.1), φ t = mk ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    intro t
    conv_lhs => rw [← ZMod.natCast_zmod_val t, ← Int.cast_natCast]
    rw [ZMod.lift_coe]
    show mk _ = mk _
    congr 1
    simp
  suffices hs : mk (argS X k) = φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) by
    unfold ModW
    rw [hφ] at hs
    exact (QuotientAddGroup.eq_iff_sub_mem).1 hs
  have hsum : φ (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then
      ((wtA D.R.rS D.R.k (side X w) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) =
      ∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then wtA D.R.rS D.R.k (side X w) i j • φ (N i j) else 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rw [← zsmul_eq_mul, map_zsmul]
    · exact map_zero φ
  rw [hsum, GlobalTheory.T.symmetricFrame_weightedEdgeSum_reindex _ D.R.rS D.R.k D.R.r (rank_eq D) (side X w) (fun i j => φ (N i j))]
  unfold argS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [hφ]
    apply hmk
    have := dual_row X w hN (X.vectorsInLattice.1 a).2 (posE D a) (GlobalTheory.T.flagDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg a) (posN D a)
    rw [symVec_posN] at this
    exact this
  · refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hw : SymFrame.EwAt X w
      · have hs : side X w = true := by simp [side, hw]
        rw [if_pos hs, hφ]
        apply hmk
        have h1 := one_sub_ew_mem X kv.1 hg hw
        have := dual_row X w hN (X.vectorsInLattice.2.2 i).2 (posB D i) (GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place D X w kv.1 hg hw h1 i)
          (posB D ⟨i.1 + 1, hi⟩)
        rw [symVec_posB X w hw] at this
        have e1 : (posB D ⟨i.1 + 1, hi⟩) = ⟨D.R.rS + i.1 + 1, by have := rank_eq D; omega⟩ :=
          Fin.ext (by simp only [posB]; omega)
        rw [e1] at this
        exact this
      · have hs : side X w = false := by simp [side, hw]
        rw [if_neg (by simp [hs])]
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
        have hew := GlobalTheory.T.idempotent_mem_placeIdealSpan_of_ne_one D X kv hw
        have hbw : X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩ ∈ X.B.I.Lf :=
          Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1
        have hint := Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.2.2 i).2 hbw
        have e : hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) =
            hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) * X.ew := by
          conv_lhs => rw [X.bwd_w i]
          rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_left, Formalism.L2.SG.Pf.unitaryCongruence.sigA_sigA, mul_comm]
        show hA X.B.I (X.bwd i) (X.B.I.fmat k *ᵥ X.bw ⟨i.1 + 1, hi⟩) ∈ wInt X w
        rw [e]
        exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hew
    · rw [dite_eq_right hi, dite_eq_right hi, map_zero]

end GlobalTheory.Mem.SymChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeArgumentResidueEqWeightedSymmetricFrameSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeArgument_residue_eq_weighted_symmetricFrameSum : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k N → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymChar.argS X k) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * N i j else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.resid_at_w | exact GlobalTheory.Mem.SymChar.resid_at_w | (intros; apply GlobalTheory.Mem.SymChar.resid_at_w <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInv
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem invMat_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] [Fact (1 < g)]
    (T S : Q →+ Q) (hST : ∀ q, S (T q) = q) (β : ι → Q) (hβ : ∀ i, g • β i = 0)
    (N N' : Matrix ι ι (ZMod g)) (hNN' : N * N' = 1)
    (hT : ∀ i, T (β i) = ∑ j, (N j i).val • β j) (m : ι) :
    S (β m) = ∑ i, (N' i m).val • β i := by
  have e1 : T (∑ i, (N' i m).val • β i) = ∑ l, ((N * N') l m).val • β l := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_nsmul, hT, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have e2 : ∑ l, (((1 : Matrix ι ι (ZMod g))) l m).val • β l = β m := by
    rw [Finset.sum_eq_single m]
    · rw [Matrix.one_apply_eq, ZMod.val_one, one_smul]
    · intro l _ hl
      rw [Matrix.one_apply_ne hl, ZMod.val_zero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hNN', e2] at e1
  rw [← e1, hST]

end GlobalTheory.Mem.SymFrame

namespace GlobalTheory.Mem.SymFrame

theorem isMatIn_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  intro D X kv hg u hu k hk N hN m
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  haveI : Fact (1 < D.host.g kv.1) := ⟨(D.host.g_prime kv.1).one_lt⟩
  let W := (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
  have hk' : k⁻¹ ∈ X.B.I.Kset := Formalism.L2.SG.Pf.unitaryCongruence.K_inv X.B.I hk
  let fT := (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
  let fS := (Matrix.mulVecLin (X.B.I.fmat k⁻¹)).toAddMonoidHom
  let T := QuotientAddGroup.map W W fT (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
  let S := QuotientAddGroup.map W W fS (fun v hv => fmat_mulVec_mem_wLf X _ hk' hv)
  have key : ∀ a b : VA X.B.I, a - b ∈ wLf X (D.naut.plGw kv.1 kv.2) ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    show a - b ∈ W ↔ _
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have hST : ∀ q, S (T q) = q := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H v =>
      show QuotientAddGroup.mk' W (X.B.I.fmat k⁻¹ *ᵥ (X.B.I.fmat k *ᵥ v)) = QuotientAddGroup.mk' W v
      rw [Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.unitaryCongruence.fmat_inv_mul X.B.I k, Matrix.one_mulVec]
  have hβ : ∀ i, D.host.g kv.1 • QuotientAddGroup.mk' W (u i) = 0 := fun i => by
    rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
      ⟨_, hg, by simp⟩ (y := u i) (hu i)
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
      simp [map_natCast]
    rw [e, Nat.cast_smul_eq_nsmul] at h1
    exact h1
  have hT : ∀ i, T (QuotientAddGroup.mk' W (u i)) =
      ∑ j, ((N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) j i).val • QuotientAddGroup.mk' W (u j) := by
    intro i
    have := (key _ _).1 (by simpa only [Nat.cast_smul_eq_nsmul] using hN i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_nsmul] at this
    rw [← this]; rfl
  have h := invMat_quot T S hST (fun i => QuotientAddGroup.mk' W (u i)) hβ
    (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) hT m
  simp only [Nat.cast_smul_eq_nsmul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

end GlobalTheory.Mem.SymFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMatrixModPlaceInFamilyInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMatrixModPlaceInFamily_inv : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (u : Fin D.R.r → VA X.B.I), (∀ i, u i ∈ X.B.I.Lf) → ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k⁻¹ ((N⁻¹ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) := by
  first | exact @GlobalTheory.Mem.SymFrame.isMatIn_inv | exact GlobalTheory.Mem.SymFrame.isMatIn_inv | (intros; apply GlobalTheory.Mem.SymFrame.isMatIn_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymEdgeConjWeightedSumEqFlagAndUnipotentPairs
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymEdgeConjWeightedSumEqFlagAndUnipotentPairs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Comb

def cw (ρ k : ℕ) (s : Bool) (i : ℕ) : ℤ :=
  if ρ ≤ i ∧ i + 1 ≠ ρ + k then (if i + 1 < ρ + k then (if s then 0 else -1) else if i = ρ + k then 1 else -1) else 0

theorem term_eq {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      if j.val = i.val + 1 then ((cw ρ k s i.val : ℤ) : R) * M i j else 0 := by
  unfold symEdge GlobalTheory.Mem.SymChar.wtB cw
  simp only [Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_neg]
  split_ifs <;> first | rfl | omega | (simp_all; done) | simp

theorem row_sum {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (c : R) (i : Fin r) :
    (∑ j : Fin r, if j.val = i.val + 1 then c * M i j else 0) =
      c * (if h : i.val + 1 < r then M i ⟨i.val + 1, h⟩ else 0) := by
  by_cases h : i.val + 1 < r
  · rw [dite_eq_left h]
    have : ∀ j : Fin r, (j.val = i.val + 1) ↔ j = ⟨i.val + 1, h⟩ := fun j => by simp [Fin.ext_iff]
    simp only [this]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h, mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega

theorem nat_id {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) (F : ℕ → R) :
    (∑ i ∈ Finset.range (2 * ρ + k), ((cw ρ k s i : ℤ) : R) * F i) =
      (∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) +
        (if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show ρ + k ≤ 2 * ρ + k by omega),
    ← Finset.sum_range_add_sum_Ico _ (show ρ ≤ ρ + k by omega),
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h0 : (∑ i ∈ Finset.range ρ, ((cw ρ k s i : ℤ) : R) * F i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [cw, show ¬ ρ ≤ i by omega]
  have h1 : (∑ t ∈ Finset.range (2 * ρ + k - (ρ + k)), ((cw ρ k s (ρ + k + t) : ℤ) : R) * F (ρ + k + t)) =
      ∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k) := by
    rw [show 2 * ρ + k - (ρ + k) = ρ by omega, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_range] at ht
    unfold cw
    by_cases h : t + 1 < ρ
    · rw [if_pos h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) = ρ + k) by omega),
        show ρ + k + (ρ - 1 - t) = 2 * ρ + k - t - 1 by omega]
      simp
    · rw [if_neg h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_pos (show ρ + k + (ρ - 1 - t) = ρ + k by omega),
        show ρ + k + (ρ - 1 - t) = ρ + k by omega]
      simp
  have h2 : (∑ t ∈ Finset.range (ρ + k - ρ), ((cw ρ k s (ρ + t) : ℤ) : R) * F (ρ + t)) =
      if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0 := by
    rw [show ρ + k - ρ = k by omega]
    cases s
    · simp only [Bool.false_eq_true, if_false]
      rw [← Finset.sum_range_reflect (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have e1 : ((cw ρ (k' + 1) false (ρ + k') : ℤ) : R) * F (ρ + k') = 0 := by
          unfold cw; rw [if_neg (by omega)]; simp
        have e2 : (if k' + 1 - 1 - 0 + 1 < k' + 1 then -F (ρ + (k' + 1) - 2 - (k' + 1 - 1 - 0)) else 0) = (0 : R) := by
          rw [if_neg (by omega)]
        rw [e1, e2, add_zero, add_zero]
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_range] at ht
        rw [if_pos (show k' + 1 - 1 - (t + 1) + 1 < k' + 1 by omega),
          show ρ + (k' + 1) - 2 - (k' + 1 - 1 - (t + 1)) = ρ + t by omega]
        simp [cw, show ρ ≤ ρ + t ∧ ρ + t + 1 ≠ ρ + (k' + 1) by omega, show ρ + t + 1 < ρ + (k' + 1) by omega]
    · simp only [if_true]
      refine Finset.sum_eq_zero fun t ht => ?_
      simp only [Finset.mem_range] at ht
      unfold cw
      split_ifs <;> first | omega | simp_all
  rw [h0, h1, h2, zero_add, add_comm]

theorem weighted_sum_eq : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  intro R _ ρ k r hr s M
  subst hr
  let F : ℕ → R := fun i => if h : i + 1 < 2 * ρ + k + 1 then M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0
  have hFv : ∀ i j (hi : i < 2 * ρ + k + 1) (hj : j < 2 * ρ + k + 1), j = i + 1 → F i = M ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hi hj e; subst e; simp only [F]; rw [dite_eq_left hj]
  have hL : (∑ i : Fin (2 * ρ + k + 1), ∑ j : Fin (2 * ρ + k + 1), if symEdge ρ k i j then
      ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      ∑ i : Fin (2 * ρ + k + 1), ((cw ρ k s i.val : ℤ) : R) * F i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [term_eq]
    rw [row_sum]
  rw [hL, Fin.sum_univ_eq_sum_range (fun i => ((cw ρ k s i : ℤ) : R) * F i), Finset.sum_range_succ,
    show F (2 * ρ + k) = 0 from dif_neg (by omega), mul_zero, add_zero, nat_id]
  congr 1
  · refine (Fin.sum_univ_eq_sum_range (fun a => if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) ρ).symm.trans
      (Finset.sum_congr rfl fun a _ => ?_)
    beta_reduce
    split_ifs with h
    · rw [hFv _ (2 * ρ + k - a.val) (by omega) (by omega) (by omega)]
    · rw [hFv _ (ρ + k + 1) (by omega) (by omega) (by omega)]
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      refine (Fin.sum_univ_eq_sum_range (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k).symm.trans
        (Finset.sum_congr rfl fun i _ => ?_)
      beta_reduce
      split_ifs with h
      · rw [hFv _ (ρ + k - 1 - i.val) (by omega) (by omega) (by omega)]
      · rfl
    · rfl

end GlobalTheory.Mem.SymChar.Comb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymEdgeConjWeightedSumEqFlagAndUnipotentPairsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symEdge_conjWeighted_sum_eq_flag_and_unipotent_pairs : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq | exact GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq | (intros; apply GlobalTheory.Mem.SymChar.Comb.weighted_sum_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.ResBar

variable {D : D7}

theorem unip_inv_sup {κ : Type} [CommRing κ] {r : ℕ} {N : GL (Fin r) κ} (hN : N ∈ unip κ r) (i j : Fin r)
    (hij : j.val = i.val + 1) :
    ((N⁻¹ : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = -(N : Matrix (Fin r) (Fin r) κ) i j := by
  have hi := Subgroup.inv_mem _ hN
  have h := unip_mul_entry hi hN (i := i) (j := j) (show i.val < j.val by omega) (fun l h1 h2 => by
    exfalso
    have : i.val < l.val := h1
    have : l.val < j.val := h2
    omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

abbrev QW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Type :=
  (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ⧸ (wInt X w).toAddSubgroup

abbrev mkW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) →+ QW X w :=
  QuotientAddGroup.mk' _

theorem mkW_eq {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a b : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a - b ∈ wInt X w) : mkW X w a = mkW X w b := by
  show (QuotientAddGroup.mk a : QW X w) = QuotientAddGroup.mk b
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem mkW_zero {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {a : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} (h : a ∈ wInt X w) : mkW X w a = 0 := by
  rw [← map_zero (mkW X w)]
  exact mkW_eq (by rw [sub_zero]; exact h)

theorem phi_exists (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (g : ℕ) [NeZero g]
    (hg : ((g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w) :
    ∃ φ : ZMod g →+ QW X w, ∀ t : ZMod g, φ t = t.val • mkW X w 1 := by
  refine ⟨ZMod.lift g ⟨zmultiplesHom _ (mkW X w 1), ?_⟩, fun t => ?_⟩
  · rw [zmultiplesHom_apply, natCast_zsmul, ← map_nsmul, nsmul_one]
    exact mkW_zero hg
  · conv_lhs => rw [← ZMod.natCast_zmod_val t]
    have e : ((t.val : ℕ) : ZMod g) = ((t.val : ℤ) : ZMod g) := by simp
    rw [e, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul]

theorem modW_of {X : HidaSetting D} {w : HeightOneSpectrum (𝓞 D.host.E)} {g : ℕ}
    {φ : ZMod g →+ QW X w} (hφ : ∀ t : ZMod g, φ t = t.val • mkW X w 1)
    {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F} {t : ZMod g} (h : mkW X w c = φ t) : ModW X w c t := by
  unfold ModW
  rw [hφ, ← map_nsmul, nsmul_one] at h
  show (c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∈ (wInt X w).toAddSubgroup
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  exact h

theorem read (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {M : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hM : GlobalTheory.Mem.SymFrame.IsMatIn X w u x M)
    {v : VA X.B.I} (hv : v ∈ X.B.I.Lf) (p q : Fin D.R.r) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hG : ∀ j, hA X.B.I v (u j) - (if j = q then c else 0) ∈ wInt X w) :
    mkW X w (hA X.B.I v (X.B.I.fmat x *ᵥ u p)) = (M q p).val • mkW X w c := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mkW_eq (hA_isMatIn X w hM hv p), map_sum]
  have e : ∀ j, mkW X w ((((M j p).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I v (u j)) =
      if j = q then (M q p).val • mkW X w c else 0 := by
    intro j
    rw [← nsmul_eq_mul, map_nsmul, mkW_eq (hG j)]
    split_ifs with hj
    · rw [hj]
    · rw [map_zero, smul_zero]
  simp only [e, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem r_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨t, ht⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r Formalism.BasicNotions.Ranks.rS
  omega

theorem symVec_mem (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (j : Fin D.R.r) :
    GlobalTheory.Mem.SymFrame.symVec X w j ∈ X.B.I.Lf := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact (X.vectorsInLattice.2.2 _).1
  · exact (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem symmetricOrderFrameModPlace_last_block (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) (p : Fin D.R.r)
    (hp : p.val = 2 * D.R.rS + D.R.k - a.val) : GlobalTheory.Mem.SymFrame.symVec X w p = X.f0 a := by
  have hr := r_eq D
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  ext
  simp only
  omega

theorem symVec_bwd (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hE : ¬ GlobalTheory.Mem.SymFrame.EwAt X w)
    (i : Fin D.R.k) (p : Fin D.R.r) (hp : p.val = D.R.rS + D.R.k - 1 - i.val) :
    GlobalTheory.Mem.SymFrame.symVec X w p = X.bwd i := by
  unfold GlobalTheory.Mem.SymFrame.symVec GlobalTheory.SeeConjRead.flagV GlobalTheory.Mem.SymFrame.epsW
  rw [if_neg hE, dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  ext
  simp only [Fin.val_rev]
  omega

theorem ite_val {r : ℕ} {R : Type} [Zero R] (j q : Fin r) (n : ℕ) (hq : q.val = n) (c : R) :
    (if j.val = n then c else 0) = (if j = q then c else 0) := by
  by_cases h : j = q
  · subst h; simp [hq]
  · have : j.val ≠ n := fun e => h (Fin.ext (by omega))
    simp [h, this]

open Matrix in
private theorem hA_move' {D : D7} (X : HidaSetting D) (x : X.B.I.Gf) (v w : VA X.B.I) :
    hA X.B.I v (X.B.I.fmat x *ᵥ w) = hA X.B.I (X.B.I.fmat x⁻¹ *ᵥ v) w := by
  let I := X.B.I
  have hform_mv : ∀ {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
      (J M : Matrix n n A) (a b : n → A),
      Formalism.UG.hform σ J (M *ᵥ a) (M *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) a b := by
    intro A _ n _ σ J M a b
    have e : ∀ (N : Matrix n n A) (u v' : n → A), Formalism.UG.hform σ N u v' = (σ ∘ u) ⬝ᵥ (N *ᵥ v') := by
      intro N u v'
      simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
    have hσ : σ ∘ (M *ᵥ a) = M.map σ *ᵥ (σ ∘ a) := funext fun i => RingHom.map_mulVec σ M a i
    rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]
  have hunit : ∀ (a b : VA I), hA I (I.fmat x *ᵥ a) (I.fmat x *ᵥ b) = hA I a b := fun a b => by
    unfold hA
    rw [hform_mv]
    have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Formalism.MainNotions.S.Af I.F)) (I.fmat x) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * I.fmat x =
        I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := x.2
    rw [h]
  have hmul : I.fmat x * I.fmat x⁻¹ = 1 := Units.mul_inv x.1
  change hA I v (I.fmat x *ᵥ w) = hA I (I.fmat x⁻¹ *ᵥ v) w
  rw [← hunit (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, hmul, one_mulVec]

theorem resBar : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  intro D X h hι hg kv k hk N hN hNu
  classical
  have hgw := hg kv
  set w := D.naut.plGw kv.1 kv.2 with hw
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have hgA : (((D.host.g kv.1 : ℕ)) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E), ⟨_, hgw, ?_⟩, ?_⟩
    · simp
    · simp
  obtain ⟨φ, hφ⟩ := phi_exists X w _ hgA
  have hr := r_eq D
  set u := GlobalTheory.Mem.SymFrame.symVec X w with hu_def
  have hu : ∀ i, u i ∈ X.B.I.Lf := symVec_mem X w
  have hNi := GlobalTheory.T.isMatrixModPlaceInFamily_inv D X kv hgw u hu k hk N hN
  have hU : N ∈ unip _ _ := unipCol_le _ _ _ hNu
  rw [GlobalTheory.T.symEdge_conjWeighted_sum_eq_flag_and_unipotent_pairs _ _ _ hr]
  apply modW_of hφ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [argS, map_add (f := _), map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
    have e := hA_move' X k⁻¹ (nxt X.e0 X.z0 a) (X.f0 a)
    rw [inv_inv] at e
    rw [← e, ← symmetricOrderFrameModPlace_last_block X w a ⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ rfl]
    by_cases ha : a.val + 1 < D.R.rS
    · rw [dite_eq_left ha]
      have hn : nxt X.e0 X.z0 a = X.e0 ⟨a.val + 1, ha⟩ := by unfold nxt; rw [dite_eq_left ha]
      rw [hn, read X w hNi (X.vectorsInLattice.1 _).1 _ ⟨2 * D.R.rS + D.R.k - a.val - 1, by omega⟩ 1 (fun j => by
        rw [← ite_val j _ (2 * D.R.rS + D.R.k - (a.val + 1)) (by simp only; omega)]
        exact GlobalTheory.T.hermitian_e0_symmetric_frame D X kv hgw ⟨a.val + 1, ha⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
    · rw [dite_eq_right ha]
      have hn : nxt X.e0 X.z0 a = X.z0 := by unfold nxt; rw [dite_eq_right ha]
      have hp : (⟨2 * D.R.rS + D.R.k - a.val, by omega⟩ : Fin D.R.r) = ⟨D.R.rS + D.R.k + 1, by omega⟩ :=
        Fin.ext (by simp only; omega)
      rw [hn, hp, read X w hNi X.vectorsInLattice.2.1 _ ⟨D.R.rS + D.R.k, by omega⟩ (-1) (fun j => by
        rw [← ite_val j _ (D.R.rS + D.R.k) rfl]
        exact GlobalTheory.T.hermitian_z0_symmetric_frame D X kv hgw j), map_neg, smul_neg, ← hφ, ← map_neg, unip_inv_sup hU _ _ (by simp only),
        neg_neg]
  · by_cases hE : GlobalTheory.Mem.SymFrame.EwAt X w
    · have hs : side X w = true := by simp [side, hE]
      rw [hs, if_pos rfl, map_zero]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dite_eq_left hi]
        apply mkW_zero
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have hb : X.bwd i ∈ wLf X w := by
          have h1 := hE (X.bwd i) (X.vectorsInLattice.2.2 i).2
          have e : (1 - X.ew) • X.bwd i = X.bwd i := by
            conv_lhs => rw [X.bwd_w i]
            rw [smul_smul, sub_mul, one_mul, X.ew_orth, sub_zero, ← X.bwd_w i]
          rwa [e] at h1
        exact hA_mem_wInt X w (Formalism.L2.SG.Pf.unitaryCongruence.K_mv X.B.I hk (X.vectorsInLattice.2.2 _).1) hb
      · rw [dite_eq_right hi, map_zero, map_zero]
    · have hs : side X w = false := by simp [side, hE]
      have hew := GlobalTheory.T.conj_idempotent_sub_one_mem_placeIdeal D X h hι kv hgw hE
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hs, if_neg (by simp), map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i.val + 1 < D.R.k
      · rw [dite_eq_left hi, dite_eq_left hi]
        rw [← Formalism.L2.SG.Pf.unitaryCongruence.hA_symm]
        have e := hA_move' X k⁻¹ (X.bw ⟨i.val + 1, hi⟩) (X.bwd i)
        rw [inv_inv] at e
        rw [← e, ← symVec_bwd X w hE i ⟨D.R.rS + D.R.k - 1 - i.val, by omega⟩ rfl,
          read X w hNi (X.vectorsInLattice.2.2 _).1 _ ⟨D.R.rS + D.R.k - 2 - i.val, by omega⟩ 1 (fun j => by
            rw [← ite_val j _ (D.R.rS + D.R.k - 1 - (i.val + 1)) (by simp only; omega)]
            exact GlobalTheory.T.hermitianForm_middle_symmetricFrame_not_oneAt D X kv hgw hE hew ⟨i.val + 1, hi⟩ j), ← hφ, unip_inv_sup hU _ _ (by simp only; omega)]
      · rw [dite_eq_right hi, dite_eq_right hi, map_zero, map_zero, map_zero]

end GlobalTheory.Mem.SymChar.ResBar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricCharResidueConjEqWeightedUnipotentSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricCharResidue_conj_eq_weightedUnipotentSum : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ (kv : Σ k : Fin 2, D.nd.PlG k), ∀ k ∈ X.B.I.Kset, ∀ N : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k → GlobalTheory.Mem.SymChar.ModW X (D.naut.plGw kv.1 kv.2) (sigA X.B.I (GlobalTheory.Mem.SymChar.argS X k)) (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j : ℤ) : ZMod (D.host.g kv.1)) * (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.ResBar.resBar | exact GlobalTheory.Mem.SymChar.ResBar.resBar | (intros; apply GlobalTheory.Mem.SymChar.ResBar.resBar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRoot
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar

theorem star_character_eq_prod_additive_characters_root : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ (ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → Fin D.R.r → (ZMod (D.host.g kv.1))ˣ), (∀ kv, ψ' kv ≠ 1) ∧ ∀ k ∈ X.K2, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) → star (X.chi2 k) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j else 0) :=
  by
  intro D X h hE hg
  obtain ⟨ψ', hψ, hchar⟩ := GlobalTheory.T.finiteAddChar_conj_eq_prod_placeResidueChars D X h hE hg
  refine ⟨ψ', fun kv i j => if GlobalTheory.Mem.SymChar.wtA D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j +
      GlobalTheory.Mem.SymChar.wtB D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j = 1 then 1 else -1, hψ, ?_⟩
  intro k hk Ns hM hU
  have hK : k ∈ X.B.I.Kset := hk.1
  rw [GlobalTheory.Mem.SymChar.otherInstanceCharacter_eq_psi_symmetricArgument, hchar _ _ _ (fun kv => GlobalTheory.T.heckeArgument_residue_eq_weighted_symmetricFrameSum D X h hE hg kv k hK _ (hM kv))
    (fun kv => GlobalTheory.T.symmetricCharResidue_conj_eq_weightedUnipotentSum D X h hE hg kv k hK (Ns kv) (hM kv) (hU kv))]
  refine Finset.prod_congr rfl fun kv _ => ?_
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases he : symEdge D.R.rS D.R.k i j
  · simp only [if_pos he]
    rw [← add_mul, ← Int.cast_add]
    rcases GlobalTheory.Mem.SymChar.wt_add D.R.rS D.R.k (GlobalTheory.Mem.SymChar.side X (D.naut.plGw kv.1 kv.2)) i j with h2 | h2
    · rw [h2]; simp
    · rw [h2]; simp
  · simp only [if_neg he, add_zero]

end GlobalTheory.Mem.SymChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarCharacterEqProdAdditiveCharactersRootStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_character_eq_prod_additive_characters_root_alt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ (ψ' : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (a : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → Fin D.R.r → (ZMod (D.host.g kv.1))ˣ), (∀ kv, ψ' kv ≠ 1) ∧ ∀ k ∈ X.K2, ∀ Ns : G0g D.nd, (∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))))) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k) → star (X.chi2 k) = ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j else 0) := by
  first | exact @GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root | exact GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root | (intros; apply GlobalTheory.Mem.SymChar.star_character_eq_prod_additive_characters_root <;> assumption)
end
