module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecompL
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ScalarAgreeRatCOfScalT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameOO3FrameValTrans
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem pi_levi (w : D.what₂.Word) {n a h : X.B.I.Ginf} (hn : n ∈ X.NinfU w) (ha : a ∈ Formalism.L2.SG.RealObj.HsetU X w)
    (hh : h ∈ X.SinfU w) : X.piU w (a * h) = (X.piU w (n * a)).comp (X.piU w h) := by
  have hnS : n ∈ X.SinfU w := fun v => (hn v).1
  have haS := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X w ha
  rw [(X.piU_rep w).2.1 a haS h hh, (X.piU_rep w).2.1 n hnS a haS, (X.piU_rep w).2.2.2.1 n hn, one_mul]
  rfl

end Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def decVal (g g' h h' : X.B.I.Ginf) (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    X.Vpi u' →L[ℂ] X.Vpi u :=
  Formalism.L2.SG.PairVal.cTerm vR s.toTerm •
    ((X.piU u g).comp ((X.piU u h).comp ((Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.toTerm)).comp
      ((X.piU u' h'⁻¹).comp (X.piU u' g'⁻¹)))))

theorem classFrameOO3_frameVal_trans (g g' h h' : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hh : h ∈ X.SinfU u) (hh' : h' ∈ X.SinfU u')
    (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    frameVal X Y u u' vR i0 i0' νq ((Formalism.L2.SG.RealObj.InfCut.piIso X u h hh).trans (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg))
      ((Formalism.L2.SG.RealObj.InfCut.piIso X u' h' hh').trans (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg')) s =
      decVal X Y u u' vR i0 i0' νq g g' h h' s := by
  have hs : ∀ (w : D.what₂.Word) (a : X.B.I.Ginf) (ha : a ∈ X.SinfU w) (y : X.Vpi w),
      (Formalism.L2.SG.RealObj.InfCut.piIso X w a ha).symm y = X.piU w a⁻¹ y := fun w a ha y => by
    have := congrArg (fun T : X.Vpi w →L[ℂ] X.Vpi w => T y) (Formalism.L2.SG.RealObj.InfCut.piIso_symm X w a ha)
    exact this
  unfold frameVal decVal
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, hs]

theorem chiOO_decomp (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ)
    (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ) (hrel : s.1.relevant) :
    ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ ∧
      ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
          (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) h h' ∧
        chiOO X Y u u' s.1 = decVal X Y u u' vR i0 i0' νq g g' h h' s.1 := by
  obtain ⟨hpt, g, hg, g', hg', hdec, hph⟩ := h3 R ρ s hrel
  have hDF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ hpt (h4' R ρ s hrel)
    exact ⟨(h, h'), hh⟩
  have hcS : hDF.choose.1 ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hDF.choose_spec.1
  have hcS' : hDF.choose.2 ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.choose_spec.2.1
  have hcSi : hDF.choose.1⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hcS
  refine ⟨g, hg, g', hg', hdec, hDF.choose.1, hDF.choose.2, hDF.choose_spec, ?_⟩
  rw [← classFrameOO3_frameVal_trans X Y u u' vR i0 i0' νq g g' _ _ hg hg' hcS hcS']
  have hat : s.1.toTerm.atPt (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) := by
    obtain ⟨w0, hw0⟩ := h1 R ρ s hrel
    exact Formalism.L2.SG.PairVal.ptOf_spec _ ⟨w0, hw0, hrel⟩
  have hcT : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) :=
    Formalism.L2.SG.PairVal.cTerm_of_atPt vR _ hat (fun w' hw' => h2 _ w' _ hw' hat)
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      (X.piU u hDF.choose.1⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
          (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
        (X.piU u' hDF.choose.2)) := by
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [if_pos hpt, dite_eq_left hDF]
  have hO : Formalism.L2.SG.TermOp.OOt s.1 =
      (((vR s.1.toTerm : ℝ) : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g'))) •
        (((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
          ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
            Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
              (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
            ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))) := by
    rw [h5 R ρ s hrel g hg g' hg' hdec, ← smul_smul]
    congr 1
    rw [hdec]
    exact ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' _ _ _ _
      (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  have e1 : ∀ z, X.piU u hDF.choose.1 (X.piU u hDF.choose.1⁻¹ z) = z := fun z =>
    ClassFrameUnitaryProducts.piU_mul_inv_apply X u hcS z
  have e2 : ∀ y, X.piU u' hDF.choose.2 ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').symm y) = y :=
    fun y => (Formalism.L2.SG.RealObj.InfCut.piIso X u' hDF.choose.2 hcS').apply_symm_apply y
  unfold chiOO frameVal
  rw [hO, hcT, hV, smul_smul, ← hph]
  have hsc : ∀ a c r : ℂ, a * (r * c) = a * c * r := fun a c r => by ring
  rw [hsc]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_trans, Formalism.L2.SG.RealObj.InfCut.piIso_apply, e1, e2]

def DFrameMoveC : Prop :=
  ∀ γ h h' g g' : X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' γ h h' → g ∈ X.SinfU u → g' ∈ X.SinfU u' →
    ∃ k k', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' (g * γ * g'⁻¹) k k' ∧
      X.piU u k = (X.piU u g).comp (X.piU u h) ∧ X.piU u' k' = (X.piU u' g').comp (X.piU u' h')

def SDecompC (w : D.what₂.Word) : Prop :=
  ∀ g ∈ X.SinfU w, ∃ n ∈ X.NinfU w, ∃ a ∈ Formalism.L2.SG.RealObj.HsetU X w, g = n * a

def DFrameMoveHC : Prop :=
  ∀ γ h h' n a n' a' : X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' γ h h' →
    n ∈ X.NinfU u → a ∈ Formalism.L2.SG.RealObj.HsetU X u → n' ∈ X.NinfU u' → a' ∈ Formalism.L2.SG.RealObj.HsetU X u' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' (n * a * γ * a'⁻¹ * n'⁻¹) (a * h) (a' * h')

theorem dFrameMoveC_of (hS : SDecompC X u) (hS' : SDecompC X u') (hM : DFrameMoveHC X u u' i0 i0') :
    DFrameMoveC X u u' i0 i0' := by
  intro γ h h' g g' hD hg hg'
  obtain ⟨n, hn, a, ha, rfl⟩ := hS g hg
  obtain ⟨n', hn', a', ha', rfl⟩ := hS' g' hg'
  refine ⟨a * h, a' * h', ?_, ?_, ?_⟩
  · have e : n * a * γ * (n' * a')⁻¹ = n * a * γ * a'⁻¹ * n'⁻¹ := by group
    rw [e]
    exact hM γ h h' n a n' a' hD hn ha hn' ha'
  · exact Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition.pi_levi X u hn ha (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hD.1)
  · exact Formalism.L2.SG.Pf.RowForm.ClassFrameLeviDecomposition.pi_levi X u' hn' ha' (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hD.2.1)

theorem ptValueC_of (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : DecompPhaseC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (hM : DFrameMoveC X u u' i0 i0') :
    PtValueC X Y u u' vR i0 i0' νq κ := by
  intro R ρ s hrel
  obtain ⟨g, hg, g', hg', hdec, h, h', hDF, hval⟩ := chiOO_decomp X Y u u' vR i0 i0' νq κ h1 h2 h3 h4 h4' h5 R ρ s hrel
  obtain ⟨k, k', hK, hk, hk'⟩ := hM _ h h' g g' hDF hg hg'
  refine ⟨k, k', hdec ▸ hK, ?_⟩
  have hkS : k ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hK.1
  have hki : k⁻¹ ∈ X.SinfU u := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hkS
  have hgi : g'⁻¹ ∈ X.SinfU u' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' hg'
  have hhi : h'⁻¹ ∈ X.SinfU u' :=
    Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' (Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hDF.2.1)
  have c1 : ∀ y, X.piU u k⁻¹ (X.piU u k y) = y := fun y => by
    have := ClassFrameUnitaryProducts.piU_mul_inv_apply X u hki y
    rwa [inv_inv] at this
  have c2 : ∀ y, X.piU u' g'⁻¹ (X.piU u' g' y) = y := fun y => by
    have := ClassFrameUnitaryProducts.piU_mul_inv_apply X u' hgi y
    rwa [inv_inv] at this
  have c3 : ∀ y, X.piU u' h'⁻¹ (X.piU u' h' y) = y := fun y => by
    have := ClassFrameUnitaryProducts.piU_mul_inv_apply X u' hhi y
    rwa [inv_inv] at this
  have hk1 : ∀ y, X.piU u g (X.piU u h y) = X.piU u k y := fun y => by rw [hk]; rfl
  have hk2 : ∀ y, X.piU u' k' y = X.piU u' g' (X.piU u' h' y) := fun y => by rw [hk']; rfl
  rw [hval]
  unfold decVal
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul, hk2, c2, c3, hk1, c1]

end Formalism.L2.SG.Pf.RowForm
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameSDecomp
noncomputable section

open Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.RowForm

namespace LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem frameLoc (w : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F) :
    PI.SchurPlaces.LeviLA.Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
      (rv X.B.I v (X.zR w)) (X.wfr w v) := by
  let fr := Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X w v
  exact
    { ee := fr.ee
      ef := fr.ef
      ff := fr.ff
      ez := fr.ez
      fz := fr.fz
      ew := fr.ew
      fw := fr.fw
      zw := fr.zw
      ww := fr.ww
      zz := fun h0 => fr.T_ne (neg_eq_zero.1 (fr.zz.symm.trans h0))
      card := by
        have h := fr.card
        omega }

end LocalFrameDecomposition

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sDecompC_holds (w : D.what₂.Word) : SDecompC X w := by
  intro g hg
  have hgi : g⁻¹ ∈ X.SinfU w := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hg
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR w)) (uMat (g⁻¹ v)) := hgi
  choose V hVu hVe hVf hVz _ hVN using fun v =>
    PI.SchurPlaces.LeviLA.levi_place (LocalFrameDecomposition.frameLoc X w v)
      ((g⁻¹ v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) (g⁻¹ v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hs0H : s0 ∈ HsetU X w := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp
      subst hp
      exact hVz v
  have hN : s0⁻¹ * g⁻¹ ∈ X.NinfU w := fun v => by
    have e : uMat ((s0⁻¹ * g⁻¹) v) =
        (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
          uMat (g⁻¹ v) := rfl
    rw [e]
    exact hVN v
  have hN' := Formalism.L2.SG.RealObj.SpanPreservation.ninfU_inv X w hN
  rw [_root_.mul_inv_rev, inv_inv, inv_inv] at hN'
  exact ⟨g * s0, hN', s0⁻¹, Formalism.L2.SG.RealObj.InfCut.hsetU_inv X w hs0H, by group⟩

end Formalism.L2.SG.Pf.RowForm
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.ClassFrameMoveH
noncomputable section

open Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

namespace Formalism.L2.SG.Pf.RowForm

namespace ClassFrameUnitaryMoves

variable {n r k : ℕ}

def wm (ε : Fin n → Bool) (wb : Fin k → Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j => hJ ε (wb i) (M *ᵥ wb j)

variable {ε : Fin n → Bool}

theorem uMat_mul_ (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem uMat_mul_inv_ (a : Formalism.REAL.UJ ε) : uMat a * uMat a⁻¹ = 1 := by simp [uMat]

theorem uMat_inv_mul_ (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by simp [uMat]

theorem cancel_ (g : Formalism.REAL.UJ ε) (w : Fin n → ℂ) : uMat g *ᵥ (uMat g⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, uMat_mul_inv_, one_mulVec]

theorem hJ_adj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g *ᵥ y) = hJ ε (uMat g⁻¹ *ᵥ x) y := by
  rw [← PtRepPf.hJ_UJ ε g (uMat g⁻¹ *ᵥ x) y, cancel_]

theorem fix_inv (g : Formalism.REAL.UJ ε) {x : Fin n → ℂ} (h : uMat g *ᵥ x = x) : uMat g⁻¹ *ᵥ x = x := by
  calc uMat g⁻¹ *ᵥ x = uMat g⁻¹ *ᵥ (uMat g *ᵥ x) := by rw [h]
    _ = x := by rw [mulVec_mulVec, uMat_inv_mul_, one_mulVec]

theorem hJ_span_zero (w : Fin n → ℂ) {S : Set (Fin n → ℂ)} (hS : ∀ y ∈ S, hJ ε w y = 0) {x : Fin n → ℂ}
    (hx : x ∈ Submodule.span ℂ S) : hJ ε w x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS y hy
  | zero => exact PtRepPf.hJ_zero_right ε w
  | add x y _ _ hx hy => rw [PtRepPf.hJ_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [PtRepPf.hJ_smul_right, hx, mul_zero]

theorem fam_fix {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {M : Matrix (Fin n) (Fin n) ℂ}
    (he : ∀ c, M *ᵥ e c = e c) (hz : M *ᵥ z = z) (b : Fin (r + 1)) : M *ᵥ fam e z b = fam e z b := by
  induction b using Fin.lastCases with
  | last => rw [PtRepPf.fam_last, hz]
  | cast c => rw [PtRepPf.fam_cs, he]

theorem tri (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : InS e z M) :
    ∃ Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, Q.IsUpperTriangular ∧ (∀ b, Q b b = 1) ∧
      ∀ b, M *ᵥ fam e z b = ∑ c, Q c b • fam e z c := by
  have hmem : ∀ b : Fin (r + 1), (M - 1) *ᵥ fam e z b ∈ Submodule.span ℂ (fam e z '' {c | c < b}) := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [PtRepPf.fam_last]
      refine Submodule.span_mono ?_ hM.2
      rintro _ ⟨c, -, rfl⟩
      exact ⟨Fin.castSucc c, Fin.castSucc_lt_last c, PtRepPf.fam_cs e z c⟩
    | cast a =>
      rw [PtRepPf.fam_cs]
      refine Submodule.span_mono ?_ (hM.1 a)
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨Fin.castSucc c, Fin.castSucc_lt_castSucc_iff.2 hc, PtRepPf.fam_cs e z c⟩
  choose l hl hlx using fun b => (Finsupp.mem_span_image_iff_linearCombination (R := ℂ)).1 (hmem b)
  have hz : ∀ b c, ¬ c < b → l b c = 0 := fun b c hc => by
    by_contra h
    have h2 := hl b
    rw [Finsupp.mem_supported] at h2
    exact hc (h2 (Finsupp.mem_support_iff.2 h))
  refine ⟨Matrix.of fun c b => (if c = b then (1 : ℂ) else 0) + l b c, ?_, ?_, ?_⟩
  · intro i j hji
    have hji' : j < i := hji
    rw [Matrix.of_apply, if_neg (ne_of_lt hji').symm, hz j i (not_lt.2 hji'.le), add_zero]
  · intro b
    rw [Matrix.of_apply, if_pos rfl, hz b b (lt_irrefl b), add_zero]
  · intro b
    have e1 : M *ᵥ fam e z b = fam e z b + (M - 1) *ᵥ fam e z b := by
      rw [sub_mulVec, one_mulVec]; abel
    rw [e1, ← hlx b, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ (fun i => zero_smul ℂ (fam e z i))]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem col_last (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQ : Q.IsUpperTriangular) (hd : ∀ b, Q b b = 1) :
    Qᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
  funext d
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, conjTranspose_apply]
  by_cases h : d = Fin.last r
  · subst h; rw [hd, star_one, if_pos rfl]
  · have h0 : Q (Fin.last r) d = 0 := hQ (lt_of_le_of_ne (Fin.le_last d) h)
    rw [h0, star_zero, if_neg h]

theorem row_last (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQ : Q.IsUpperTriangular) (hd : ∀ b, Q b b = 1) :
    Pi.single (Fin.last r) 1 ᵥ* Q = Pi.single (Fin.last r) 1 := by
  funext c
  simp only [vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h : c = Fin.last r
  · subst h; rw [hd, if_pos rfl]
  · have h0 : Q (Fin.last r) c = 0 := hQ (lt_of_le_of_ne (Fin.le_last c) h)
    rw [h0, if_neg h]

theorem tri_adj (Z Q Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQt : Q.IsUpperTriangular) (hQd : ∀ b, Q b b = 1)
    (hQt' : Q'.IsUpperTriangular) (hQd' : ∀ b, Q' b b = 1) :
    (Q' * adjugate (Qᴴ * Z * Q')) *ᵥ Pi.single (Fin.last r) 1 = adjugate Z *ᵥ Pi.single (Fin.last r) 1 ∧
      Pi.single (Fin.last r) 1 ᵥ* (adjugate (Qᴴ * Z * Q') * Qᴴ) = Pi.single (Fin.last r) 1 ᵥ* adjugate Z ∧
      (Qᴴ * Z * Q').det = Z.det := by
  have hQdet : Q.det = 1 := by rw [det_of_isUpperTriangular hQt]; simp [hQd]
  have hQdet' : Q'.det = 1 := by rw [det_of_isUpperTriangular hQt']; simp [hQd']
  have hcolQ : Qᴴ *ᵥ Pi.single (Fin.last r) (1 : ℂ) = Pi.single (Fin.last r) 1 := col_last Q hQt hQd
  have hrowQ : Pi.single (Fin.last r) (1 : ℂ) ᵥ* Q' = Pi.single (Fin.last r) 1 := row_last Q' hQt' hQd'
  have hA1 : adjugate Qᴴ * Qᴴ = 1 := by rw [adjugate_mul, det_conjTranspose, hQdet, star_one, one_smul]
  have hA2 : Q' * adjugate Q' = 1 := by rw [mul_adjugate, hQdet', one_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [adjugate_mul_distrib, adjugate_mul_distrib, ← Matrix.mul_assoc, hA2, Matrix.one_mul, ← mulVec_mulVec]
    congr 1
    conv_lhs => rw [← hcolQ]
    rw [mulVec_mulVec, hA1, one_mulVec]
  · have hs : Pi.single (Fin.last r) (1 : ℂ) ᵥ* adjugate Q' = Pi.single (Fin.last r) 1 := by
      conv_lhs => rw [← hrowQ]
      rw [vecMul_vecMul, hA2, vecMul_one]
    rw [adjugate_mul_distrib, adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc, hA1, Matrix.mul_one,
      ← vecMul_vecMul, hs]
  · rw [det_mul, det_mul, det_conjTranspose, hQdet, hQdet', star_one, one_mul, mul_one]

theorem Dl_full (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Formalism.L2.SG.RealObj.Dl Z (r + 1) = Z.det := by
  unfold Formalism.L2.SG.RealObj.Dl
  rw [dite_eq_left le_rfl]
  rfl

theorem xPr_move (Z₂ Z Q' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (G₂ G Nm Am : Matrix (Fin n) (Fin n) ℂ)
    (f' : Fin (r + 1) → Fin n → ℂ) (hG : ∀ b, G₂ *ᵥ f' b = Nm *ᵥ (Am *ᵥ ∑ c, Q' c b • (G *ᵥ f' c)))
    (hc : (Q' * adjugate Z₂) *ᵥ Pi.single (Fin.last r) 1 = adjugate Z *ᵥ Pi.single (Fin.last r) 1) :
    xPr Z₂ G₂ f' = Nm *ᵥ (Am *ᵥ xPr Z G f') := by
  have hc' : ∀ c, ∑ b, adjugate Z₂ b (Fin.last r) * Q' c b = adjugate Z c (Fin.last r) := fun c => by
    have h := congrFun hc c
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.mul_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  unfold xPr
  simp only [hG, mulVec_sum, mulVec_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul, hc' c]

theorem xUn_move (Z₂ Z Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Ni Ai : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin (r + 1) → Fin n → ℂ) (hQ : ∀ b, Ni *ᵥ f b = ∑ c, Q c b • f c) (hA : ∀ b, Ai *ᵥ f b = f b)
    (hr : Pi.single (Fin.last r) 1 ᵥ* (adjugate Z₂ * Qᴴ) = Pi.single (Fin.last r) 1 ᵥ* adjugate Z) :
    Ai *ᵥ (Ni *ᵥ xUn Z₂ f) = xUn Z f := by
  have hr' : ∀ d, ∑ a, star (adjugate Z₂ (Fin.last r) a) * Q d a = star (adjugate Z (Fin.last r) d) := by
    intro d
    have h := congrFun hr d
    simp only [vecMul, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Matrix.mul_apply, conjTranspose_apply] at h
    rw [← h, star_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [star_mul', star_star]
  unfold xUn
  simp only [mulVec_sum, mulVec_smul, hQ, Finset.smul_sum, smul_smul, hA]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, hr' d]

theorem xPr_perp (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (f' : Fin (r + 1) → Fin n → ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin r) : hJ ε (e c) (xPr (Zhat ε (fam e z) f' G) G f') = 0 := by
  have h1 := congrFun₂ (mul_adjugate (Zhat ε (fam e z) f' G)) (Fin.castSucc c) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last c).ne, smul_zero] at h1
  unfold xPr
  rw [PtRepPf.hJ_sum_right, ← h1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [PtRepPf.hJ_smul_right, ← PtRepPf.fam_cs e z c]
  exact mul_comm _ _

theorem xUn_perp (f : Fin (r + 1) → Fin n → ℂ) (e' : Fin r → Fin n → ℂ) (z' : Fin n → ℂ) (g : Formalism.REAL.UJ ε)
    (c : Fin r) : hJ ε (e' c) (uMat g⁻¹ *ᵥ xUn (Zhat ε f (fam e' z') (uMat g)) f) = 0 := by
  have h1 := congrFun₂ (adjugate_mul (Zhat ε f (fam e' z') (uMat g))) (Fin.last r) (Fin.castSucc c)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last c).ne', smul_zero] at h1
  rw [hJ_adj, inv_inv]
  unfold xUn
  rw [PtRepPf.hJ_sum_right]
  calc ∑ a, hJ ε (uMat g *ᵥ e' c) (star (adjugate (Zhat ε f (fam e' z') (uMat g)) (Fin.last r) a) • f a)
      = star (∑ a, adjugate (Zhat ε f (fam e' z') (uMat g)) (Fin.last r) a *
          Zhat ε f (fam e' z') (uMat g) a (Fin.castSucc c)) := by
        rw [star_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [PtRepPf.hJ_smul_right, star_mul', ← PtRepPf.hJ_conj, ← PtRepPf.fam_cs e' z' c]
        rfl
    _ = 0 := by rw [h1, star_zero]

theorem pair_na (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (nn a : Formalism.REAL.UJ ε)
    (Q : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hQ : ∀ b, uMat nn⁻¹ *ᵥ fam e z b = ∑ c, Q c b • fam e z c)
    (ha : ∀ b, uMat a *ᵥ fam e z b = fam e z b) (b : Fin (r + 1)) (y : Fin n → ℂ) :
    hJ ε (fam e z b) (uMat nn *ᵥ (uMat a *ᵥ y)) = ∑ d, star (Q d b) * hJ ε (fam e z d) y := by
  rw [hJ_adj, hJ_adj, hQ, mulVec_sum, PtRepPf.hJ_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mulVec_smul, fix_inv a (ha d), PtRepPf.hJ_smul_left]

theorem dot_self_ (y : Fin k → ℂ) : ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem eN_unitary (U : Matrix (Fin k) (Fin k) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (y : Fin k → ℂ) :
    eN (U *ᵥ y) = eN y := by
  have hUU : star U * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
  have h : ((∑ i, ‖(U *ᵥ y) i‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) := by
    rw [dot_self_, dot_self_, star_mulVec, dotProduct_mulVec, vecMul_vecMul, ← Matrix.star_eq_conjTranspose, hUU,
      vecMul_one]
  unfold eN
  rw [Complex.ofReal_injective h]

section Fr

variable (F : PtRepPf.Fr ε r k)

theorem wCoord_fix (M : Matrix (Fin n) (Fin n) ℂ) (he : ∀ c, M *ᵥ F.e c = F.e c)
    (hf : ∀ c, M *ᵥ F.fd c = F.fd c) (hz : M *ᵥ F.z = F.z) (x : Fin n → ℂ) :
    wCoord ε F.wb (M *ᵥ x) = wm ε F.wb M *ᵥ wCoord ε F.wb x := by
  have hx := PtRepPf.expand_of_dual ε F.bv F.dv F.card_ix F.dual x
  funext i
  have h2 : hJ ε (F.wb i) (M *ᵥ x) = ∑ j, hJ ε (F.dv j) x * hJ ε (F.wb i) (M *ᵥ F.bv j) := by
    conv_lhs => rw [hx]
    rw [mulVec_sum, PtRepPf.hJ_sum_right]
    simp only [mulVec_smul, PtRepPf.hJ_smul_right]
  show hJ ε (F.wb i) (M *ᵥ x) = ∑ j, wm ε F.wb M i j * hJ ε (F.wb j) x
  rw [h2, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [PtRepPf.Fr.bv, PtRepPf.Fr.dv, Sum.elim_inl, Sum.elim_inr, he, hf, hz, F.we, F.wf, F.wz, mul_zero,
    Finset.sum_const_zero, zero_add, Fintype.sum_unique]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem wCoord_N (N : Matrix (Fin n) (Fin n) ℂ) (hN : InN ε F.e F.z N) {x : Fin n → ℂ}
    (hx : ∀ c, hJ ε (F.e c) x = 0) : wCoord ε F.wb (N *ᵥ x) = wCoord ε F.wb x := by
  funext i
  show hJ ε (F.wb i) (N *ᵥ x) = hJ ε (F.wb i) x
  have e1 : N *ᵥ x = x + (N - 1) *ᵥ x := by rw [sub_mulVec, one_mulVec]; abel
  have h0 : hJ ε (F.wb i) ((N - 1) *ᵥ x) = 0 := by
    refine hJ_span_zero (F.wb i) (fun y hy => ?_) (hN.2 x hx)
    obtain ⟨c, -, rfl⟩ := hy
    exact F.we i c
  rw [e1, PtRepPf.hJ_add_right, h0, add_zero]

theorem perp_fix (g : Formalism.REAL.UJ ε) (he : ∀ c, uMat g *ᵥ F.e c = F.e c) {x : Fin n → ℂ}
    (hx : ∀ c, hJ ε (F.e c) x = 0) (c : Fin r) : hJ ε (F.e c) (uMat g *ᵥ x) = 0 := by
  rw [← he c, PtRepPf.hJ_UJ, hx]

theorem wm_unitary (g : Formalism.REAL.UJ ε) (he : ∀ c, uMat g *ᵥ F.e c = F.e c) (hz : uMat g *ᵥ F.z = F.z) :
    wm ε F.wb (uMat g) ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext j l
  have hzw : ∀ m, hJ ε F.z (uMat g *ᵥ F.wb m) = 0 := fun m => by rw [← hz, PtRepPf.hJ_UJ, F.zw]
  have hew : ∀ m c, hJ ε (F.e c) (uMat g *ᵥ F.wb m) = 0 := fun m c => by rw [← he c, PtRepPf.hJ_UJ, F.ew]
  have hp := F.pair (uMat g *ᵥ F.wb j) (uMat g *ᵥ F.wb l) (hew j) (hew l)
  simp only [hzw, mul_zero, zero_mul, star_zero, zero_add] at hp
  rw [PtRepPf.hJ_UJ, F.ww] at hp
  rw [Matrix.mul_apply, Matrix.one_apply, hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.star_apply, wm]
  ring

theorem wm_mul (A H : Matrix (Fin n) (Fin n) ℂ) (he : ∀ c, A *ᵥ F.e c = F.e c) (hf : ∀ c, A *ᵥ F.fd c = F.fd c)
    (hz : A *ᵥ F.z = F.z) : wm ε F.wb (A * H) = wm ε F.wb A * wm ε F.wb H := by
  ext i j
  have h1 := congrFun (wCoord_fix F A he hf hz (H *ᵥ F.wb j)) i
  calc wm ε F.wb (A * H) i j = wCoord ε F.wb (A *ᵥ (H *ᵥ F.wb j)) i := by
        simp only [wm, wCoord, mulVec_mulVec]
    _ = _ := h1
    _ = (wm ε F.wb A * wm ε F.wb H) i j := by
        simp only [mulVec, dotProduct, Matrix.mul_apply, wm, wCoord]

end Fr

theorem move_loc (A B : PtRepPf.Fr ε r k) (i0 i0' : Fin k) (γ nn a nn' a' : Formalism.REAL.UJ ε)
    (hn : InN ε A.e A.z (uMat nn)) (hn' : InN ε B.e B.z (uMat nn'))
    (hae : ∀ c, uMat a *ᵥ A.e c = A.e c) (haf : ∀ c, uMat a *ᵥ A.fd c = A.fd c) (haz : uMat a *ᵥ A.z = A.z)
    (hae' : ∀ c, uMat a' *ᵥ B.e c = B.e c) (haf' : ∀ c, uMat a' *ᵥ B.fd c = B.fd c)
    (haz' : uMat a' *ᵥ B.z = B.z) (H H' : Matrix (Fin k) (Fin k) ℂ)
    (hD : IsDFrame ε (fam A.e A.z) (fam B.e B.z) (uMat γ) (uMat γ⁻¹) A.wb B.wb i0 i0' H H') :
    IsDFrame ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))
      (uMat ((nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹)) A.wb B.wb i0 i0' (wm ε A.wb (uMat a) * H)
      (wm ε B.wb (uMat a') * H') := by
  obtain ⟨hH, hH', hN1, hN2, hU0⟩ := hD
  have haF : ∀ b, uMat a *ᵥ fam A.e A.z b = fam A.e A.z b := fam_fix hae haz
  have haF' : ∀ b, uMat a' *ᵥ fam B.e B.z b = fam B.e B.z b := fam_fix hae' haz'
  have haiF : ∀ b, uMat a⁻¹ *ᵥ fam A.e A.z b = fam A.e A.z b := fun b => fix_inv a (haF b)
  have haiF' : ∀ b, uMat a'⁻¹ *ᵥ fam B.e B.z b = fam B.e B.z b := fun b => fix_inv a' (haF' b)
  obtain ⟨Q, hQt, hQd, hQ⟩ := tri A.e A.z (uMat nn⁻¹)
    (Formalism.L2.SG.RealObj.SpanPreservation.inN_inv ε A.e A.z (uMat nn) (uMat nn⁻¹) (uMat_inv_mul_ nn) hn).1
  obtain ⟨Q', hQt', hQd', hQ'⟩ := tri B.e B.z (uMat nn'⁻¹)
    (Formalism.L2.SG.RealObj.SpanPreservation.inN_inv ε B.e B.z (uMat nn') (uMat nn'⁻¹) (uMat_inv_mul_ nn') hn').1
  obtain ⟨Qn, -, -, hQn⟩ := tri A.e A.z (uMat nn) hn.1
  obtain ⟨Qn', -, -, hQn'⟩ := tri B.e B.z (uMat nn') hn'.1
  have hWa := wm_unitary A a hae haz
  have hWa' := wm_unitary B a' hae' haz'

  have hG2f : ∀ b, uMat (nn * a * γ * a'⁻¹ * nn'⁻¹) *ᵥ fam B.e B.z b =
      uMat nn *ᵥ (uMat a *ᵥ ∑ c, Q' c b • (uMat γ *ᵥ fam B.e B.z c)) := fun b => by
    simp only [uMat_mul_, ← mulVec_mulVec, hQ', mulVec_sum, mulVec_smul, haiF']
  have hZ2 : Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)) =
      Qᴴ * Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ) * Q' := by
    ext i j
    show hJ ε (fam A.e A.z i) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹) *ᵥ fam B.e B.z j) = _
    rw [hG2f, pair_na A.e A.z nn a Q hQ haF]
    simp only [PtRepPf.hJ_sum_right, PtRepPf.hJ_smul_right, Matrix.mul_apply, conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
      simp only [Formalism.L2.SG.RealObj.Zhat]; ring
  obtain ⟨hcol, hrow, hdetZ⟩ := tri_adj (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) Q Q' hQt hQd hQt' hQd'
  have hdet : Formalism.L2.SG.RealObj.Dl (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))) (r + 1) =
      Formalism.L2.SG.RealObj.Dl (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (r + 1) := by
    rw [Dl_full, Dl_full, hZ2, hdetZ]

  have hxPr : xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)))
      (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)) (fam B.e B.z) =
      uMat nn *ᵥ (uMat a *ᵥ xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (uMat γ) (fam B.e B.z)) :=
    xPr_move _ _ Q' _ _ _ _ _ hG2f (by rw [hZ2]; exact hcol)
  have hwc1 : wCoord ε A.wb (xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)))
      (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹)) (fam B.e B.z)) =
      wm ε A.wb (uMat a) *ᵥ wCoord ε A.wb (xPr (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (uMat γ) (fam B.e B.z)) := by
    rw [hxPr, wCoord_N A _ hn (perp_fix A a hae (fun c => xPr_perp A.e A.z _ _ c)), wCoord_fix A _ hae haf haz]

  have hg2inv : (nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹ = nn' * a' * γ⁻¹ * a⁻¹ * nn⁻¹ := by group
  have hinv : ∀ x, uMat ((nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹) *ᵥ x =
      uMat nn' *ᵥ (uMat a' *ᵥ (uMat γ⁻¹ *ᵥ (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ x)))) := fun x => by
    rw [hg2inv]
    simp only [uMat_mul_, ← mulVec_mulVec]
  have hxUn : uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ
      xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))) (fam A.e A.z)) =
      xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (fam A.e A.z) :=
    xUn_move _ _ Q _ _ _ hQ haiF (by rw [hZ2]; exact hrow)
  have hwc2 : wCoord ε B.wb (uMat ((nn * a * γ * a'⁻¹ * nn'⁻¹)⁻¹) *ᵥ
      xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat (nn * a * γ * a'⁻¹ * nn'⁻¹))) (fam A.e A.z)) =
      wm ε B.wb (uMat a') *ᵥ wCoord ε B.wb (uMat γ⁻¹ *ᵥ xUn (Zhat ε (fam A.e A.z) (fam B.e B.z) (uMat γ)) (fam A.e A.z)) := by
    rw [hinv, hxUn, wCoord_N B _ hn' (perp_fix B a' hae' (fun c => xUn_perp _ B.e B.z γ c)),
      wCoord_fix B _ hae' haf' haz']

  have hgrp : nn * a * γ * a'⁻¹ * nn'⁻¹ * nn' * a' = nn * a * γ := by group
  have hmv : ∀ v, uMat (nn * a * γ * a'⁻¹ * nn'⁻¹) *ᵥ (uMat nn' *ᵥ (uMat a' *ᵥ v)) =
      uMat nn *ᵥ (uMat a *ᵥ (uMat γ *ᵥ v)) := fun v => by
    have h := congrArg (fun g => uMat g *ᵥ v) hgrp
    simp only [uMat_mul_, ← mulVec_mulVec] at h ⊢
    exact h
  refine ⟨(Matrix.unitaryGroup (Fin k) ℂ).mul_mem hWa hH, (Matrix.unitaryGroup (Fin k) ℂ).mul_mem hWa' hH', ?_, ?_, ?_⟩
  · rw [hdet, hwc1, ← mulVec_smul, eN_unitary _ hWa, ← mulVec_smul, ← mulVec_mulVec, hN1]
  · rw [hdet, hwc2, ← mulVec_smul, eN_unitary _ hWa', ← mulVec_smul, ← mulVec_mulVec, hN2]
  · intro y hya hyb
    have hy0a : ∀ c, hJ ε (fam A.e A.z c) (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y)) = 0 := by
      intro c
      rw [hJ_adj, inv_inv, haF c, hJ_adj, inv_inv, hQn c, PtRepPf.hJ_sum_left]
      exact Finset.sum_eq_zero fun d _ => by rw [PtRepPf.hJ_smul_left, hya d, mul_zero]
    have hy0b : ∀ b, hJ ε (uMat γ *ᵥ fam B.e B.z b) (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y)) = 0 := by
      intro b
      rw [hJ_adj, inv_inv, hJ_adj, inv_inv, ← hmv, haF' b, hQn' b, mulVec_sum, PtRepPf.hJ_sum_left]
      exact Finset.sum_eq_zero fun c _ => by rw [mulVec_smul, PtRepPf.hJ_smul_left, hyb c, mul_zero]
    have hperp0 : ∀ c, hJ ε (B.e c) (uMat γ⁻¹ *ᵥ (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y))) = 0 := fun c => by
      rw [hJ_adj, inv_inv, ← PtRepPf.fam_cs B.e B.z c]
      exact hy0b _
    have hperpA : ∀ c, hJ ε (A.e c) (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y)) = 0 := fun c => by
      rw [← PtRepPf.fam_cs A.e A.z c]
      exact hy0a _
    have hyy : y = uMat nn *ᵥ (uMat a *ᵥ (uMat a⁻¹ *ᵥ (uMat nn⁻¹ *ᵥ y))) := by
      rw [cancel_ a, cancel_ nn]
    have hWW : ∀ v, star (wm ε B.wb (uMat a')) *ᵥ (wm ε B.wb (uMat a') *ᵥ v) = v := fun v => by
      rw [mulVec_mulVec, (Matrix.mem_unitaryGroup_iff').1 hWa', one_mulVec]
    conv_rhs => rw [hyy]
    rw [wCoord_N A _ hn (perp_fix A a hae hperpA), wCoord_fix A _ hae haf haz, hinv,
      wCoord_N B _ hn' (perp_fix B a' hae' hperp0), wCoord_fix B _ hae' haf' haz', star_mul,
      ← mulVec_mulVec, ← mulVec_mulVec, hWW, hU0 _ hy0a hy0b]

end ClassFrameUnitaryMoves

open ClassFrameUnitaryMoves

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem dFrameMoveHC_holds (u u' : D.what₂.Word) (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) :
    DFrameMoveHC X u u' i0 i0' := by
  intro γ h h' n a n' a' hD hn ha hn' ha'
  unfold Formalism.L2.SG.RealObj.IsDFrameX at hD ⊢
  have hmulH : ∀ w {p q : X.B.I.Ginf}, p ∈ HsetU X w → q ∈ HsetU X w → p * q ∈ HsetU X w := by
    intro w p q hp hq v x hx
    show uMat (p v * q v) *ᵥ rv X.B.I v x = rv X.B.I v x
    rw [uMat_mul_, ← mulVec_mulVec, hq v x hx, hp v x hx]
  refine ⟨hmulH u ha hD.1, hmulH u' ha' hD.2.1, fun v => ?_⟩
  have hfx : ∀ w (p : X.B.I.Ginf), p ∈ HsetU X w →
      (∀ c, uMat (p v) *ᵥ rv X.B.I v (X.eR c) = rv X.B.I v (X.eR c)) ∧
      (∀ c, uMat (p v) *ᵥ rv X.B.I v (X.fR c) = rv X.B.I v (X.fR c)) ∧
      uMat (p v) *ᵥ rv X.B.I v (X.zR w) = rv X.B.I v (X.zR w) := fun w p hp =>
    ⟨fun c => hp v _ (Or.inl (Or.inl ⟨c, rfl⟩)), fun c => hp v _ (Or.inl (Or.inr ⟨c, rfl⟩)), hp v _ (Or.inr rfl)⟩
  obtain ⟨hae, haf, haz⟩ := hfx u a ha
  obtain ⟨hae', haf', haz'⟩ := hfx u' a' ha'
  have hfrm : ∀ w, frm X w 1 v = fam (fun c => rv X.B.I v (X.eR c)) (rv X.B.I v (X.zR w)) := fun w => by
    funext b
    simp [frm, famSc]
  have hmat : ∀ w (p q : X.B.I.Ginf), p ∈ HsetU X w →
      matW X.B.I (X.wfr w v) v (p * q) = wm (X.B.I.ε v) (X.wfr w v) (uMat (p v)) * matW X.B.I (X.wfr w v) v q :=
    fun w p q hp => by
      obtain ⟨he, hf, hz⟩ := hfx w p hp
      exact wm_mul (PtRepPf.frU X w v) (uMat (p v)) (uMat (q v)) he hf hz
  rw [hmat u a h ha, hmat u' a' h' ha', hfrm u, hfrm u']
  have h0 := hD.2.2 v
  rw [hfrm u, hfrm u'] at h0
  exact move_loc (PtRepPf.frU X u v) (PtRepPf.frU X u' v) (i0 v) (i0' v) (γ v) (n v) (a v) (n' v) (a' v)
    (hn v) (hn' v) hae haf haz hae' haf' haz' _ _ h0

end Formalism.L2.SG.Pf.RowForm
end
end

noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem classFrameAll_comp {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (P G K : V →L[ℂ] V) (G' H' K' : V' →L[ℂ] V') (T : V' →L[ℂ] V)
    (a : ℂ) (hK : K = P * G) (hK' : K' = G' * H') :
    P.comp ((a • G.comp (T.comp G')).comp H') = a • K.comp (T.comp K') := by
  subst hK hK'
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, map_smul]

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (Y : Formalism.L2.SG.Full.Full X)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (sd C Th : ℝ)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' (X.Fu u) (Y.what₂ u))
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def VIndepAtC (sc : ℝ) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) →
    (∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (Formalism.L2.SG.RealObj.gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h₁ h₁' →
      Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
            (Formalism.L2.SG.RealObj.gamW X u u' w)).comp (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
            (Formalism.L2.SG.RealObj.gamW X u u' w)).comp (X.piU u' h₂'))

theorem classFrameAll_pi_inv (w : D.what₂.Word) {k g h : X.B.I.Ginf} (hk : k ∈ X.SinfU w) (hg : g ∈ X.SinfU w)
    (hh : h ∈ X.SinfU w) (e : X.piU w k = X.piU w g⁻¹ * X.piU w h) :
    X.piU w k⁻¹ = X.piU w h⁻¹ * X.piU w g := by
  have rep := X.piU_rep w
  have hki := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hk
  have hgi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hg
  have hhi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X w hh
  have e1 : X.piU w k * (X.piU w h⁻¹ * X.piU w g) = 1 := by
    rw [e, mul_assoc, ← mul_assoc (X.piU w h), ← rep.2.1 h hh h⁻¹ hhi, mul_inv_cancel, rep.1, one_mul,
      ← rep.2.1 g⁻¹ hgi g hg, inv_mul_cancel, rep.1]
  calc X.piU w k⁻¹ = X.piU w k⁻¹ * (X.piU w k * (X.piU w h⁻¹ * X.piU w g)) := by rw [e1, mul_one]
    _ = X.piU w h⁻¹ * X.piU w g := by rw [← mul_assoc, ← rep.2.1 k⁻¹ hki k hk, inv_mul_cancel, rep.1, one_mul]

theorem classFrameAll_pull (γ g g' h h' : X.B.I.Ginf) (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hD : Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' (g * γ * g'⁻¹) h h') :
    ∃ k k', Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0' γ k k' ∧
      X.piU u k⁻¹ = X.piU u h⁻¹ * X.piU u g ∧ X.piU u' k' = X.piU u' g'⁻¹ * X.piU u' h' := by
  have hgi := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u hg
  have hgi' := Formalism.L2.SG.RealObj.InfCut.sinfU_inv X u' hg'
  obtain ⟨n, hn, a, ha, e⟩ := sDecompC_holds X u g⁻¹ hgi
  obtain ⟨n', hn', a', ha', e'⟩ := sDecompC_holds X u' g'⁻¹ hgi'
  have hM := dFrameMoveHC_holds X u u' i0 i0' _ h h' n a n' a' hD hn ha hn' ha'
  have eγ : n * a * (g * γ * g'⁻¹) * a'⁻¹ * n'⁻¹ = γ := by
    have e0 : n * a * (g * γ * g'⁻¹) * a'⁻¹ * n'⁻¹ = n * a * (g * γ * g'⁻¹) * (n' * a')⁻¹ := by group
    rw [e0, ← e, ← e']
    group
  rw [eγ] at hM
  have hh := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hD.1
  have hh' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hD.2.1
  have hk := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hM.1
  have p1 : X.piU u (a * h) = X.piU u g⁻¹ * X.piU u h := by
    rw [ClassFrameLeviDecomposition.pi_levi X u hn ha hh, ← e]
    rfl
  have p2 : X.piU u' (a' * h') = X.piU u' g'⁻¹ * X.piU u' h' := by
    rw [ClassFrameLeviDecomposition.pi_levi X u' hn' ha' hh', ← e']
    rfl
  exact ⟨a * h, a' * h', hM, classFrameAll_pi_inv X u hk hg hh p1, p2⟩

theorem vIndepLiftC_of_at (h3 : LiftDecompC X Y u u' κ) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (hVA : VIndepAtC X u u' i0 i0' νq 1) :
    VIndepLiftC X Y u u' i0 i0' κ := by
  intro R ρ s hrel h₁ h₁' h₂ h₂' hD₁ hD₂
  obtain ⟨hpt, g, hg, g', hg', hdec⟩ := h3 R ρ s hrel
  have hO : Formalism.L2.SG.TermOp.OOt s.1 =
      (((vR s.1.toTerm : ℝ) : ℂ) * (X.psiInfU u g * conj (X.psiInfU u' g'))) •
        (((Formalism.L2.SG.RealObj.InfCut.piIso X u g hg).toContinuousLinearEquiv : X.Vpi u →L[ℂ] X.Vpi u).comp
          ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
            Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))) Set.univ
              (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
            ((Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg').symm.toContinuousLinearEquiv : X.Vpi u' →L[ℂ] X.Vpi u'))) := by
    rw [h5 R ρ s hrel g hg g' hg' hdec, ← smul_smul]
    congr 1
    rw [hdec]
    exact ClassFrameNormal.oo_map_mulLeft _ _ _ _ g g' _ _ _ _
      (fun x => (X.Wu_spec u).1 g hg x) (fun x => (X.Wu_spec u').1 g' hg' x)
  rw [Formalism.L2.SG.RealObj.InfCut.piIso_coe, Formalism.L2.SG.RealObj.InfCut.piIso_symm] at hO
  rw [hdec] at hD₁ hD₂
  obtain ⟨k₁, k₁', hK₁, e₁, e₁'⟩ := classFrameAll_pull X u u' i0 i0' _ g g' h₁ h₁' hg hg' hD₁
  obtain ⟨k₂, k₂', hK₂, e₂, e₂'⟩ := classFrameAll_pull X u u' i0 i0' _ g g' h₂ h₂' hg hg' hD₂
  have hV := hVA _ hpt (h4' R ρ s hrel) k₁ k₁' k₂ k₂' hK₁ hK₂
  unfold chiOO
  rw [hO, smul_smul, classFrameAll_comp _ _ _ _ _ _ _ _ e₁ e₁', classFrameAll_comp _ _ _ _ _ _ _ _ e₂ e₂', hV]

theorem normalFormC_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ :=
  normalFormC_of' X Y u u' vR i0 i0' νq κ (RealDecompL.liftAtSomeC_of X Y u u' κ hAtS) hCU
    (decompPhaseC_of X Y u u' κ (RealDecompL.liftDecompC_of_atSome X Y u u' κ hAtS) hPT) hDF
    (RealDecompL.liftGPosC_of X Y u u' κ hAtS hTP) hFT

theorem commonFrameC_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ)
    (hVA : VIndepAtC X u u' i0 i0' νq 1) (hSc : ScalTC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ)
    (hAt : AtPtRelevantC X Y u u') :
    CommonFrameC X Y u u' vR i0 i0' νq κ := by
  have hLD := RealDecompL.liftDecompC_of_atSome X Y u u' κ hAtS
  have hGP := RealDecompL.liftGPosC_of X Y u u' κ hAtS hTP
  have hP : PtValueC X Y u u' vR i0 i0' νq κ :=
    ptValueC_of X Y u u' vR i0 i0' νq κ (RealDecompL.liftAtSomeC_of X Y u u' κ hAtS) hCU
      (decompPhaseC_of X Y u u' κ hLD hPT) hDF hGP hFT
      (dFrameMoveC_of X u u' i0 i0' (sDecompC_holds X u) (sDecompC_holds X u') (dFrameMoveHC_holds X u u' i0 i0'))
  exact commonFrameC_of X Y u u' vR i0 i0' νq κ hP (vIndepLiftC_of_at X Y u u' vR i0 i0' νq κ hLD hGP hFT hVA)
    (commonDFrameC_of_exact X Y u u' vR i0 i0' νq κ (commonDFrameExactC_of X Y u u' vR i0 i0' νq κ hP
      (pairDFrameC_of X Y u u' i0 i0' κ (scalarAgreeC_of_scalT X Y u u' κ hSc))))
    (irrelZeroC_of X Y u u' vR i0 i0' νq κ hV hAt)

theorem classFrameOO_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ)
    (hVA : VIndepAtC X u u' i0 i0' νq 1) (hSc : ScalTC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ)
    (hAt : AtPtRelevantC X Y u u') :
    ClassFrameOO X Y u u' vR i0 i0' νq κ :=
  Formalism.L2.SG.Pf.classFrameOO_of X Y u u' vR i0 i0' νq κ
    (normalFormC_all X Y u u' vR i0 i0' νq κ hAtS hTP hCU hDF hPT hFT)
    (commonFrameC_all X Y u u' vR i0 i0' νq κ hAtS hTP hCU hDF hPT hFT hVA hSc hV hAt) hV hAt

theorem classFrameC_all
    (hAtS : ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), t.G ≠ 0 → t.relevant → ∃ w, t.atPt w)
    (hTP : ∀ (t : Term D u u' (X.Fu u) (Y.what₂ u)) (w : Point D.host.E (D.R.rS + 1)), t.atPt w →
      TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w))
    (hCU : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (hDF : DFrameAtS X u u' i0 i0' 1) (hPT : PhaseTieC X Y u u' κ) (hFT : FormTranspC X Y u u' vR νq κ)
    (hVA : VIndepAtC X u u' i0 i0' νq 1) (hSc : ScalTC X Y u u' κ) (hV : LemmaVLiftC X Y u u' κ)
    (hAt : AtPtRelevantC X Y u u') (hVol : 0 < X.volK2)
    (hc : 0 ≤ (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0 *
      (bCF X hb Y.hK (Y.FN u) (Y.FN u') u u' X0 ψ (Y.tO u u') sd C Th vR Q M δ i0 i0' νq).c0') :
    ClassFrameC X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ :=
  classFrameC_of_OO X hb Y u u' X0 ψ sd C Th vR Q M δ i0 i0' νq κ
    (classFrameOO_all X Y u u' vR i0 i0' νq κ hAtS hTP hCU hDF hPT hFT hVA hSc hV hAt) hVol hc

end Formalism.L2.SG.Pf.RowForm
