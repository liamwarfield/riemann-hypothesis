module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsColLatRepS
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormHSBlocks

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInst

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tauU {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : X.Vpi u →L[ℂ] X.Vpi u :=
  X.psiInfU u s • X.piU u s

def StepSchurG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D),
    IsUnitRep X.B.σs ∧ IsSchur (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) ∧ ‖X.B.tens X.B.w‖ = 1 ∧
      ∀ y : X.B.I.Ginf, (Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y) =
        ((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ

def StepSubG : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsHaarSub (X.SinfU u) (muS X u) ∧ IsFolner (X.SinfU u) (muS X u) ∧
      tauU X u 1 = 1 ∧ (∀ s ∈ X.SinfU u, ∀ t ∈ X.SinfU u, tauU X u (s * t) = tauU X u s * tauU X u t) ∧
      SFinite (X.nuQ u)

def StepSection : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∃ h : Cinf X → X.B.I.Ginf, Measurable h ∧ ∀ c ∈ Good X u u', HasDiag X u u' sc c (h c)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem tauU_unit (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) (a b : X.Vpi u) :
    ⟪tauU X u s a, tauU X u s b⟫_ℂ = ⟪a, b⟫_ℂ := by
  simp only [tauU, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, (X.piU_rep u).2.2.1 s hs]
  rw [← mul_assoc, Complex.mul_conj', Formalism.L2.SG.RealObj.InfCut.norm_psiInfU]
  simp

theorem isWAbs_of (hS : StepSchurG) (hG : StepSubG) (u : D.what₂.Word) :
    IsWAbs (Formalism.L2.SG.ProjRows.muInf X.B.I) X.B.σs (degX X) (X.B.tens X.B.w) (X.SinfU u) (tauU X u)
      (X.nuQ u) (X.Wu u) := by
  obtain ⟨-, -, -, hph⟩ := hS D X
  obtain ⟨-, -, h1, hmul, -⟩ := hG D X u
  have hW := X.Wu_spec u
  refine ⟨h1, hmul, fun s hs a b => tauU_unit X u s hs a b, fun s hs x => ?_, hW.2.2.1, fun x => ?_,
    hW.2.2.2.1, hW.2.2.2.2⟩
  · rw [hW.1 s hs x]; rfl
  · obtain ⟨hi, he⟩ := hW.2.1 x
    have e : (fun y => (((degX X : ℝ) : ℂ) * conj ⟪X.B.tens X.B.w, X.B.σs y (X.B.tens X.B.w)⟫_ℂ) • X.Wu u (x * y)) =
        fun y => Formalism.L2.SG.ProjRows.phInf X.B.I X.B.σ X.B.w X.dv y • X.Wu u (x * y) :=
      funext fun y => by rw [hph y]
    rw [e]
    exact ⟨hi, he⟩

theorem inner_transfer (hG : StepSubG) (u u' : D.what₂.Word) (φ : X.B.I.Ginf → ℝ≥0∞) (hφ : Measurable φ)
    (γ γ' : X.B.I.Ginf) (a : X.B.I.Ginf) (ha : a ∈ X.SinfU u) (b : X.B.I.Ginf) (hb : b ∈ X.SinfU u')
    (hγ : γ' = a * γ * b⁻¹) :
    ∫⁻ s, ∫⁻ s', φ (s * γ' * s'⁻¹) ∂(muS X u') ∂(muS X u) = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂(muS X u') ∂(muS X u) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hR, -⟩ := (hG D X u).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hR', -⟩ := (hG D X u').1
  subst hγ
  have hin : ∀ s, ∫⁻ s', φ (s * (a * γ * b⁻¹) * s'⁻¹) ∂(muS X u') = ∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u') := by
    intro s
    have e : ∀ s', s * (a * γ * b⁻¹) * s'⁻¹ = s * a * γ * (MeasurableEquiv.mulRight b s')⁻¹ := by
      intro s'
      simp only [MeasurableEquiv.coe_mulRight]
      group
    simp_rw [e]
    rw [← lintegral_map_equiv (fun t => φ (s * a * γ * t⁻¹)) (MeasurableEquiv.mulRight b),
      MeasurableEquiv.coe_mulRight, hR' b hb]
  simp_rw [hin]
  have e2 : ∀ s, (∫⁻ s', φ (s * a * γ * s'⁻¹) ∂(muS X u')) =
      (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a s) := by
    intro s
    simp only [MeasurableEquiv.coe_mulRight]
  simp_rw [e2]
  rw [← lintegral_map_equiv (fun t => ∫⁻ s', φ (t * γ * s'⁻¹) ∂(muS X u')) (MeasurableEquiv.mulRight a),
    MeasurableEquiv.coe_mulRight, hR a ha]

end Formalism.L2.SG.RealObj.EnergyInst
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormClosed
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormExpSatC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    NormExpSat (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def SatGramC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').genSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) ∧
      SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').ngSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u'))

def ChiNBiC : Prop := ∀ (D : D7) (X : HidaSetting D), ChiNBi X

def NeatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK

def LeviOntoC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.Pf.NormSteps.LeviOntoS Y.TR (Y.cs u)

theorem colLatRepC (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.NormSteps.ColLatRepS (Y.cs u) Y.hK :=
  Formalism.L2.SG.Pf.NormSteps.column_lattice_representatives (Y.cs u) Y.hK (Y.rowsOK u)

def MassAC : Prop := ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), MassA Y.TR (X.Fu u) (Y.cs u)

theorem normExpSatC'_of (hCL : NeatC) (hO : LeviOntoC) (hM : MassAC) (hS : SatGramC') : NormExpSatC' := by
  intro D X Y u u' _ _ _ hAbs
  obtain ⟨hSg, hSn⟩ := hS D X Y u u' ‹_› ‹_› ‹_›
  have hTF := Full.frameTie (X := X) u u'
  have hF := colFree_steps (TR := Y.TR) (F0 := X.Fu u) (cs := Y.cs u) (hK := Y.hK) (hR := Y.colReps u)
    (hCL := hCL D X Y u) (hO := hO D X Y u) (hRep := colLatRepC D X Y u) (hMass := hM D X Y u)
  have hF' := colFree_steps (TR := Y.TR) (F0 := X.Fu u') (cs := Y.cs u') (hK := Y.hK) (hR := Y.colReps u')
    (hCL := hCL D X Y u') (hO := hO D X Y u') (hRep := colLatRepC D X Y u') (hMass := hM D X Y u')
  exact normExpSat_of (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (FdN := Y.FN u) (FdN' := Y.FN u')
    (hHS := hilbert_schmidt_blocks) (hGam := Formalism.L2.SG.NormCut.gamma_product_sum_holds)
    (hPsi := Formalism.L2.SG.NormCut.psi_natural_equiv_holds) (hAbs := hAbs)
    (hChi := chiNIndep_of_frameTie (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (sc := scOf Y.TR (Y.cs u)) (sc' := scOf Y.TR (Y.cs u'))
    (hPh := colPhase_holds (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (A := Aset Y.TR (Y.cs u)) (A' := Aset Y.TR (Y.cs u')) (hF := hF) (hF' := hF') (hSg := hSg) (hSn := hSn)

end Formalism.L2.SG.NormCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightInvOfModular
noncomputable section

open MeasureTheory Topology Filter Matrix
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem inS_pres {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : ℕ) :
    ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
  intro y hy
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : ℕ) < a := hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    have e1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨b, hb', rfl⟩) ?_
    refine Submodule.span_mono ?_ (hg.1 b)
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_trans hc hb', rfl⟩
  exact hle hy

theorem inS_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) : InS e z (g * h) := by
  have key : ∀ v : Fin n → ℂ, (g * h - 1) *ᵥ v = g *ᵥ ((h - 1) *ᵥ v) + (g - 1) *ᵥ v := fun v => by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg r _ hh.2) hg.2

theorem inS_one : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _,
    by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _⟩

def SG : Subgroup (Formalism.REAL.UJ ε) where
  carrier := SLoc ε e z
  one_mem' := inS_one e z
  mul_mem' {a b} ha hb := inS_mul e z ha hb
  inv_mem' {a} ha := Formalism.L2.SG.RealObj.InfCut.inS_inv _ _ (Formalism.MainNotions.S.uMat a) (Formalism.MainNotions.S.uMat a⁻¹)
    (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' a) ha

theorem coe_SG : (SG ε e z : Set (Formalism.REAL.UJ ε)) = SLoc ε e z := rfl

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  ((Formalism.REAL.uJEmb n ε).1).continuous

theorem SG_closed : IsClosed (SG ε e z : Set (Formalism.REAL.UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (SG ε e z : Set (Formalism.REAL.UJ ε)) =
      (⋂ a : Fin r, (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ e a) ⁻¹' (spanLt e a.1 : Set (Fin n → ℂ))) ∩
        (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ z) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_SG, SLoc, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
  rw [e1]
  exact (isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional _).preimage (hc _)).inter
    ((Submodule.closed_of_finiteDimensional _).preimage (hc _))

section Sub

variable {ε e z}

end Sub

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacLocOfHpk
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BigCellDiagIff
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem dl_diagonal {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (h : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE h i) := by
  unfold Dl
  simp only [dif_pos h, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective h), Matrix.det_diagonal,
    Function.comp_apply]

theorem dcLoc_eq (r : ℕ) : dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  haveI : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by rw [two_smul]; infer_instance
  unfold dcLoc
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def JacEx : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def GoodPos {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) : Prop :=
  ∃ f : Fin r → Fin n → ℂ, (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
    ∀ a, hJ ε (f a) z = 0 ∧ hJ ε (f a) z' = 0

def JacExGood : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def HpkEx : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ μ μW μW' μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μ →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z') μW' →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec →
    ∃ K : ℝ, 0 < K ∧ ∀ φ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ x, φ x ∂μ = ENNReal.ofReal K * ∫⁻ q : (Fin r → ℂ) × ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r (Formalism.QuantumDeterminants.Tz k r z) (Formalism.QuantumDeterminants.Tz k r z') q) *
          ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * (Matrix.of s')⁻¹) i j)
            ∂(Formalism.MainNotions.S.muS μW' μN) ∂(Formalism.MainNotions.S.muS μW μN)

def TransEx : Prop := HpkEx → RightInvS → JacExGood

def DegRed : Prop := RightInvS → JacExGood → JacEx

theorem jacLoc_of_ex (h1 : DiagDCLoc) (hR : RightInvS) (hE : JacEx) : JacLoc := by
  intro n r k ε e z z' T T' sc hF hsc μS μS' hμ hμ' h hh
  obtain ⟨h0, hh0, hD⟩ := hE n r k ε e z z' T T' sc hF hsc
  obtain ⟨C, hC, hDC⟩ := hD μS μS' hμ hμ'
  have hF' : FrameLoc ε k e z' z T' T :=
    ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩
  refine ⟨C, hC, fun φ hφ => ?_⟩
  rw [hDC φ hφ]
  refine setLIntegral_congr_fun (measurableSet_goodLoc r T T') ?_
  intro c hc
  obtain ⟨s₁, hs₁, s₁', hs₁', hcs⟩ :=
    h1 n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  beta_reduce
  congr 1
  rw [hcs]
  symm
  have eS := hR n r k ε e z z' T T' hF μS hμ s₁ hs₁
  have eS' := hR n r k ε e z' z T' T hF' μS' hμ' s₁' hs₁'
  have hmap : ∀ (a : Formalism.REAL.UJ ε) (ν : Measure (Formalism.REAL.UJ ε)),
      ν.map (fun x => x * a) = ν → ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, ∫⁻ x, F (x * a) ∂ν = ∫⁻ x, F x ∂ν := by
    intro a ν hν F
    have := lintegral_map_equiv F (MeasurableEquiv.mulRight a) (μ := ν)
    rw [show ⇑(MeasurableEquiv.mulRight a) = (fun x => x * a) from rfl, hν] at this
    exact this.symm
  calc ∫⁻ s, ∫⁻ s', φ (s * (s₁ * h0 c * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS
      = ∫⁻ s, ∫⁻ s', φ ((s * s₁) * h0 c * (s' * s₁')⁻¹) ∂μS' ∂μS := by
        simp only [_root_.mul_inv_rev, mul_assoc]
    _ = ∫⁻ s, ∫⁻ s', φ (s * h0 c * (s' * s₁')⁻¹) ∂μS' ∂μS :=
        hmap s₁ μS eS (fun s => ∫⁻ s', φ (s * h0 c * (s' * s₁')⁻¹) ∂μS')
    _ = ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹) ∂μS' ∂μS := by
        congr 1
        funext s
        exact hmap s₁' μS' eS' (fun s' => φ (s * h0 c * s'⁻¹))

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end
