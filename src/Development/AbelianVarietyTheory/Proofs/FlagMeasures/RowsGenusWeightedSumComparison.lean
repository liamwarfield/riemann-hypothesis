module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbSumFibreEquiv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowOfUnimodularLatticePrimitiveVector
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.StabilizerSymmMapsOrthogonal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizer
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

section Gen
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frF_Xa' (F : FlagG S r T) (hT : T ≠ 0) (k : ℕ) : (GlobalTheory.TypeAsm.frF F hT).Xa k = F.Xa k := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.Xa
  have h : (fun b : Fin r => (GlobalTheory.TypeAsm.frF F hT).e b.castSucc) = F.e := funext fun b => GlobalTheory.TypeAsm.fv_cast F b
  rw [h]

theorem frF_X' (F : FlagG S r T) (hT : T ≠ 0) : (GlobalTheory.TypeAsm.frF F hT).X = F.X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X
  rw [frF_Xa']
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x; simp

end Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_X : (GlobalTheory.TypeAsm.F0 X u).X = (X.Fu u).X := frF_X' _ _

theorem FuX_eq : (X.Fu u).X = Submodule.span D.host.E (Set.range X.eX) := by
  rw [FlagG.X, X.Fu_e]

theorem Wb_le (w : Wb X) : (w : (VS D).V) ∈ perpS (VS D) (X.Fu u).X := by
  intro y hy
  rw [FuX_eq] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact (w.2 a).1
  | zero => simp
  | add y v _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def iotaL : Wb X →ₗ[D.host.E] WbQ D (X.Fu u) :=
  (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.nX D (X.Fu u)).mkQ ∘ₗ
    Submodule.inclusion (fun v hv => Wb_le X u ⟨v, hv⟩)

theorem iotaL_apply (w : Wb X) :
    iotaL X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iotaL_bij : Function.Bijective (iotaL X u) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker, iotaL_apply, Submodule.Quotient.mk_eq_zero] at hw
    have hwX : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := by
      rw [← FuX_eq]; exact hw
    have h1 := Formalism.L2.SG.Pf.pj_X (f := X.fY) X.ee X.ef _ hwX
    rw [Formalism.L2.SG.Pf.pj_perp _ (fun a => w.2 a)] at h1
    exact Subtype.ext h1
  · intro q
    induction q using Submodule.Quotient.induction_on with | H a => ?_
    refine ⟨⟨Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V), fun b =>
      ⟨Formalism.L2.SG.Pf.hT_e_pj X.ee X.ef _ b, Formalism.L2.SG.Pf.hT_f_pj X.ff X.ef _ b⟩⟩, ?_⟩
    rw [iotaL_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    show Formalism.L2.SG.Pf.pj X.eX X.fY (a : (VS D).V) - (a : (VS D).V) ∈ (X.Fu u).X
    have h := Formalism.L2.SG.Pf.pj_sub_mem (e := X.eX) (f := X.fY) (a : (VS D).V)
      (fun b => a.2 _ (by rw [FuX_eq]; exact Submodule.subset_span ⟨b, rfl⟩))
    rw [← FuX_eq] at h
    exact h

def iota : Wb X ≃ₗ[D.host.E] WbQ D (X.Fu u) := LinearEquiv.ofBijective (iotaL X u) (iotaL_bij X u)

theorem iota_apply (w : Wb X) : iota X u w = Submodule.Quotient.mk ⟨(w : (VS D).V), Wb_le X u w⟩ := rfl

theorem iota_h (x y : Wb X) : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (iota X u x) (iota X u y) = hb X x y := rfl

theorem definiteInclusion_orthogonal_negativeVector : iota X u (zb X u) = PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u) := by
  rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar]
  congr 1
  apply Subtype.ext
  exact (X.flagZVector u).symm

theorem iota_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (w : Wb X) :
    iota X u w ∈ PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔ w ∈ Lmap X u Λ := by
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mem_Mof, mem_Lmap, fixedFrameOfWord_X]
  constructor
  · rintro ⟨a, haΛ, hmk⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk] at hmk
    refine Submodule.mem_sup.2 ⟨a, haΛ, (w : (VS D).V) - a, ?_, by abel⟩
    have := Submodule.neg_mem _ hmk
    rw [neg_sub] at this
    exact this
  · intro hw
    obtain ⟨l, hl, x, hx, hlx⟩ := Submodule.mem_sup.1 hw
    have hxX : x ∈ (X.Fu u).X := hx
    have hlp : l ∈ perpS (VS D) (X.Fu u).X := by
      have : l = (w : (VS D).V) - x := by rw [← hlx]; abel
      rw [this]
      exact Submodule.sub_mem _ (Wb_le X u w) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.X_le_perp D (X.Fu u) hxX)
    refine ⟨⟨l, hlp⟩, hl, ?_⟩
    rw [iota_apply, PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowMPf.mk_eq_mk]
    have : l - (w : (VS D).V) = -x := by rw [← hlx]; abel
    show l - (w : (VS D).V) ∈ _
    rw [this]
    exact Submodule.neg_mem _ hxX

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrbCard

open GlobalTheory.RowsOrb

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def conj (g : Wb X ≃ₗ[D.host.E] Wb X) : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u) :=
  (iota X u).symm.trans (g.trans (iota X u))

def unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : Wb X ≃ₗ[D.host.E] Wb X :=
  (iota X u).trans (σ.trans (iota X u).symm)

theorem conj_iota (g : Wb X ≃ₗ[D.host.E] Wb X) (w : Wb X) : conj X u g (iota X u w) = iota X u (g w) := by
  simp [conj]

theorem conj_unconj (σ : WbQ D (X.Fu u) ≃ₗ[D.host.E] WbQ D (X.Fu u)) : conj X u (unconj X u σ) = σ := by
  ext q; simp [conj, unconj]

theorem unconj_conj (g : Wb X ≃ₗ[D.host.E] Wb X) : unconj X u (conj X u g) = g := by
  ext w; simp [conj, unconj]

theorem conj_isom (g : Wb X ≃ₗ[D.host.E] Wb X) (hg : ∀ x y, hb X (g x) (g y) = hb X x y)
    (x y : WbQ D (X.Fu u)) :
    PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) (conj X u g x) (conj X u g y) =
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u) x y := by
  have e : ∀ q, conj X u g q = iota X u (g ((iota X u).symm q)) := fun q => rfl
  have e2 : ∀ q, iota X u ((iota X u).symm q) = q := fun q => (iota X u).apply_symm_apply q
  rw [e, e, iota_h, hg, ← iota_h, e2, e2]

theorem gmap_conj (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : Wb X ≃ₗ[D.host.E] Wb X) :
    Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) =
              PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ ↔
      Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) = Lmap X u Λ := by
  have key : ∀ w, iota X u w ∈ Formalism.HermitianLatticesTheory.gmap (conj X u g) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) ↔
      w ∈ Formalism.HermitianLatticesTheory.gmap g (Lmap X u Λ) := by
    intro w
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨(iota X u).symm y, (iota_mem X u Λ _).1 (by simpa using hy), ?_⟩
      apply (iota X u).injective
      rw [← h, ← conj_iota]
      simp
    · rintro ⟨y, hy, h⟩
      refine ⟨iota X u y, (iota_mem X u Λ y).2 hy, ?_⟩
      rw [conj_iota, h]
  constructor
  · intro h
    ext w
    rw [← key, h, iota_mem]
  · intro h
    ext q
    rw [← (iota X u).apply_symm_apply q, key, h, iota_mem]

theorem conj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V) (g : MulAction.stabilizer (Gz X u) (Lmap X u Λ)) :
    conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) ∈
      PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ) := by
  have hz : (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u) = zb X u :=
    MulAction.mem_stabilizer_iff.1 (g : Gz X u).2
  have hL : Formalism.HermitianLatticesTheory.gmap (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (Lmap X u Λ) =
      Lmap X u Λ := MulAction.mem_stabilizer_iff.1 g.2
  have hg : ∀ x y, hb X ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) x)
      ((((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) y) = hb X x y :=
    ((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)).2
  refine ⟨⟨conj_isom X u _ hg, ?_⟩, (gmap_conj X u Λ _).2 hL⟩
  have e := conj_iota X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X) (zb X u)
  rw [hz, definiteInclusion_orthogonal_negativeVector] at e
  exact e

theorem unconj_mem (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (σ : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) :
    ∃ (h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X)) (h2 : (⟨unconj X u σ.1, h1⟩ : Formalism.HermitianLatticesTheory.isom (hb X)) ∈ Gz X u),
      (⟨⟨unconj X u σ.1, h1⟩, h2⟩ : Gz X u) ∈ MulAction.stabilizer (Gz X u) (Lmap X u Λ) := by
  obtain ⟨⟨hi, hz⟩, hM⟩ := σ.2
  have h1 : unconj X u σ.1 ∈ Formalism.HermitianLatticesTheory.isom (hb X) := by
    intro x y
    rw [← iota_h, ← iota_h]
    have e : ∀ w, iota X u (unconj X u σ.1 w) = σ.1 (iota X u w) := fun w => by simp [unconj]
    rw [e, e]
    exact hi _ _
  refine ⟨h1, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    show unconj X u σ.1 (zb X u) = zb X u
    apply (iota X u).injective
    simp only [unconj, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, definiteInclusion_orthogonal_negativeVector]
    exact hz
  · rw [MulAction.mem_stabilizer_iff]
    show Formalism.HermitianLatticesTheory.gmap (unconj X u σ.1) (Lmap X u Λ) = Lmap X u Λ
    rw [← gmap_conj, conj_unconj]
    exact hM

theorem card_stab (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Nat.card (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.stabZ (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.hWb D (X.Fu u))
        (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.zbar D (X.Fu u)) (PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.Mof D (X.Fu u) Λ)) =
      Nat.card (MulAction.stabilizer (Gz X u) (Lmap X u Λ)) := by
  refine (Nat.card_congr
    { toFun := fun g => ⟨conj X u (((g : Gz X u) : Formalism.HermitianLatticesTheory.isom (hb X)) : Wb X ≃ₗ[D.host.E] Wb X), conj_mem X u Λ g⟩
      invFun := fun σ => ⟨⟨⟨unconj X u σ.1, (unconj_mem X u Λ σ).1⟩, (unconj_mem X u Λ σ).2.1⟩,
        (unconj_mem X u Λ σ).2.2⟩
      left_inv := fun g => by
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        exact unconj_conj X u _
      right_inv := fun σ => by
        apply Subtype.ext
        exact conj_unconj X u _ }).symm

end GlobalTheory.RowsOrbCard

namespace GlobalTheory.RowsOrb

theorem card_autLz : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ →
    ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) =
      Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  intro D large₂ X Y u _ Λ hΛ
  rw [PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_weight_formula D u (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ)]
  exact GlobalTheory.RowsOrbCard.card_stab X u Λ

end GlobalTheory.RowsOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardRowAutomorphismsEqLatticeStabilizerStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_row_automorphisms_eq_lattice_stabilizer : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), GlobalTheory.TypeAsm.Std D large₂ → ∀ Λ ∈ Y.what₂ u, Nat.card (autLz D (X.Fu u) Λ) = Nat.card (MulAction.stabilizer (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.card_autLz | exact GlobalTheory.RowsOrb.card_autLz | (intros; apply GlobalTheory.RowsOrb.card_autLz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefinite
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb

variable {D : D7}

theorem eq_zero_of_mem_span_eX (X : HidaSetting D) (w : (VS D).V)
    (hw : w ∈ Submodule.span D.host.E (Set.range X.eX)) (hf : ∀ b, (VS D).hT (X.fY b) w = 0) : w = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hw
  have hc : ∀ b, c b = 0 := by
    intro b
    have h := hf b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul] at h
    have hfe : ∀ a, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
      intro a
      rw [a_herm, X.ef a b]
      split_ifs <;> simp
    simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  simp [hc]

theorem pd_hU : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  intro D X u τ x hx
  have hpos : (GlobalTheory.TypeAsm.F0 X u).PosDefAt τ :=
    Formalism.MainNotions.KappaEndpoints.nf_pos (lf D (X.Fu u)) (GlobalTheory.TypeAsm.tu_ne D u)
      (p_posX D (Tu D u) (D.mem u).A.T_prime.pos _) τ
  set w : (VS D).V := ((x : Wb X) : (VS D).V) with hwdef
  have hWb := (mem_Wb X _).1 (x : Wb X).2
  have hUb := (mem_Ub X u _).1 x.2
  have hw0 : w ≠ 0 := by
    intro h
    apply hx
    exact Subtype.ext (Subtype.ext h)
  have h1 : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) w = 0 := by
    intro a
    change (VS D).hT w ((X.Fu u).fvec a) = 0
    induction a using Fin.lastCases with
    | last =>
      rw [FlagG.fvec, Fin.snoc_last, X.flagZVector]
      exact p_symm_zero (VS D) hUb
    | cast b =>
      rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
      exact p_symm_zero (VS D) (hWb b).1
  have h2 : w ∉ (GlobalTheory.TypeAsm.F0 X u).X := by
    intro hX
    apply hw0
    refine eq_zero_of_mem_span_eX X w ?_ (fun b => (hWb b).2)
    refine (Submodule.span_le.2 ?_) hX
    rintro _ ⟨b, -, rfl⟩
    change (X.Fu u).fvec b.castSucc ∈ _
    rw [FlagG.fvec, Fin.snoc_castSucc, X.Fu_e]
    exact Submodule.subset_span ⟨b, rfl⟩
  have := hpos w h1 h2
  rw [hU_apply]
  exact this

end GlobalTheory.RowsOrb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalTotallyPositiveDefiniteStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropicOrthogonal_totallyPositiveDefinite : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.Mass.PD (GlobalTheory.RowsOrb.hU X u) := by
  first | exact @GlobalTheory.RowsOrb.pd_hU | exact GlobalTheory.RowsOrb.pd_hU | (intros; apply GlobalTheory.RowsOrb.pd_hU <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalIsometricDefiniteModel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalIsometricDefiniteModel
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem fixedFrameOfWord_castSucc_eq_hyperbolic (a : Fin D.R.rS) : (GlobalTheory.TypeAsm.F0 X u).e a.castSucc = X.eX a := by
  show (lf D (X.Fu u)).fl.fvec a.castSucc = X.eX a
  rw [GlobalTheory.TypeAsm.fv_cast]
  exact congrFun (X.Fu_e u) a

theorem fixedFrameOfWord_last_eq_anisotropic : (GlobalTheory.TypeAsm.F0 X u).e (Fin.last _) = X.zu u := by
  show (lf D (X.Fu u)).fl.fvec (Fin.last _) = X.zu u
  rw [GlobalTheory.TypeAsm.fv_last]
  exact X.flagZVector u

theorem fixedFrameOfWord_isotropicSpan_eq : (GlobalTheory.TypeAsm.F0 X u).X = Submodule.span D.host.E (Set.range X.eX) := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, fixedFrameOfWord_castSucc_eq_hyperbolic]
  exact ⟨fun ⟨b, _, h⟩ => ⟨b, h⟩, fun ⟨b, h⟩ => ⟨b, b.isLt, h⟩⟩

theorem hT_span_left {v : (VS D).V} (hv : ∀ a, (VS D).hT (X.eX a) v = 0) {y : (VS D).V}
    (hy : y ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y v = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, hv]

theorem hT_span_span {y y' : (VS D).V} (hy : y ∈ Submodule.span D.host.E (Set.range X.eX))
    (hy' : y' ∈ Submodule.span D.host.E (Set.range X.eX)) : (VS D).hT y y' = 0 := by
  refine hT_span_left X (fun a => ?_) hy
  exact p_symm_zero (VS D) (hT_span_left X (fun b => X.ee b a) hy')

theorem hT_f_e (a b : Fin D.R.rS) : (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := by
  rw [a_herm (S := VS D) (X.eX a) (X.fY b), X.ef a b]
  split_ifs <;> simp

theorem span_eq_zero {d : (VS D).V} (hd : d ∈ Submodule.span D.host.E (Set.range X.eX))
    (h : ∀ b, (VS D).hT (X.fY b) d = 0) : d = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hd
  have hc : ∀ b, c b = 0 := by
    intro b
    have := h b
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, hT_f_e] using this
  simp [hc]

end GlobalTheory.RowsOrb.ModelIso

namespace GlobalTheory.RowsOrb.ModelIso

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def corr (W : Submodule D.host.E (VS D).V) : W →ₗ[D.host.E] (VS D).V :=
  ∑ a, LinearMap.smulRight (((VS D).hT (X.fY a)).comp W.subtype) (X.eX a)

theorem corr_apply (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w = ∑ a, (VS D).hT (X.fY a) (w : (VS D).V) • X.eX a := by
  simp [corr, LinearMap.sum_apply]

theorem corr_mem (W : Submodule D.host.E (VS D).V) (w : W) :
    corr X W w ∈ Submodule.span D.host.E (Set.range X.eX) := by
  rw [corr_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end GlobalTheory.RowsOrb.ModelIso


open GlobalTheory.RowsOrb.ModelIso in
theorem GlobalTheory.RowsOrb.ub_equiv_model : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (GlobalTheory.TypeAsm.F0 X u) HW W.subtype →
    ∃ e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W, (∀ x y, HW.B.flip (e x) (e y) = GlobalTheory.RowsOrb.hU X u x y) ∧
      ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X := by
  intro D X u W HW hE

  have hWe : ∀ (w : W) a, (VS D).hT (X.eX a) (w : (VS D).V) = 0 := by
    intro w a
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) a.castSucc
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e a.castSucc) = 0 at h
    rw [fixedFrameOfWord_castSucc_eq_hyperbolic] at h
    exact p_symm_zero (VS D) h
  have hWz : ∀ w : W, (VS D).hT (X.zu u) (w : (VS D).V) = 0 := by
    intro w
    have h := ((hE.2 (w : (VS D).V)).2 (Submodule.mem_sup_left ⟨w, rfl⟩)) (Fin.last _)
    change (VS D).hT (w : (VS D).V) ((GlobalTheory.TypeAsm.F0 X u).e (Fin.last _)) = 0 at h
    rw [fixedFrameOfWord_last_eq_anisotropic] at h
    exact p_symm_zero (VS D) h
  have hXW : ∀ (w : W) {y : (VS D).V}, y ∈ Submodule.span D.host.E (Set.range X.eX) →
      (VS D).hT y (w : (VS D).V) = 0 ∧ (VS D).hT (w : (VS D).V) y = 0 := by
    intro w y hy
    have h := hT_span_left X (hWe w) hy
    exact ⟨h, p_symm_zero (VS D) h⟩
  have hBW : ∀ x y : W, HW.B x y = (VS D).hT (y : (VS D).V) (x : (VS D).V) := fun x y => (hE.1 x y).symm

  have hmWb : ∀ w : W, (w : (VS D).V) - corr X W w ∈ GlobalTheory.RowsOrb.Wb X := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Wb]
    intro b
    have hc := corr_mem X W w
    refine ⟨?_, ?_⟩
    · rw [map_sub, hWe w b, zero_sub, neg_eq_zero]
      exact p_symm_zero (VS D) (hT_span_left X (fun a => X.ee a b) hc)
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, corr_apply, map_sum]
        simp only [map_smul, hT_f_e, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true, sub_self]
  have hmUb : ∀ w : W, (⟨(w : (VS D).V) - corr X W w, hmWb w⟩ : GlobalTheory.RowsOrb.Wb X) ∈ GlobalTheory.RowsOrb.Ub X u := by
    intro w
    rw [GlobalTheory.RowsOrb.mem_Ub]
    change (VS D).hT (X.zu u) ((w : (VS D).V) - corr X W w) = 0
    rw [map_sub, hWz w, zero_sub, neg_eq_zero]
    refine p_symm_zero (VS D) (hT_span_left X (fun a => (X.zu_orth u a).1) (corr_mem X W w))
  let g : W →ₗ[D.host.E] GlobalTheory.RowsOrb.Ub X u :=
    { toFun := fun w => ⟨⟨(w : (VS D).V) - corr X W w, hmWb w⟩, hmUb w⟩
      map_add' := fun x y => by ext; simp only [Submodule.coe_add, map_add (f := _)]; abel
      map_smul' := fun c x => by ext; simp [smul_sub] }
  have hg : ∀ w, (((g w : GlobalTheory.RowsOrb.Wb X)) : (VS D).V) = (w : (VS D).V) - corr X W w := fun _ => rfl
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : (w : (VS D).V) = corr X W w := by
      have := congrArg (fun x : GlobalTheory.RowsOrb.Ub X u => ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V)) hw
      simp only [hg, ZeroMemClass.coe_zero] at this
      exact sub_eq_zero.1 this
    have hmem : (w : (VS D).V) ∈ Submodule.span D.host.E (Set.range X.eX) := h0 ▸ corr_mem X W w
    exact HW.nondeg w fun y => by rw [hBW]; exact (hXW y hmem).2
  have hsurj : Function.Surjective g := by
    intro x
    have hv : ∀ a : Fin (D.R.rS + 1), (GlobalTheory.TypeAsm.HV D).B ((GlobalTheory.TypeAsm.F0 X u).e a) ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      intro a
      change (VS D).hT _ ((GlobalTheory.TypeAsm.F0 X u).e a) = 0
      refine Fin.lastCases ?_ (fun b => ?_) a
      · rw [fixedFrameOfWord_last_eq_anisotropic]; exact p_symm_zero (VS D) ((GlobalTheory.RowsOrb.mem_Ub X u _).1 x.2)
      · rw [fixedFrameOfWord_castSucc_eq_hyperbolic]; exact p_symm_zero (VS D) ((((x : GlobalTheory.RowsOrb.Wb X)).2 b).1)
    obtain ⟨y, ⟨w, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 ((hE.2 _).1 hv)
    refine ⟨w, ?_⟩
    rw [fixedFrameOfWord_isotropicSpan_eq] at hz
    have hd : ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) - ((g w : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = 0 := by
      apply span_eq_zero X
      · rw [hg, ← hyz]
        have : (W.subtype w + z) - ((w : (VS D).V) - corr X W w) = z + corr X W w := by
          simp only [Submodule.subtype_apply]; abel
        rw [this]
        exact Submodule.add_mem _ hz (corr_mem X W w)
      · intro b
        exact ((Submodule.sub_mem _ (x : GlobalTheory.RowsOrb.Wb X).2 (g w : GlobalTheory.RowsOrb.Wb X).2) b).2
    ext
    exact (sub_eq_zero.1 hd).symm
  let e := (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).symm
  have hge : ∀ x, g (e x) = x := fun x => (LinearEquiv.ofBijective g ⟨hinj, hsurj⟩).apply_symm_apply x
  have hxe : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) = ((e x : W) : (VS D).V) - corr X W (e x) := by
    intro x
    rw [← hg (e x), hge x]
  refine ⟨e, fun x y => ?_, fun x => ?_⟩
  · rw [LinearMap.flip_apply, hBW, GlobalTheory.RowsOrb.hU_apply, hxe x, hxe y]
    have h1 := (hXW (e y) (corr_mem X W (e x))).1
    have h2 := (hXW (e x) (corr_mem X W (e y))).2
    have h3 := hT_span_span X (corr_mem X W (e x)) (corr_mem X W (e y))
    simp only [map_sub, LinearMap.sub_apply, h1, h2, h3, sub_zero]
  · rw [hxe x, sub_sub_cancel, fixedFrameOfWord_isotropicSpan_eq]
    exact corr_mem X W (e x)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnisotropicOrthogonalIsometricDefiniteModelStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropicOrthogonal_isometric_definiteModel : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (GlobalTheory.TypeAsm.F0 X u) HW W.subtype → ∃ e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W, (∀ x y, HW.B.flip (e x) (e y) = GlobalTheory.RowsOrb.hU X u x y) ∧ ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X := by
  first | exact @GlobalTheory.RowsOrb.ub_equiv_model | exact GlobalTheory.RowsOrb.ub_equiv_model | (intros; apply GlobalTheory.RowsOrb.ub_equiv_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSum
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mass.Transp

theorem orbSum_img : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he φ hφ L
  have hinv : ∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V),
      φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M) := by
    intro s M
    have hs := img_smul (R := 𝓞 K) e he s M
    erw [hs, hφ]
  have hgen : ∀ M : Submodule (𝓞 K) V,
      GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L := by
    intro M
    constructor
    · intro hM
      have := genus_img e.symm (symm_isom e he) _ _ hM
      rwa [img_symm_img, img_symm_img] at this
    · exact genus_img e he L M
  refine ⟨hinv, hgen, ?_⟩
  symm
  refine GlobalTheory.Mass.OrbTransport.main _ _ _ _ (conj e he) (img e) _ _ φ (genus_stable _) (genus_stable _) ?_
    (fun g x _ => img_smul e he g x) hφ
  refine ⟨fun M hM => (hgen M).2 hM, fun a _ b _ hab => ?_, fun M hM => ⟨img e.symm M, ?_, img_img_symm e M⟩⟩
  · rw [← img_symm_img e a, hab, img_symm_img]
  · rw [← hgen, img_img_symm]; exact hM

end GlobalTheory.Mass.Transp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSumStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_transports_genus_orbitSum : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  first | exact @GlobalTheory.Mass.Transp.orbSum_img | exact GlobalTheory.Mass.Transp.orbSum_img | (intros; apply GlobalTheory.Mass.Transp.orbSum_img <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPart
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPart
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem lat0_eq_img_latIn_Ub (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V)
    (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W)
    (he : ∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ
      = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  ext w
  rw [GlobalTheory.Mass.Transp.mem_img]
  have hd : ((e (e.symm w) : W) : (VS D).V) - (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
      ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X :=
    (le_sup_right : GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X ≤ _) (he (e.symm w))
  rw [LinearEquiv.apply_symm_apply] at hd
  have h1 : w ∈ GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ ↔
      (w : (VS D).V) ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  have h2 : e.symm w ∈ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ↔
      (((e.symm w : GlobalTheory.RowsOrb.Ub X u) : GlobalTheory.RowsOrb.Wb X) : (VS D).V)
        ∈ Λ ⊔ GlobalTheory.HermLat.rs (𝓞 D.host.E) (GlobalTheory.TypeAsm.F0 X u).X := Iff.rfl
  rw [h1, h2]
  constructor
  · intro h
    simpa using Submodule.sub_mem _ h hd
  · intro h
    simpa using Submodule.add_mem _ hd h

end GlobalTheory.RowsOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientLatticeEqImageAnisotropicPartStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (W : Submodule D.host.E (VS D).V) (e : GlobalTheory.RowsOrb.Ub X u ≃ₗ[D.host.E] W), (∀ x : GlobalTheory.RowsOrb.Ub X u, ((e x : W) : (VS D).V) - ((x : GlobalTheory.RowsOrb.Wb X) : (VS D).V) ∈ (GlobalTheory.TypeAsm.F0 X u).X) → ∀ Λ : Submodule (𝓞 D.host.E) (VS D).V, GlobalTheory.DegAsm.lat0 (GlobalTheory.TypeAsm.F0 X u) W.subtype Λ = GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ)) := by
  first | exact @GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | exact GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub | (intros; apply GlobalTheory.RowsOrb.lat0_eq_img_latIn_Ub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizer
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.StabSet

open GlobalTheory.Mass Formalism.HermitianLatticesTheory GlobalTheory.Mass.RowMean

theorem main : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  intro D X u M₀ ψ hψ
  have hU : ∀ v, v ∈ GlobalTheory.RowsOrb.Ub X u ↔ GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) v = 0 :=
    fun v => GlobalTheory.RowsOrb.mem_Ub X u v
  have hπ : ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)),
      GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) =
        resZ (GlobalTheory.RowsOrb.hb X) hU g • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L :=
    fun g L => StabSplit.latIn_smul (GlobalTheory.RowsOrb.hb X) (GlobalTheory.RowsOrb.Ub X u) g.1 (smul_compl _ hU g) L
  have hY : Stable (isom (GlobalTheory.RowsOrb.hU X u)) (genus (GlobalTheory.RowsOrb.hU X u) M₀) :=
    Transp.genus_stable (R := 𝓞 D.host.E) (K := D.host.E) (V := GlobalTheory.RowsOrb.Ub X u) (h := GlobalTheory.RowsOrb.hU X u) M₀
  refine ⟨?_, fun g L => by rw [hπ]; exact hψ _ _⟩
  rintro g L ⟨h1, h2, h3, h4⟩
  have H := Formalism.HermitianLatticesTheory.isomAct (𝓞 D.host.E) D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) g.1.1 g.1.2 L
  refine ⟨H.2.2.2.2.2 h1, H.2.2.2.1.2 h2, fun t => ?_, ?_⟩
  · have hg : g.1.1 (GlobalTheory.RowsOrb.zb X u) = GlobalTheory.RowsOrb.zb X u := g.2
    have hs : g.1.1.symm (t • GlobalTheory.RowsOrb.zb X u) = t • GlobalTheory.RowsOrb.zb X u :=
      g.1.1.symm_apply_eq.2 (by rw [map_smul, hg])
    change t • GlobalTheory.RowsOrb.zb X u ∈ Formalism.HermitianLatticesTheory.gmap (g.1.1 : GlobalTheory.RowsOrb.Wb X ≃ₗ[D.host.E] GlobalTheory.RowsOrb.Wb X) L ↔ _
    rw [isomAct_mem_gmap, hs, h3]
  · let s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u) := resZ (GlobalTheory.RowsOrb.hb X) hU g
    have k : s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀ := hY s _ h4
    have e : GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L) = s • GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L := hπ g L
    exact Eq.mpr (congrArg (fun N => N ∈ genus (GlobalTheory.RowsOrb.hU X u) M₀) e) k

end GlobalTheory.RowsOrb.StabSet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesStableUnderVectorStabilizerStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (M₀ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)) (ψ : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u) → ℝ≥0∞), (∀ (s : Formalism.HermitianLatticesTheory.isom (GlobalTheory.RowsOrb.hU X u)) (M : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Ub X u)), ψ (s • M) = ψ M) → GlobalTheory.Mass.Stable (GlobalTheory.RowsOrb.Gz X u) {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} ∧ ∀ (g : GlobalTheory.RowsOrb.Gz X u) (L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X)), ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (g • L)) = ψ (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L) := by
  first | exact @GlobalTheory.RowsOrb.StabSet.main | exact GlobalTheory.RowsOrb.StabSet.main | (intros; apply GlobalTheory.RowsOrb.StabSet.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModule
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModule
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mass.Transp.discModule_transport : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  intro K V V' _ _ _ _ _ _ _ _ _ _ _ h h' e he L I hI hQ
  have hL : GlobalTheory.Mass.IsIntLat h L := by
    have := GlobalTheory.Mass.Transp.intLat_img e.symm (GlobalTheory.Mass.Transp.symm_isom e he) _ hI
    rwa [GlobalTheory.Mass.Transp.img_symm_img] at this
  refine ⟨hL, ?_⟩
  obtain ⟨q⟩ := hQ
  set D := Formalism.HermitianLatticesTheory.dual h L with hDdef
  set D' := Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L) with hD'def
  have hD : D' = GlobalTheory.Mass.Transp.img e D := GlobalTheory.Mass.Transp.dual_img e he L
  have hmem : ∀ x : V, x ∈ D → e x ∈ D' := by
    intro x hx; rw [hD, GlobalTheory.Mass.Transp.mem_img]; simpa using hx
  have hmem' : ∀ y : V', y ∈ D' → e.symm y ∈ D := by
    intro y hy; rw [hD, GlobalTheory.Mass.Transp.mem_img] at hy; exact hy
  let f : D ≃ₗ[𝓞 K] D' :=
    { toFun := fun x => ⟨e x, hmem x x.2⟩
      invFun := fun y => ⟨e.symm y, hmem' y y.2⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by
        ext
        simp only [SetLike.val_smul, RingHom.id_apply]
        exact (e.toLinearMap.restrictScalars (𝓞 K)).map_smul r x
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp }
  have hf : (L.comap D.subtype).map (f : D →ₗ[𝓞 K] D') = (GlobalTheory.Mass.Transp.img e L).comap D'.subtype := by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    rw [GlobalTheory.Mass.Transp.mem_img]
    constructor
    · rintro ⟨⟨x, hx⟩, hxL, hxy⟩
      have : (f ⟨x, hx⟩ : V') = y := congrArg Subtype.val hxy
      simp only [f, LinearEquiv.coe_mk] at this
      rw [← this]; simpa using hxL
    · intro hyL
      refine ⟨⟨e.symm y, hmem' y hy⟩, hyL, ?_⟩
      ext; simp [f]
  exact ⟨(Submodule.Quotient.equiv _ _ f hf).trans q⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsDiscriminantModuleStatement
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_transports_discriminantModule : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ (L : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)), GlobalTheory.Mass.IsIntLat h' (GlobalTheory.Mass.Transp.img e L) → Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)) ⧸ (GlobalTheory.Mass.Transp.img e L).comap (Formalism.HermitianLatticesTheory.dual h' (GlobalTheory.Mass.Transp.img e L)).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) → GlobalTheory.Mass.IsIntLat h L ∧ Nonempty ((↥(Formalism.HermitianLatticesTheory.dual h L) ⧸ L.comap (Formalism.HermitianLatticesTheory.dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ I)) := by
  first | exact @GlobalTheory.Mass.Transp.discModule_transport | exact GlobalTheory.Mass.Transp.discModule_transport | (intros; apply GlobalTheory.Mass.Transp.discModule_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparison
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb

theorem cardE (α : Type) [Nonempty α] :
    ENNReal.ofReal ((Nat.card α : ℝ)⁻¹) = ((ENat.card α : ℕ∞) : ℝ≥0∞)⁻¹ := by
  rcases finite_or_infinite α with h | h
  · have h0 : 0 < Nat.card α := Nat.card_pos
    rw [ENat.card_eq_coe_natCard, ENNReal.ofReal_inv_of_pos (by exact_mod_cast h0), ENNReal.ofReal_natCast]
    simp
  · rw [Nat.card_eq_zero_of_infinite, ENat.card_eq_top_of_infinite]
    simp

set_option maxHeartbeats 4000000 in
theorem rowsOrbC : GlobalTheory.TypeAsm.RowsOrbC := by
  intro D large₂ X Y u hS W HW hEmb φ hφ Λ₀ hΛ₀
  obtain ⟨e, he, heX⟩ := GlobalTheory.T.anisotropicOrthogonal_isometric_definiteModel D X u W HW hEmb
  have hlat := GlobalTheory.T.definiteQuotientLattice_eq_image_anisotropicPart D X u W e heX
  set M₀ := GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ₀) with hM₀
  obtain ⟨hψ, hgen, horb⟩ := GlobalTheory.T.isometry_transports_genus_orbitSum D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he φ hφ M₀
  obtain ⟨hcm, -, -, -, hf, -, -, -, -, -, -, -, hTu⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨hTp, hsp⟩ := hTu u
  have hl0 := GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hS W HW hEmb Λ₀ hΛ₀
  rw [hlat Λ₀] at hl0
  obtain ⟨hM₀i, hM₀d⟩ := GlobalTheory.T.isometry_transports_discriminantModule D.host.E (GlobalTheory.RowsOrb.Ub X u) W (GlobalTheory.RowsOrb.hU X u) HW.B.flip e he M₀ _ hl0.1 hl0.2
  have hbs : (GlobalTheory.RowsOrb.hb X).IsSymm := ⟨fun a b => (VS D).herm.eq (a : (VS D).V) (b : (VS D).V)⟩
  have hz : GlobalTheory.RowsOrb.hb X (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.zb X u) = -((Tu D u : ℕ) : D.host.E) := X.zu_norm u
  have hrm := GlobalTheory.Mass.RowMean.main D.host.E (GlobalTheory.RowsOrb.Wb X) (GlobalTheory.RowsOrb.hb X) hcm hbs (Tu D u)
    (GlobalTheory.RowsOrb.zb X u) (GlobalTheory.RowsOrb.Ub X u) hTp hsp hz rfl (GlobalTheory.T.anisotropicOrthogonal_totallyPositiveDefinite D X u) M₀ hM₀i hM₀d
    (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  simp only [hlat, ← hM₀, hgen]
  rw [horb, ← hf]
  refine Eq.trans ?_ hrm
  obtain ⟨hst, hinv⟩ := GlobalTheory.T.gluedLattices_stable_under_vectorStabilizer D X u M₀ (fun M => φ (GlobalTheory.Mass.Transp.img e M)) hψ
  have hinj : ∀ a ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      ∀ b ∈ (Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀),
      GlobalTheory.RowsOrb.Lmap X u a = GlobalTheory.RowsOrb.Lmap X u b → a = b := by
    intro a ha b hb hab
    exact GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices D large₂ X Y u hS a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 1 ((one_smul (GlobalTheory.RowsOrb.Gz X u) (GlobalTheory.RowsOrb.Lmap X u a)).trans hab)
  refine Eq.trans ?_ (GlobalTheory.Mass.orbSum_eq_sum_reps (GlobalTheory.RowsOrb.Gz X u) (Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X))
    {L : Submodule (𝓞 D.host.E) (GlobalTheory.RowsOrb.Wb X) | Submodule.IsLattice D.host.E L ∧ Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.RowsOrb.hb X) L ∧ (∀ t : D.host.E, t • GlobalTheory.RowsOrb.zb X u ∈ L ↔ t ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ∧ GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀} (fun L => φ (GlobalTheory.Mass.Transp.img e (GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) L))) hst (fun g L => hinv g L)
    (((Y.what₂ u).filter (fun Λ => GlobalTheory.Mass.latIn (GlobalTheory.RowsOrb.Ub X u) (GlobalTheory.RowsOrb.Lmap X u Λ) ∈ Formalism.HermitianLatticesTheory.genus (GlobalTheory.RowsOrb.hU X u) M₀)).image (GlobalTheory.RowsOrb.Lmap X u)) ?_ ?_).symm
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    congr 1
    show ENNReal.ofReal ((Nat.card (autLz D (X.Fu u) Λ) : ℝ)⁻¹) = _
    rw [GlobalTheory.T.card_row_automorphisms_eq_lattice_stabilizer D large₂ X Y u hS Λ (Finset.mem_filter.1 hΛ).1, cardE]
  · intro L hL
    obtain ⟨Λ, hΛ, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨hΛr, hΛg⟩ := Finset.mem_filter.1 hΛ
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.orbit_lattice_unimodular_and_primitive D large₂ X Y u hS Λ hΛr
    exact ⟨h1, h2, h3, hΛg⟩
  · intro L hL
    obtain ⟨Λ, hΛ, g, hg⟩ := GlobalTheory.T.exists_row_of_unimodular_lattice_primitive_vector D large₂ X Y u hS L hL.1 hL.2.1 hL.2.2.1
    refine ⟨GlobalTheory.RowsOrb.Lmap X u Λ, ⟨Finset.mem_image.2 ⟨Λ, Finset.mem_filter.2 ⟨hΛ, ?_⟩, rfl⟩, g, hg⟩, ?_⟩
    · have := hst g⁻¹ L hL
      erw [← hg, inv_smul_smul] at this
      exact this.2.2.2
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.1 hy
      congr 1
      exact GlobalTheory.T.rows_eq_of_stabilizer_conjugate_lattices D large₂ X Y u hS Λ' (Finset.mem_filter.1 hΛ').1 Λ hΛ (g⁻¹ * g') (by erw [mul_smul, hg', ← hg, inv_smul_smul])

end GlobalTheory.RowsOrb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsGenusWeightedSumComparisonStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsGenus_weightedSumComparison : GlobalTheory.TypeAsm.RowsOrbC := by
  first | exact @GlobalTheory.RowsOrb.rowsOrbC | exact GlobalTheory.RowsOrb.rowsOrbC | (intros; apply GlobalTheory.RowsOrb.rowsOrbC <;> assumption)
end
