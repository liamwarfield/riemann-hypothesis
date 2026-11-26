module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainCommutationValid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelGeneratedByLocalUnipotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveMain
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotLevGEmpty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralAdaptedElementProperty
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIdentityOffFreePositionsRightBlockIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MemMatch

variable {D : D7}

theorem st_of_kset (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0))
    (κ : GA D (D.sp.Y 0)) (hκ : (iotaX X h κ).2 ∈ X.B.I.Kset) : Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D),
      (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ I.Kset → Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β := by
    intro I hI hx
    subst hI
    have hL : (Formalism.L2.SG.InstExistsPf.instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 :=
      Formalism.L2.SG.InstExistsPf.Lv_eq_map D
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx' := (GlobalTheory.FlagBasis.kset_iff (Formalism.L2.SG.InstExistsPf.instOf D) (β := β) (hL ▸ hβ) _).1 hx
    rw [e2]
    exact hx'
  exact key X.B.I h hκ

theorem exists_generic (Pg : Finset (Pl D.host.E)) : ∃ ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi Pg ψ := by
  have h : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    haveI : Finite (kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
    haveI : Nontrivial (kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun e => hψ (by rw [e]; rfl)⟩
  choose ψ hψ using h
  exact ⟨ψ, fun PP _ => hψ PP⟩

theorem isIdentityOffFreePositions_rightBlock_iff {K : Type} [CommRing K] {r n : ℕ} (ρ k : ℕ) (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) K) :
    GlobalTheory.SymRes.IsPat ρ k (upperLeftBlock hr g) ↔ GlobalTheory.SymRes.IsPat ρ k g := by
  obtain rfl : r = n := le_antisymm hr hn
  rw [GlobalTheory.SeeConjRead.restrictedBlock_self_apply]

theorem reductionBlock_injective_of_eq {K : Type} [CommRing K] {r n : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g g' : GL (Fin n) K)
    (h : upperLeftBlock hr g = upperLeftBlock hr g') : g = g' := by
  obtain rfl : r = n := le_antisymm hr hn
  rwa [GlobalTheory.SeeConjRead.restrictedBlock_self_apply, GlobalTheory.SeeConjRead.restrictedBlock_self_apply] at h

theorem conj_mem_GfC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (s k : GA D (D.sp.Y 0)) (hk : k ∈ GfC (D.sp.Y 0)) : s * k * s⁻¹ ∈ GfC (D.sp.Y 0) := by
  rw [← GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h] at hk ⊢
  rw [map_mul, map_mul, map_inv, Prod.fst_mul, Prod.fst_mul, hk, mul_one, Prod.fst_inv, mul_inv_cancel]

theorem exists_read (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hTP : IsTypePlaces Pg) (hsp : ∃ e, IsIdemSum e Pg)
    (hid : ∀ PP : Pg, ∃ e, Formalism.L2.NTheta.IsIdemAt (D := D) e PP.1)
    (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (Λ) (N : ℕ) (hβ : Lev.IsBaseFrame (D.sp.Y 0) β Λ N) (s : GA D (D.sp.Y 0))
    (hSt : ∀ κ : GA D (D.sp.Y 0), (κ ∈ GfC (D.sp.Y 0) ∧ finE (D.sp.Y 0) κ ∈ St (finE (D.sp.Y 0) s * β)) ↔
      ((iotaX X h κ).1 = 1 ∧ (iotaX X h κ).2 ∈ X.B.I.Kset)) :
    ∃ m : ∀ PP : Pg, GL (Fin (D.sp.Y 0).rank) (kP PP.1), ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β →
      ((iotaX X h (s * k * s⁻¹)).2 ∈ X.K2 ↔ ∀ PP : Pg, m PP * redFn β PP.1 (finE (D.sp.Y 0) k) * (m PP)⁻¹ ∈
        unipSym (kP PP.1) (D.sp.Y 0).rank D.R.rS D.R.k) := by
  obtain ⟨ψ0, hψ⟩ := exists_generic Pg
  obtain ⟨β₀, hβ₀, hK⟩ := GlobalTheory.SeeConjRead.read_fin X h Pg hTP (GlobalTheory.T.genusTypePlaceSet_not_conjugatePlaces Pg hTP hsp) ψ0 hψ
  have hfe : ∀ k : GA D (D.sp.Y 0), finE (D.sp.Y 0) (s * k * s⁻¹) =
      finE (D.sp.Y 0) s * finE (D.sp.Y 0) k * (finE (D.sp.Y 0) s)⁻¹ := fun k => by rw [map_mul, map_mul, map_inv]
  obtain ⟨β₂, rfl⟩ : ∃ β₂, β₀ = finE (D.sp.Y 0) s * β₂ := ⟨(finE (D.sp.Y 0) s)⁻¹ * β₀, by group⟩
  have h12 : ∀ k ∈ GfC (D.sp.Y 0), finE (D.sp.Y 0) k ∈ St β → finE (D.sp.Y 0) k ∈ St β₂ := by
    intro k hk hS
    have h1 := ((hSt (s * k * s⁻¹)).1 ⟨conj_mem_GfC X h s k hk, by
      rw [hfe, GlobalTheory.FrameConj.conj_mem_St_iff]; exact hS⟩).2
    have h2 := st_of_kset X h _ hβ₀ _ h1
    rwa [hfe, GlobalTheory.FrameConj.conj_mem_St_iff] at h2
  have hm := fun PP : Pg => (hid PP).elim fun e he => GlobalTheory.T.splitPlaceReductions_conj_of_nestedFrameStabilisers D (D.sp.Y 0) β β₂ Λ N hβ e PP.1 he h12
  choose m hm using hm
  refine ⟨m, fun k hk hS => ?_⟩
  rw [(hK _).1, hfe, GlobalTheory.FrameConj.conj_mem_St_iff]
  simp only [GlobalTheory.FrameConj.redFn_conj]
  refine ⟨fun hh PP => ?_, fun hh => ⟨h12 k hk hS, fun PP hPP => ?_⟩⟩
  · rw [← hm PP _ hS (h12 k hk hS)]; exact hh.2 PP.1 PP.2
  · rw [hm ⟨PP, hPP⟩ _ hS (h12 k hk hS)]; exact hh ⟨PP, hPP⟩

end GlobalTheory.MemMatch

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevZeroMem

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

theorem h0_eq (D : D7) : 0 + 2 * D.R.rS + 2 = D.R.m := by
  obtain ⟨q, hq⟩ := D.R.m_even
  have := D.R.two_le_m
  unfold Ranks.rS
  omega




end GlobalTheory.LevZeroMem

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryChainStepValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PenVol

section Gen

open ValuativeRel

variable {k n : Type} [Field k] [ValuativeRel k] [Fintype n] [DecidableEq n]

theorem mulVec_mem_box_of_int (A : Matrix n n k) (hA : ∀ i j, valuation k (A i j) ≤ 1) {c : kˣ} {y : n → k}
    (hy : y ∈ GlobalTheory.StepData.box n c) : A *ᵥ y ∈ GlobalTheory.StepData.box n c := by
  intro i
  show valuation k ((A *ᵥ y) i) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  calc valuation k (A i j) * valuation k (y j) ≤ 1 * valuation k (c : k) := mul_le_mul' (hA i j) (hy j)
    _ = valuation k (c : k) := one_mul _

theorem val_le_one_of_mem_KO {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (i j : n ⊕ Fin 0) :
    valuation k (g.val i j) ≤ 1 := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val i j).2

theorem toBlocks₁₁_mulVec_mem_box {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) {c : kˣ}
    {y : n → k} (hy : y ∈ GlobalTheory.StepData.box n c) : g.val.toBlocks₁₁ *ᵥ y ∈ GlobalTheory.StepData.box n c :=
  mulVec_mem_box_of_int _ (fun i j => val_le_one_of_mem_KO hg (Sum.inl i) (Sum.inl j)) hy

def boxQ {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    ((n → k) ⧸ GlobalTheory.StepData.box n c) →ₗ[𝒪[k]] ((n → k) ⧸ GlobalTheory.StepData.box n c) :=
  Submodule.mapQ _ _ ((Matrix.mulVecLin g.val.toBlocks₁₁).restrictScalars 𝒪[k])
    (fun _ hy => toBlocks₁₁_mulVec_mem_box hg hy)

theorem boxQ_mk {g : GL (n ⊕ Fin 0) k} (hg : g ∈ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) (y : n → k) :
    boxQ hg c (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y) := rfl

def boxAct (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ) :
    MulAction J ((n → k) ⧸ GlobalTheory.StepData.box n c) where
  smul g q := boxQ (hJ g.2) c q
  one_smul q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = _
    rw [boxQ_mk, show ((1 : J) : GL (n ⊕ Fin 0) k).val = 1 from rfl, toBlocks_one_fin_zero, Matrix.one_mulVec]
  mul_smul g h q := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show boxQ _ c _ = boxQ _ c (boxQ _ c _)
    rw [boxQ_mk, boxQ_mk, boxQ_mk, show ((g * h : J) : GL (n ⊕ Fin 0) k).val = g.val.val * h.val.val from rfl,
      toBlocks_mul_fin_zero, Matrix.mulVec_mulVec]

theorem relIndex_cosStab_box (J : Subgroup (GL (n ⊕ Fin 0) k)) (hJ : J ≤ GlobalTheory.SplitWeil.KO k (n ⊕ Fin 0)) (c : kˣ)
    (x : (n → k) ⧸ GlobalTheory.StepData.box n c) :
    (cosStab J (GlobalTheory.StepData.box n c) x).relIndex J = Nat.card {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
  letI := boxAct J hJ c
  have smk : ∀ (g : J) (y : n → k), g • (Submodule.Quotient.mk y : (n → k) ⧸ GlobalTheory.StepData.box n c) =
      Submodule.Quotient.mk (g.val.val.toBlocks₁₁ *ᵥ y) := fun _ _ => rfl
  have hst : (cosStab J (GlobalTheory.StepData.box n c) x).subgroupOf J = MulAction.stabilizer J x := by
    ext g
    rw [Subgroup.mem_subgroupOf, mem_cosStab, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [smk]
      exact (h y).2 rfl
    · intro h
      refine ⟨g.2, fun y => ?_⟩
      rw [← smk]
      constructor
      · intro h'
        rw [← h] at h'
        exact smul_left_cancel g h'
      · intro h'
        rw [h', h]
  have horb : MulAction.orbit J x = {yb | GlobalTheory.QPl.SameOrb J (GlobalTheory.StepData.box n c) x yb} := by
    ext yb
    simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq, GlobalTheory.QPl.SameOrb]
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact ⟨g.1, g.2, y, rfl, (smk g y).symm⟩
    · rintro ⟨g, hg, y, rfl, h⟩
      exact ⟨⟨g, hg⟩, by rw [smk]; exact h⟩
  rw [Subgroup.relIndex, hst, MulAction.index_stabilizer, horb, Nat.card_coe_set_eq]

end Gen

end GlobalTheory.PenVol

end

namespace GlobalTheory.PenVol

theorem relIndex_cosStab_eq_wt {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E}
    (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)) :
    (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex
      (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  have hJ := E.le (G.s + 1) 0 rfl
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ (cosStab_le _ _ _) hJ, relIndex_cosStab_box _ hJ, E.wt_pen y,
    E.idx_mid (G.s + 1) 0 rfl]
  push_cast
  ring

end GlobalTheory.PenVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexCouplingCosetStabilizerEqChartWeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_couplingCosetStabilizer_eq_chartWeight : ∀ {D : D7} {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP) {χ : ℕ → (AE D)ˣ →* Circle} (E : QExt G χ) (y : E.Ch (G.s + 1)), (((GlobalTheory.PenVol.cosStab ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (GlobalTheory.StepData.box _ (G.ϖ ^ E.M)) (E.cos y)).relIndex (GlobalTheory.SplitWeil.KO G.k _) : ℕ) : ℂ) = E.wt (G.s + 1) y := by
  first | exact @GlobalTheory.PenVol.relIndex_cosStab_eq_wt | exact GlobalTheory.PenVol.relIndex_cosStab_eq_wt | (intros; apply GlobalTheory.PenVol.relIndex_cosStab_eq_wt <;> assumption)
end
end

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PenVol

theorem relIndex_ne_zero_of_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K U U0 : Subgroup G)
    (hU0 : U0 ≤ K) (hc : IsCompact (U0 : Set G)) (ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K)) :
    U.relIndex U0 ≠ 0 := by
  haveI : CompactSpace U0 := isCompact_iff_compactSpace.1 hc
  have hcont : Continuous (fun x : U0 => (⟨x.1, hU0 x.2⟩ : K)) := Continuous.subtype_mk continuous_subtype_val _
  have ho' : IsOpen ((U.subgroupOf U0 : Subgroup U0) : Set U0) := ho.preimage hcont
  haveI : Finite (U0 ⧸ U.subgroupOf U0) := (U.subgroupOf U0).quotient_finite_of_isOpen ho'
  haveI : (U.subgroupOf U0).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero

theorem wt_cast (C : ℕ → Type) (w : ∀ j, C j → ℂ) {j j' : ℕ} (h : j = j') (x : C j) :
    w j' (cast (congrArg C h) x) = w j x := by
  subst h; rfl

end GlobalTheory.PenVol


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureIdentityAltBis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_identity_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((pk W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  first | exact @GlobalTheory.RLatMove.move_main | exact GlobalTheory.RLatMove.move_main | (intros; apply GlobalTheory.RLatMove.move_main <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFiniteIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Fam.MidLoc

theorem nonempty_colCh {D : D7} (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : Nonempty (ColCh u C) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => 0, eT := fun _ _ _ => 0, Ram := fun _ => ∅,
     S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 0, cK := fun _ => 0, cP := 0 }⟩

theorem nonempty_rowCh {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (P : LevelP R.Pg D.R.r ℂ) (hc : R.IsChain) (u : D.what₂.Word)
    (g : Fam.Geo D) (t : T) : Nonempty (RowCh R P u g t) :=
  ⟨{ vP := fun _ => 0, vT := fun _ _ => 0, io := fun _ => 0, ioT := fun _ _ => 0
     sBF := fun j ρ h => FamInhab.mkStep _ _ (hc.ωY t j (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes j ρ h).d)
       (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j ρ h).d) (g.vol (j + 1)) ρ ρ
     sFB := fun j σ h => FamInhab.mkStep _ _ (hc.ωY t (j + 1) (by omega)) (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.jac j (σ + 1) h).d)
       (GlobalTheory.Unf.Inhab.even_im_hermitian_sub (g.bes (j + 1 + 1) σ (idx_step h)).d) (g.vol (j + 1 + 1)) (σ + 1) σ }⟩

end GlobalTheory.Fam.MidLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopStandardCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.TopDatumTheta

open GlobalTheory.LocMod.StepVec
open GlobalTheory.FunObj.Comparison₂ (IsRed)

section Gen

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_moved (p : Place D k) (GS : Frame k S.rank Y') (GT : Frame k T.rank Y) (g : GA D S) (h : GA D T) (x : WO S T) :
    p.down (moved p GS g) (moved p GT h) (actO S T g h x) = p.down GS GT x := by
  have h1 : (Formalism.L2.Theta.mt T h⁻¹).map p.π * (Formalism.L2.Theta.mt T h).map p.π = 1 := by
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  have h2 : (Formalism.L2.Theta.mt S g⁻¹).map p.π * (Formalism.L2.Theta.mt S g).map p.π = 1 := by
    rw [← Matrix.map_mul]
    simp [Formalism.L2.Theta.mt]
  unfold Place.down moved
  rw [GlobalTheory.VacMove.actO_eq, Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((Formalism.L2.Theta.mt T h⁻¹).map p.π), h1, Matrix.one_mul,
    ← Matrix.mul_assoc ((Formalism.L2.Theta.mt S g⁻¹).map p.π), h2, Matrix.one_mul]

theorem coords_moved (p : Place D k) (GS : Frame k S.rank Y') (GT : Frame k T.rank Y) {π' : Datum.EAf D →+* k}
    (hπ : ∀ a, π' (toEAf D a) = p.π a) {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (LS : LatFrame k ι' Y') (LT : LatFrame k ι Y) (ea : ι' ≃ Fin S.rank) (eb : ι ≃ Fin T.rank)
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {g : GA D S} {h : GA D T}
    (mS : MovedTo p S g βS ((GS.β * LS.bas.val).submatrix id fun i => LS.ord (ea.symm i)))
    (mT : MovedTo p T h βT ((GT.β * LT.bas.val).submatrix id fun i => LT.ord (eb.symm i))) (x : WO S T) :
    LT.coords LS (p.down GS GT x) = ((frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x)).map π').submatrix eb ea := by
  rw [← coords_down p _ _ hπ LS LT ea eb (map_eq_of_movedTo _ GS hπ _ _ mS) (map_eq_of_movedTo _ GT hπ _ _ mT), down_moved]

theorem isHalf_actO_iff {e : AE D} (g : GA D S) (h : GA D T) (x : WO S T) : IsHalf e (actO S T g h x) ↔ IsHalf e x :=
  ⟨fun H => by
    have := GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ H
    rwa [GlobalTheory.SplitHecke.actO_inv_actO] at this, GlobalTheory.SplitHecke.isHalf_actO g h⟩

theorem part_int (q : GlobalTheory.FinPl.SplitPt D k) {π' : Datum.EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = q.pr a)
    (hint : ∀ z : Datum.EAf D, z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      (1 - toEAf D q.e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' z ∈ 𝒪[k]) {z : Datum.EAf D} (hz : π' z ∈ 𝒪[k]) :
    toEAf D q.e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hee : q.e * q.e = q.e := q.split.1
  have h1 : q.pr q.e = 1 := by
    have a := (ofSplit q).ι_π 1
    have b := (ofSplit q).π_ι ((ofSplit q).π 1)
    rw [a, mul_one, map_one] at b
    exact b
  refine (hint _).2 ⟨?_, ?_⟩
  · rw [← mul_assoc, sub_mul, one_mul, ← map_mul, hee, sub_self, zero_mul]
    exact zero_mem _
  · rwa [map_mul, hπ, h1, one_mul]

theorem sum_part_mem {R R' ι : Type} [CommRing R] [CommRing R'] [Fintype ι] (φ : R →+* R') (A : Subring R') (a : ι → R) (z : R')
    (h : ∀ i, φ (a i) * z ∈ A) : φ (∑ i, a i) * z ∈ A := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  exact sum_mem fun i _ => h i

theorem idem_eq {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n : ℕ} (a : Fin n → AE D)
    (pl : Fin n ≃ P) (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i).1) : e = ∑ i, a i := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P, ← Equiv.sum_comp pl]
  exact Finset.sum_congr rfl fun i _ => (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ _ _ (hes _ (pl i).2) (ha i)).1 rfl

end Gen

section Fam

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} {f : FamCh W u}
  {v : VCom f.c}



end Fam


end GlobalTheory.TopDatumTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtraProjectionLevelCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StepLevelP

theorem eq_mul_of_inv_mul {a b c d : ℂ} (ha : a ≠ 0) (h : a⁻¹ * b = c * d) : b = a * c * d := by
  rw [mul_assoc, ← h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

theorem mul_eq_of {a c d u v p q : ℂ} (h1 : u = a * p) (h2 : v = c * d * q) : u * v = a * (c * d) * (p * q) := by
  rw [h1, h2]; ring

theorem const_eq {a b c I : ℂ} (hb : b ≠ 0) : a * b⁻¹ * (b * c) * I = c * a * I := by
  field_simp


set_option maxHeartbeats 800000 in
theorem ioX_levChi_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ)
    (hL : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hc : R.IsChain) (t : T)
    (F : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) (hF : F.1 ∈ CXP R P t) (κ : GA D (Yc D (D.R.m - 1)))
    (hκ : κ ∈ levS (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P)) (φ x g) :
    (R.ioX t F).1 (R.ItX φ x) (g * κ) =
      levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ * (R.ioX t F).1 (R.ItX φ x) g := by
  have hθ : IsInfFam R.θ := hm.inf
  have hio := hc.ioX t
  have hκG : κ ∈ GfC (Yc D (D.R.m - 1)) := hκ.1
  have hκP : Lev.finE (Yc D (D.R.m - 1)) κ ∈ parLev D.sp.cm (Yc D (D.R.m - 1)).gram (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) := hκ.2.1
  have hκH : rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ) ∈ P.H := hκ.2.2
  have hκl : IsLevelLift (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv)
      (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ)) κ := ⟨hκG, hκP, rfl⟩
  refine (GlobalTheory.Fam.FamInhab.lifts_top (R := R) hL t
    (rTup (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) R.triv) (Lev.finE (Yc D (D.R.m - 1)) κ))).elim fun κ' hκ' => ?_
  have hlaw := GlobalTheory.StepLaw.last_step_law R hL hθ hc.ωX hc.vX t _ κ κ' hκl hκ'
  have hsS : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ ≠ 0 := levChi_ne_zero _ _
  have hsT : levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' ≠ 0 := levChi_ne_zero _ _
  have hlaw' : (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ)⁻¹ •
      R.ωX t (κ, κ') (R.vX t) =
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ • R.vX t := hlaw
  have hv : R.ωX t (κ, κ') (R.vX t) =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ *
        (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.vX t := by
    rw [mul_smul, ← hlaw', smul_smul, mul_inv_cancel₀ hsS, one_smul]
  have hpt := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ _ _ _ _ (R.ωX t) hθ (hc.ωX t)
    _ _ _ _ (R.vX t) (hc.ptX t) κ hκG κ' hκ'.1 _ hv φ
  have hker := GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ _ _ _ _ (R.ωX t) (hc.ωX t)
    (R.ptX t φ) (hc.ptX t φ)
  have e1 : levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (R.datYt t (D.R.m - 1) P) κ =
      ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ := by
    unfold levChi
    erw [levFn_withP (L := R.datYt t (D.R.m - 1) R.triv) P, extendOne_of_mem _ hκH, Units.val_mul]
    rfl
  have hfd : (R.νX t).IsHaarMeasure ∧ IsFundamentalDomain (GQ D.sp.X') (R.fdX t) (R.νX t) :=
    ⟨(hm.νX t).1.1, (hm.νX t).2⟩
  have hi := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable D.sp.X'
  haveI i1 := hi.1
  haveI i2 := hi.2.1
  haveI i3 := hi.2.2.1
  haveI i4 := hi.2.2.2
  have htg : IsTopologicalGroup (GA D D.sp.X') := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    exact inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig D.sp.X'.gram))
  haveI := hfd.1
  haveI hR : (R.νX t).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hfd.1
  have hmap : Measure.map (fun h => h * κ') (R.νX t) = R.νX t := map_mul_right_eq_self _ κ'
  have hFv := (GlobalTheory.StepLevelP.IoLevPf.multT_val R.θ R.MX _ _ F.1 hF x).1
  have hF1 := ((GlobalTheory.Fam.FamInhab.cxp_iff P t F.1).1 hF).2 ⟨_, hκH⟩ κ' hκ' x
  have hF2 : ∀ h, F.1 x (h * κ') =
      levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ) * F.1 x h := fun h =>
    eq_mul_of_inv_mul hsT (hF1 h)
  have hpt' : R.ωX t (κ, κ') (R.ptX t φ) = (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹) • R.ptX t φ := hpt
  have hth := hker.2 κ κ' _ hpt'
  have hint := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ D.sp.X') (R.νX t)
    (R.fdX t) hfd.2 κ' hmap
    (fun h => thetaKO (R.ωX t) (g * κ) h (R.ptX t φ) * F.1 x h)
    (fun γ hγ h => by
      have h1 := hker.1 1 (GQ (Yc D (D.R.m - 1))).one_mem γ hγ (g * κ) h
      rw [one_mul] at h1
      simp only [h1, hFv γ hγ h])
    (hio.integ F φ x (g * κ))
  have hpw : ∀ h, thetaKO (R.ωX t) (g * κ) (h * κ') (R.ptX t φ) * F.1 x (h * κ') =
      (levChi (Yc D (D.R.m - 1)) (R.βY (D.R.m - 1)) (flagL (R.datYt t (D.R.m - 1) R.triv)) κ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ')⁻¹ * (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ' * ((P.chi ⟨_, hκH⟩ : ℂˣ) : ℂ))) * (thetaKO (R.ωX t) g h (R.ptX t φ) * F.1 x h) := fun h => by
    exact mul_eq_of (hth g h) (hF2 h)
  refine (hio.eq F φ x (g * κ)).symm.trans (hint.2.symm.trans ?_)
  refine (congrArg (fun f => ∫ h in R.fdX t, f h ∂(R.νX t)) (funext hpw)).trans ((integral_const_mul _ _).trans ?_)
  refine (const_eq hsT).trans ?_
  exact congrArg₂ (· * ·) e1.symm (hio.eq F φ x g)

end GlobalTheory.StepLevelP

end
end
