module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralFiniteCombination
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwisted
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapHandedFunctionVanishingPeriodInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopVol

theorem volLev_ne_zero_of_isCompact {D : D7} (V : HSp D) (hK : IsCompact (GinfC V : Set (GA D V))) (v : GlobalTheory.Unf.Vol V)
    (U : Subgroup (GA D V)) (hle : U ≤ GfC V) (hc : IsCompact (U : Set (GA D V)))
    (ho : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))) : GlobalTheory.SeeSaw.volLev v U ≠ 0 := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hvol : GlobalTheory.SeeSaw.volLev v U = (v.μ K).toReal := by
    unfold GlobalTheory.SeeSaw.volLev
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hc
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho' : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      ho.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho'
    show g ∈ (K : Set (GA D V))
    rw [hKset]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  rw [hvol]
  exact (ENNReal.toReal_pos hKpos.ne' hKfin).ne'

end GlobalTheory.TopVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

namespace GlobalTheory.TopVol.InKConj

variable {D : D7}

theorem idAt_le_of {P : Pl D → Prop} {v : Pl D} (hv : P v) : idAt D (· = v) ≤ idAt D P := by
  intro a ha
  rw [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun h => w.2 (h ▸ hv)⟩⟩

theorem moves_at {V : HSp D} {g : GA D V} {M : Lat V} {P : Pl D → Prop} (h : Moves V g M M P) {v : Pl D} (hv : P v) :
    Moves V g M M (· = v) := by
  intro y hy
  have hy' : ∀ i, y i ∈ idAt D P := fun i => idAt_le_of hv (hy i)
  rw [KOpen.mem_latV_iff V M _ y hy, KOpen.mem_latV_iff V M _ _ (KOpen.supp_mulVec V _ g hy),
    ← KOpen.mem_latV_iff V M P y hy', ← KOpen.mem_latV_iff V M P _ (KOpen.supp_mulVec V P g hy')]
  exact h y hy'

theorem conj_mem_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ M : Lat V) (Ld : LevDat D.host.E ℂ V.rank)
    (P : Pl D → Prop) (t κ : GA D V) (hβ : IsFrame β Λ) (hΛ : IsSelfDualC V Λ) (ht : t ∈ GfC V)
    (hm : ∀ v, P v → Moves V t Λ M (· = v)) (hQ : Ld.Q = ∅)
    (hPg : ∀ PP ∈ Ld.Pg, ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) (hκ : InK V M P κ) :
    t⁻¹ * κ * t ∈ Lev.levG V β Ld := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfg : Λ.FG := Submodule.IsLattice.fg (A := D.host.E) Λ
  obtain ⟨hκf, hκ1⟩ := (KOpen.mem_grpAt_iff V P κ).1 hκ.1
  have hy : t⁻¹ * κ * t ∈ GfC V := (GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem ht) hκf) ht
  have hproj : ∀ v, ¬ P v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (t⁻¹ * κ * t) = 1 := fun v hv => by
    rw [map_mul, map_mul, hκ1 v hv, mul_one, map_inv, inv_mul_cancel]
  have hSt : Lev.finE V (t⁻¹ * κ * t) ∈ St β := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ]
    intro v
    by_cases hv : P v
    · rw [← GlobalTheory.StMoves.moves_iff_stabLoc V Λ hfg v]
      exact (GlobalTheory.StMoves.moves_conj_iff κ (hm v hv)).2 (moves_at hκ.2 hv)
    · rw [hproj v hv]; exact Subgroup.one_mem _
  have hred : ∀ PP ∈ Ld.Pg, redFn β PP (Lev.finE V (t⁻¹ * κ * t)) = 1 := fun PP hP =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt (hproj _ (hPg PP hP))
  refine ⟨hy, mem_lev.2 ⟨mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSt, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩⟩
  · rw [hred PP hP]; exact Subgroup.one_mem _
  · rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  · have e : rTup β Ld (Lev.finE V (t⁻¹ * κ * t)) = 1 := by
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 _) = 1
      rw [hred PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [e]; exact Subgroup.one_mem _

end GlobalTheory.TopVol.InKConj

namespace GlobalTheory.TopVol.InKConj

end GlobalTheory.TopVol.InKConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProof
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl

namespace GlobalTheory.SeeSaw.VacShape

theorem nonempty_pl (D : D7) : Nonempty (Pl D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField D.host.F)⟩⟩

theorem vacOfShape : ∀ D : D7, GlobalTheory.SeeSaw.VacOfShape D := by
  intro D c v k _ _ _ _ ι o hc hv hs t
  obtain ⟨x₀⟩ := nonempty_pl D
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D c.ψ (· ∉ v.tP)
  have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hc.std
  refine ⟨?_, ?_⟩
  · intro j σ h Ψ₁ Ψ₂ h₁ h₂
    have f₁ := hFV.1 (σ + 1) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (t.sBF j (σ + 1) h) (v.N j) (o.M j (σ + 1) h)
      (v.N (j + 1)) (c.x (j + 1)).L (fun x _ => (hs.good x).bf j (σ + 1) h) Ψ₁ h₁
    have f₂ := hFV.2.1 σ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sFB j σ h) (v.N (j + 1)) (c.x (j + 1)).L
      (v.N (j + 1 + 1)) (o.M (j + 1 + 1) σ (idx_step h)) (fun x _ => (hs.good x).fb j σ h) Ψ₂ h₂
    have hg0 := (hs.good x₀).bf j (σ + 1) h
    have hg1 := (hs.good x₀).fb j σ h
    have hor : ∀ x, x ∉ v.tP → (∃ LL, OrthAt (c.B j (σ + 1) h).o (o.M j (σ + 1) h) (c.x j).L LL x) ∧
        ∃ LL, OrthAt (c.B (j + 1 + 1) σ (idx_step h)).o (o.M (j + 1 + 1) σ (idx_step h)) (c.x (j + 1 + 1)).L LL x := by
      intro x hx
      obtain ⟨LL, _, hLL⟩ := (hs.split x hx).core j (σ + 1) h
      obtain ⟨LL', _, hLL'⟩ := (hs.split x hx).core (j + 1 + 1) σ (idx_step h)
      exact ⟨⟨LL, hLL⟩, ⟨LL', hLL'⟩⟩
    exact (hCC (σ + 1) σ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h)
      _ _ f₁.1 f₂.1).2.2 (· ∉ v.tP) (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (o.M j (σ + 1) h)
      (o.M (j + 1 + 1) σ (idx_step h)) (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd hg0.sdV₀ hg1.sdW₀ hor f₁ f₂
  · intro j h Ψ₁ Ψ₂ h₁ h₂
    have f₁ := hFV.1 0 (c.B j 0 h) (c.J j 0 h) (t.sBF j 0 h) (v.N j) (o.M j 0 h) (v.N (j + 1)) (c.x (j + 1)).L
      (fun x _ => (hs.good x).bf j 0 h) Ψ₁ h₁
    have f₂ := hFV.2.2 (c.V (j + 1)) (c.X (j + 1)) c.T (c.jac j 0 h).d (v.N (j + 1)) (c.x (j + 1)).L v.NT
      (hv.sd (j + 1) (by omega)) (hc.x (j + 1) (by omega)).sd hv.sdT (fun x _ => ((hs.good x).bf j 0 h).monoW) Ψ₂ h₂
    have hg0 := (hs.good x₀).bf j 0 h
    exact GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both D c.ψ hc.std _ (c.X j) _ (c.X (j + 1)) (c.X (j + 1 + 1)) c.T c.Lz (c.bes j 0 h).o
      (c.oT (j + 1 + 1) h) (v.τ j h) (c.bes j 0 h).line.1 hs.pre.line.1 (hs.pre.tau j h) (· ∉ v.tP) (o.M j 0 h)
      (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L v.NT hg0.sdV₀ (hc.x j (by omega)).sd (hc.x (j + 1) (by omega)).sd
      (hc.x (j + 1 + 1) (by omega)).sd hv.sdT (fun x hx => ⟨((hs.good x).bf j 0 h).tame, (hs.split x hx).top j h⟩)
      _ _ f₁ f₂

end GlobalTheory.SeeSaw.VacShape

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedVacuaOfShapeProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof : ∀ D : D7, GlobalTheory.SeeSaw.VacOfShape D := by
  first | exact @GlobalTheory.SeeSaw.VacShape.vacOfShape | exact GlobalTheory.SeeSaw.VacShape.vacOfShape | (intros; apply GlobalTheory.SeeSaw.VacShape.vacOfShape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.QPl.EpsSupp

theorem exists_prod_of_mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

theorem eps_mem_grpAt {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ)
    (h0 : ∀ i β, (F.Q i).εL 0 β = Finsupp.single 1 1) (j : ℕ) (α : t.Ch j) :
    ∀ g ∈ ((F.pinTup sc cT).ε j α).support, g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ (F.pinTup sc cT).Q) := by
  classical
  intro g hg
  dsimp only [QFam.pinTup] at hg ⊢
  split_ifs at hg with hc
  · have hg' := Finsupp.support_smul hg
    obtain ⟨x, hx, rfl⟩ := exists_prod_of_mem_support_conv _ _ g hg'
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    have hP : (F.Q i).q.v ∈ Finset.univ.image fun i => (F.Q i).q.v := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    rcases hc with ⟨ρ, hρ⟩ | hj
    · obtain ⟨e, -, he⟩ := (F.Q i).εL_at j ρ hρ (2 * ρ) (by have := (F.Q i).hs; omega) (F.eqv j α i)
      have hxi := hx i
      rw [he] at hxi
      obtain ⟨a, -, hax⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hxi)
      rw [← hax]
      exact GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D _ (F.Q i).q _ _ ((F.Q i).gl_loc _ _ _ a).1 _ hP
    · subst hj
      have hxi := hx i
      rw [h0] at hxi
      have h1 := Finsupp.support_single_subset hxi
      rw [Finset.mem_singleton] at h1
      rw [h1]
      exact one_mem _
  · simp at hg

end GlobalTheory.QPl.EpsSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryJointTwistValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

namespace GlobalTheory.QPl.PinComb

variable {D : D7} {c : Comm D}

def mxSub (P : GlobalTheory.FinPl.Pl D → Prop) (S T : HSp D) : AddSubmonoid (WO S T) where
  carrier := {u | GlobalTheory.FinPl.MxAt P u}
  zero_mem' := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  add_mem' {a b} ha hb := fun i j => by
    simpa using (GlobalTheory.FinPl.idAt D P).add_mem (ha i j) (hb i j)

theorem combAt_aconv {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (l : List (WO S T →₀ ℂ))
    (hl : ∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (aconv l) :=
  GlobalTheory.QPl.ThetaPin.aconv_support (mxSub P S T) l hl

theorem combAt_smul {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} (r : ℂ) {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P (r • e) :=
  fun u hu => he u (Finsupp.support_smul hu)

theorem combAt_zero {P : GlobalTheory.FinPl.Pl D → Prop} {S T : HSp D} : GlobalTheory.FinPl.CombAt P (0 : WO S T →₀ ℂ) :=
  fun u hu => by simp at hu

theorem combAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ p, P p → P' p) {S T : HSp D} {e : WO S T →₀ ℂ}
    (he : GlobalTheory.FinPl.CombAt P e) : GlobalTheory.FinPl.CombAt P' e :=
  fun u hu => GlobalTheory.DisjComb.mxAt_mono h (he u hu)

theorem combAt_of_isCombAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {q : GlobalTheory.FinPl.SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {FS : Frame k S.rank Y'} {FT : Frame k T.rank Y}
    {e : WO S T →₀ ℂ} {Ξ : Matrix Y Y' k → ℂ} (h : (ofSplit q).IsCombAt ψ FS FT e Ξ) : GlobalTheory.FinPl.CombAt (· = q.v) e :=
  fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D k q u (h.1 u hu)

variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

theorem eL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eL j) := by
  obtain ⟨d, hd⟩ : ∃ d, j + d = Q.s := ⟨Q.s - j, by omega⟩
  exact combAt_of_isCombAt (Q.eL_at j d hd)

theorem eT_combAt (Q : QAt v χ) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.eT j h) := by
  have hj : j = Q.s := by have := Q.hs; omega
  subst hj
  exact combAt_of_isCombAt Q.eLT_at

theorem dL_combAt (Q : QAt v χ) (j : ℕ) (hj : j ≤ Q.s + 1) (α : Q.Ch j) (γ : Q.Ch (j + 1)) :
    GlobalTheory.FinPl.CombAt (· = Q.q.v) (Q.dL j α γ) := by
  rcases Nat.lt_or_ge j Q.s with h | h
  · obtain ⟨d, hd⟩ : ∃ d, j + 1 + d = Q.s := ⟨Q.s - (j + 1), by omega⟩
    exact combAt_of_isCombAt (Q.dL_mid j d hd α γ)
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      exact combAt_of_isCombAt (Q.dL_pen α γ)
    · have h'' : j = Q.s + 1 := by omega
      subst h''
      exact combAt_of_isCombAt (Q.dL_top α γ)

theorem pinTup_combAt {t : Tup c} (F : QFam v t) (sc cT : ℕ → ℂ) (j : ℕ) :
    GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQ j) ∧
      (∀ h, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).eQT j h)) ∧
      ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) ((F.pinTup sc cT).dQ j α γ) := by
  have hQ : ∀ i, (F.Q i).q.v ∈ (F.pinTup sc cT).Q := fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hmono : ∀ i {S T : HSp D} {e : WO S T →₀ ℂ}, GlobalTheory.FinPl.CombAt (· = (F.Q i).q.v) e →
      GlobalTheory.FinPl.CombAt (· ∈ (F.pinTup sc cT).Q) e :=
    fun i _ _ _ he => combAt_mono (fun p hp => hp ▸ hQ i) he
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨?_, fun h => ?_, fun α γ => ?_⟩
  · show GlobalTheory.FinPl.CombAt _ (if j + 1 < D.R.m then aconv (List.ofFn fun i => (F.Q i).eL j) else 0)
    split_ifs with hj
    · refine combAt_aconv _ fun e he => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (eL_combAt _ j (by have := hs i; omega))
    · exact combAt_zero
  · show GlobalTheory.FinPl.CombAt _ (aconv (List.ofFn fun i => (F.Q i).eT j h))
    refine combAt_aconv _ fun e he => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
    exact hmono i (eT_combAt _ j h)
  · show GlobalTheory.FinPl.CombAt _ (if j < D.R.m then
      (∏ i, (F.Q i).wt j (F.eqv j α i)) • aconv (List.ofFn fun i => (F.Q i).dL j (F.eqv j α i) (F.eqv (j + 1) γ i)) else 0)
    split_ifs with hj
    · refine combAt_smul _ (combAt_aconv _ fun e he => ?_)
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 he
      exact hmono i (dL_combAt _ j (by have := hs i; omega) _ _)
    · exact combAt_zero

end GlobalTheory.QPl.PinComb


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePair
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwMovedVal


set_option maxHeartbeats 4000000 in
theorem moves_rep_tw : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} (A : TwDat I l Z u a Ch), A.Is → ∀ (j : ℕ) (hj : j ≤ B.R.m) (c : (I.stp u a j).Cl) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), finM _ (rankN (I.rec7 l Z) j hj) g = ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 → Moves _ (rankN (I.rec7 l Z) j hj) g ((I.stp u a j).rep c).1.1.deco.1.N := by
  intro B X I l Z u a Ch A hA j hj c g hg
  have h1 := ((hA.reads j hj).pt c).lat
  have h2 := ((hA.base j hj (A.chOf j c)).1).lat
  rw [extTo_deco] at h1 h2
  rw [(hA.base j hj (A.chOf j c)).2] at h2
  have hinv : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ = ((((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1)⁻¹ : GL _ _).1 := by
    have e1 : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ * ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 = 1 := by
      rw [← hg, ← GlobalTheory.RepLattice.finM_mul', inv_mul_cancel, GlobalTheory.RepLattice.finM_one']
    rw [← Matrix.mul_one (finM _ _ g⁻¹), ← Units.mul_inv (((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1), ← Matrix.mul_assoc, e1,
      Matrix.one_mul]
  intro x
  rw [hinv]
  let p := ((I.stp u a j).rep c).1.1
  have hspan : Submodule.span B.fields.E (p.deco.1.N : Set (Formalism.L2.Col.Sp B.fields.E (B.R.N j))) = ⊤ := by
    open Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col in
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply le_antisymm ?_ bot_le
    intro f hf
    let v := fun i => star (f (Pi.single i 1))
    have hpair : hStd B.fields.E _ v = f := by
      apply (Pi.basisFun B.fields.E _).ext
      intro i
      rw [Pi.basisFun_apply, hStd_apply, Finset.sum_eq_single i]
      · simp [v]
      · intro j _ hj
        simp [hj]
      · simp
    have hline (r : B.fields.E) : r • v ∈ p.deco.1.N := by
      rw [← show dual (hStd B.fields.E _) p.deco.1.N = p.deco.1.N from p.deco.2.uni, dualBasic_mem_dual]
      intro y hy
      have hy0 : hStd B.fields.E _ v y = 0 := by
        rw [hpair]
        exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
      have hz : hStd B.fields.E _ y v = 0 := by
        simpa [hy0] using ((hStd_isSymm (E := B.fields.E)).eq v y).symm
      simp [hz]
    have hv : v = 0 := by
      funext i
      change v i = 0
      by_contra hi
      let coord := (LinearMap.proj i : (Formalism.L2.Col.Sp B.fields.E (B.R.N j)) →ₗ[B.fields.E] B.fields.E).restrictScalars (𝓞 B.fields.E)
      have htop : p.deco.1.N.map coord = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨(x / v i) • v, hline _, div_mul_cancel₀ _ hi⟩
      have : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.finite_def.mpr (htop ▸ p.deco.2.lat.fg.map coord)
      exact RingOfIntegers.not_isField B.fields.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E))
    rw [Submodule.mem_bot]
    simpa [hv] using hpair.symm
  have hfull : Submodule.IsFullLattice B.fields.E p.deco.1.N :=
    { toIsLattice := p.deco.2.lat, span_eq_top := hspan }
  exact GlobalTheory.RepLattice.mem_iff_of_carries _ _ _ hfull h1 h2 x


set_option maxHeartbeats 1600000 in
theorem moved_datum_val_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}), Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (A.h i α c) ((I.stp u a i).rep c.1).1.1.deco.1.N ∧ Moves _ (rankN (I.rec7 l Z) (i + 1) hi) (A.h (i + 1) γ c') ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N ∧ ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, Φ (actO _ _ (A.h i α c)⁻¹ (A.h (i + 1) γ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = p * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hOk hP l Z u a Ch A hA i hi α γ Φ hΦ p hΦv c c'
  obtain ⟨c, rfl⟩ := c
  obtain ⟨c', rfl⟩ := c'
  obtain ⟨hg, hy⟩ := hA.h i (Nat.le_of_succ_le hi) (A.chOf i c) ⟨c, rfl⟩
  obtain ⟨hg', hy'⟩ := hA.h (i + 1) hi (A.chOf (i + 1) c') ⟨c', rfl⟩
  refine ⟨moves_rep_tw A hA i _ c _ hy, moves_rep_tw A hA (i + 1) hi c' _ hy', fun z => ?_⟩
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.chartBasePair_datum_rational_approx_eq_twisted I hOk hP l Z u a Ch A hA i hi c c' _ _ hg hg' hy hy'
  obtain ⟨-, k, hk0, hkinv, -⟩ := hΦ
  obtain ⟨γ₀, v, hv, hvh, he⟩ := GlobalTheory.AdForm.exists_rat_half_approx _ _ A.e _ hA.idem (M * k) (Nat.mul_pos hM0 hk0)
    (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r))
  have hx : actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) =
      A.e • actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r) := by
    have : (z.map fun r => A.e * incA (I.rec7 l Z) r) = A.e • (z.map fun r => incA (I.rec7 l Z) r) := by
      ext a b; rfl
    simp only [actO, this, Matrix.mul_smul, Matrix.smul_mul]
  have half : ∀ (n : ℕ) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), IsHalf A.e v → IsHalf A.e (n • v) :=
    fun n v h a b => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, h a b]
  have e1 : Φ (γ₀.map fun r => A.e * incA (I.rec7 l Z) r) =
      Φ (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) := by
    rw [he, ← hx, mul_nsmul]
    exact hkinv _ (nsmul_mem hv M) (half M v hvh) _
  rw [← e1, hΦv]
  congr 1
  refine hM z γ₀ (k • v) (nsmul_mem hv k) (half k v hvh) ?_
  rw [he, ← hx, mul_nsmul']

end GlobalTheory.AdForm.TwMovedVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumEqFiniteDatumRepresentativePairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}), Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (A.h i α c) ((I.stp u a i).rep c.1).1.1.deco.1.N ∧ Moves _ (rankN (I.rec7 l Z) (i + 1) hi) (A.h (i + 1) γ c') ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N ∧ ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, Φ (actO _ _ (A.h i α c)⁻¹ (A.h (i + 1) γ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = p * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  first | exact @GlobalTheory.AdForm.TwMovedVal.moved_datum_val_tw | exact GlobalTheory.AdForm.TwMovedVal.moved_datum_val_tw | (intros; apply GlobalTheory.AdForm.TwMovedVal.moved_datum_val_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistChainIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem frGL_mul' {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) :
    Formalism.L2.DIV.frGL β y * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E n y := by
  simp [Formalism.L2.DIV.frGL]


set_option maxHeartbeats 1000000 in
theorem mul_moved (p : GlobalTheory.LocMod.Place D k) {π' : Formalism.IndefR.Lev.EAf D →+* k} (hπ : ∀ a, π' (toEAf D a) = p.π a) (V : HSp D)
    (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) {M : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : GlobalTheory.LocMod.MovedTo p V t β M) :
    (mt V x).map p.π * M = M * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have h1 := hM (β.val.map f) (Matrix.ext fun i j => hf _)
  have h2 : (β.val.map f).map p.π = β.val.map π' := Matrix.ext fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hπ, hf]; rfl
  rw [Matrix.map_mul, h2] at h1
  have h3 : Formalism.IndefR.Lev.finE V (t⁻¹ * x * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E _ y := by
    rw [← hy]
    exact frGL_mul' β y
  have h4 : (mt V (t⁻¹ * x * t)).map p.π * β.val.map π' =
      β.val.map π' * y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) := by
    have h5 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => g.val.map π') h3
    simp only [Units.val_mul, Matrix.map_mul] at h5
    have h6 : (Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)).val.map π' = (mt V (t⁻¹ * x * t)).map p.π := Matrix.ext fun i j => hπ _
    rw [h6] at h5
    exact h5
  have h7 : mt V x * mt V t = mt V t * mt V (t⁻¹ * x * t) := by
    rw [← GlobalTheory.MixModel.mt_mul, ← GlobalTheory.MixModel.mt_mul, mul_assoc, mul_inv_cancel_left]
  rw [← h1, ← Matrix.mul_assoc, ← Matrix.map_mul, h7, Matrix.map_mul, Matrix.mul_assoc, h4, Matrix.mul_assoc]


set_option maxHeartbeats 1000000 in
theorem locHom_eq {Y : Type} [Fintype Y] [DecidableEq Y] (q : SplitPt D k) {π' : Formalism.IndefR.Lev.EAf D →+* k}
    (hπ : ∀ a, π' (toEAf D a) = q.pr a) (V : HSp D) (t x : GA D V) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * x * t)) (F : GlobalTheory.LocMod.Frame k V.rank Y) (e : Y ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) :
    (GlobalTheory.LevIdx.locHom q V F x).val = (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix e e := by
  have h := mul_moved (ofSplit q) (π' := π') hπ V t x β y hy hM
  have hF : F.β = (F.β.submatrix id e.symm).submatrix id e := by
    ext i j; simp
  rw [GlobalTheory.LevIdx.locHom_val]
  generalize (y.val.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) = Yn at h ⊢
  generalize hMm : F.β.submatrix id e.symm = Mm at h hF
  have key : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) k) (B : Matrix (Fin V.rank) (Fin V.rank) k),
      A * B.submatrix id e = (A * B).submatrix id e := fun A B => by
    ext i j; simp [Matrix.mul_apply]
  have h' : (mt V x).map q.pr * Mm = Mm * Yn := h
  have h2 : (mt V x).map q.pr * F.β = F.β * Yn.submatrix e e := by
    calc (mt V x).map q.pr * F.β = (mt V x).map q.pr * Mm.submatrix id e := by rw [← hF]
      _ = ((mt V x).map q.pr * Mm).submatrix id e := key _ _
      _ = (Mm * Yn).submatrix id e := by rw [h']
      _ = Mm.submatrix id e * Yn.submatrix e e := (Matrix.submatrix_mul_equiv Mm Yn id e e).symm
      _ = F.β * Yn.submatrix e e := by rw [← hF]
  calc F.γ * (mt V x).map q.pr * F.β = F.γ * ((mt V x).map q.pr * F.β) := Matrix.mul_assoc _ _ _
    _ = F.γ * (F.β * Yn.submatrix e e) := by rw [h2]
    _ = Yn.submatrix e e := by rw [← Matrix.mul_assoc, F.γβ, Matrix.one_mul]

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_twist_levTop {s : ℕ} {τ κ : Type} [Fintype τ] [DecidableEq τ] [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ)
    (hδ : GlobalTheory.SplitWeil.IsTame δ) (ν : ℕ → kˣ →* ℂˣ) (x : GL (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2)) k) :
    x ∈ (GlobalTheory.StepData.twistChain s τ κ δ hδ ν).levTop.J ↔
      x ∈ GlobalTheory.SplitWeil.KO k _ ∧ ∀ i j, ValuativeRel.valuation k (x.val (Sum.inr i) (Sum.inl j)) < 1 := by
  have e : (GlobalTheory.StepData.LatFrame.refl k (GlobalTheory.StepData.Ix (κ ⊕ Fin (s + 1)) τ (s + 2))).conj.symm x = x := by
    rw [MulEquiv.symm_apply_eq]
    ext i j
    simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_val]
  show x ∈ ((GlobalTheory.StepData.parahoric (κ ⊕ Fin (s + 1)) (Fin (s + 2) × τ) δ hδ).toLevel.map
    (GlobalTheory.StepData.LatFrame.refl k _).conj).J ↔ _
  rw [GlobalTheory.StepData.Level.mem_map, e, GlobalTheory.StepData.mem_parahoric]
  rfl

theorem frGL_inv {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {t g : GA D V}
    {y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)}
    (hy : Formalism.L2.DIV.frGL β y = Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) :
    Formalism.L2.DIV.frGL β y⁻¹ = Formalism.IndefR.Lev.finE V (t⁻¹ * g⁻¹ * t) := by
  have e : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
  exact ((Formalism.L2.DIV.frGL β).map_inv y).trans ((congrArg (·⁻¹) hy).trans
    (((Formalism.IndefR.Lev.finE V).map_inv _).symm.trans (congrArg (Formalism.IndefR.Lev.finE V) e.symm)))


set_option maxHeartbeats 1000000 in
theorem red_iff {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] (q : SplitPt D k)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hPP : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (t g : GA D V)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (F : GlobalTheory.LocMod.Frame k V.rank (R ⊕ S)) (e : R ⊕ S ≃ Fin V.rank)
    (hM : GlobalTheory.LocMod.MovedTo (ofSplit q) V t β (F.β.submatrix id e.symm)) (r : ℕ)
    (hl : ∀ a, (e (Sum.inl a)).val < r) (hr : ∀ a, r ≤ (e (Sum.inr a)).val)
    (hst : Formalism.IndefR.Lev.finE V (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) ∈ blockTri (blk2 r) ↔
      GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ ∧
        ∀ i j, ValuativeRel.valuation k ((GlobalTheory.LevIdx.locHom q V F g).val (Sum.inr i) (Sum.inl j)) < 1 := by
  obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hPP
  obtain ⟨y, hy⟩ := hst
  have h1 := locHom_eq q hπ V t g β y hy F e hM
  have h2 := locHom_eq q hπ V t g⁻¹ β y⁻¹ (frGL_inv hy) F e hM
  have hK : GlobalTheory.LevIdx.locHom q V F g ∈ GlobalTheory.SplitWeil.KO k _ := by
    refine GlobalTheory.StepData.mem_KO.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [h1]; exact hred.int _
    · rw [← (GlobalTheory.LevIdx.locHom q V F).map_inv, h2]; exact hred.int _
  have h3 : Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V (t⁻¹ * g * t)) = Formalism.UG.bc (resS D.host.F PP) y :=
    (congrArg (Formalism.L2.DIV.redFn β PP) hy.symm).trans (redFn_frGL β PP y)
  rw [h3, mem_blockTri, h1]
  constructor
  · intro h
    refine ⟨hK, fun i j => (hred.ker _).1 (h (e (Sum.inr i)) (e (Sum.inl j)) ?_)⟩
    simp [blk2, hl j, (hr i).not_gt]
  · rintro ⟨-, h⟩ i j hij
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i
    · simp [blk2, hl i] at hij
    rcases j with j | j
    · exact (hred.ker _).2 (h i j)
    · simp [blk2, (hr i).not_gt, (hr j).not_gt] at hij


set_option maxHeartbeats 1000000 in
theorem red_iff_levTop {c : Comm D} {v : VCom c} {B : GlobalTheory.Fam.Base c} {PP : Formalism.L2.DIV.Pl D.host.E} (G : QGeo v B PP)
    (δ : G.kˣ →* ℂˣ) (hδ : GlobalTheory.SplitWeil.IsTame δ) (η : ℕ → G.kˣ →* ℂˣ) (g : GA D c.T)
    (hst : Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT) ∈ Formalism.L2.DIV.St B.βT) :
    Formalism.L2.DIV.redFn B.βT PP (Formalism.IndefR.Lev.finE c.T (B.bT⁻¹ * g * B.bT)) ∈ blockTri (blk2 D.R.r) ↔
      ∀ x, (mt c.T g).map G.q.pr = G.FT.β * Units.val x * G.FT.γ → x ∈ (G.T δ hδ η).levTop.J := by
  obtain ⟨e, he, hM⟩ := G.frameTop
  have hs := G.hs
  have hk : D.R.r = D.R.k + (G.s + 1) := by
    unfold Ranks.r
    omega
  refine (red_iff G.q PP G.idem c.T B.bT g B.βT G.FT e hM _ (fun a => ?_) (fun a => ?_) hst).trans ?_
  · rw [he, hk]
    rcases a with a | a
    · exact lt_of_lt_of_le a.2 (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left a.2 _
  · rw [he, hk]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  · refine (mem_twist_levTop δ hδ η _).symm.trans ⟨fun h x hx => ?_, fun h => h _ ?_⟩
    · obtain rfl := (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g x).1 hx
      exact h
    · exact (GlobalTheory.LevIdx.eq_locHom_iff G.q c.T G.FT g _).2 rfl

theorem levS_split (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (kP PP)ˣ →* ℂˣ) (κ : GA D V) :
    κ ∈ levS V β L ↔ κ ∈ levS V β { L with Q := ∅, xq := ξ } ∧
      ∀ PP ∈ L.Q, Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V κ) ∈ blockTri (blk2 L.r) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a, b, c, d⟩ := mem_parLev.1 h2
    exact ⟨⟨h1, mem_parLev.2 ⟨a, b, c, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, h3⟩, d⟩
  · rintro ⟨⟨h1, h2, h3⟩, d⟩
    obtain ⟨a, b, c, -⟩ := mem_parLev.1 h2
    exact ⟨h1, mem_parLev.2 ⟨a, b, c, d⟩, h3⟩

end GlobalTheory.TopAgree

namespace GlobalTheory.TopAgree


end GlobalTheory.TopAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiPrimitiveOfInverseDifferentLines
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiPrimitiveOfInverseDifferentLines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.AdaptFBIdeals

theorem primAt_lastAt_of_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  intro D ψ hψ S S₀ ρ d z L M μ v hμ hline hcol
  have hdI : dI D ≠ 0 := (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.2.2
  have hu : incA D μ⁻¹ * incA D μ = 1 := by rw [← map_mul, inv_mul_cancel₀ hμ, map_one]
  have key : ∀ 𝔞 𝔟 : FI D, 𝔞 ≠ 0 → 𝔟 ≠ 0 → 𝔟 * 𝔞⁻¹ = dI D → ∀ s ∈ idAt D (· = v),
      ((∀ a ∈ idAt D (· = v), incA D μ * a ∈ idV 𝔞 v → incA D μ * (s * a) ∈ idV 𝔟 v) ↔
        ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1) := by
    intro 𝔞 𝔟 h𝔞 h𝔟 hq s hs
    rw [← GlobalTheory.SeeSaw.DiffDual.idV_dI_iff D ψ hψ v s hs, ← hq, ← GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔞 𝔟 h𝔞 h𝔟 s hs]
    constructor
    · intro h b hb
      have hbAt := idV_supp 𝔞 v hb
      have ha : incA D μ⁻¹ * b ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ hbAt
      have hb' : incA D μ * (incA D μ⁻¹ * b) = b := by rw [← mul_assoc, mul_comm (incA D μ), hu, one_mul]
      have h2 := h _ ha (by rw [hb']; exact hb)
      rwa [mul_left_comm, hb'] at h2
    · intro h a _ hma
      rw [mul_left_comm]
      exact h _ hma
  constructor
  · intro i j hij s hs
    have hq : dI D ^ (ρ - i.1) * (dI D ^ (ρ - j.1))⁻¹ = dI D := by
      have he : ρ - i.1 = (ρ - j.1) + 1 := by have := j.2; omega
      rw [he, pow_succ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hdI), one_mul]
    rw [← key (dI D ^ (ρ - j.1)) (dI D ^ (ρ - i.1)) (pow_ne_zero _ hdI) (pow_ne_zero _ hdI) hq s hs]
    constructor
    · intro h a ha hma
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ((hcol j a ha).2 hma))
    · intro h a ha
      have haAt := supp_of_colMul d L v j a ha
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ haAt)).2 (h a haAt ((hcol j a haAt).1 ha))
  · intro i hi s hs
    rw [← key 1 (dI D) one_ne_zero hdI (by rw [inv_one, mul_one]) s hs]
    have hρi : ρ - i.1 = 1 := by omega
    constructor
    · intro h a ha hma
      rw [GlobalTheory.SeeSaw.idV_one_eq_intAt] at hma
      have h2 := (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).1 (h a ha ((hline a ha).2 hma))
      rwa [hρi, pow_one] at h2
    · intro h a ha hz
      have h2 := h a ha ((GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ((hline a ha).1 hz))
      exact (hcol i (s * a) (Ideal.mul_mem_left _ _ ha)).2 (by rwa [hρi, pow_one])

end GlobalTheory.Core.Mi.LatMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiPrimitiveOfInverseDifferentLinesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_primitive_of_inverseDifferent_lines : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L : Lat S) (M : Lat S₀) (μ : D.host.E) (v : GlobalTheory.FinPl.Pl D), μ ≠ 0 → LineAt z μ M v → (∀ i : Fin ρ, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ incA D μ * a ∈ idV (dI D ^ (ρ - i.1)) v) → PrimAt ψ d L v ∧ LastAt ψ d z L M v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines | exact GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines | (intros; apply GlobalTheory.Core.Mi.LatMatch.primAt_lastAt_of_lines <;> assumption)
end
end
