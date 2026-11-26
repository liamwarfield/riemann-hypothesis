module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOneEqOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FlagOfUpUni

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.Pf.MainEqCut

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Pf.MainEqSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abs

variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

def ScalEquivOn (X : PB.Terms τ Rw I H H₁) : Prop :=
  (∀ t ∈ X.genSet, X.s0 t t = 1 ∧ X.scal t t) ∧
  (∀ t ∈ X.genSet, ∀ t' ∈ X.genSet, X.rowOf t = X.rowOf t' → X.s0 t t' = 1 → X.scal t t' →
    X.s0 t' t = 1 ∧ X.scal t' t) ∧
  (∀ t ∈ X.genSet, ∀ t' ∈ X.genSet, ∀ t'' ∈ X.genSet, X.rowOf t = X.rowOf t' → X.rowOf t' = X.rowOf t'' →
    X.s0 t t' = 1 → X.scal t t' → X.s0 t' t'' = 1 → X.scal t' t'' → X.s0 t t'' = 1 ∧ X.scal t t'')

end Abs

section Conc

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

theorem classInputG_of (h : ScalEquivOn (Y.tO u u)) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf)
    (ng : PN.Pts D.host.E D.R.rS → ℝ) : PN.ClassInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) := by
  obtain ⟨hrefl, hsymm, htrans⟩ := h
  have hset : ∀ t, t ∈ (genT (Y.tO u u)).ngSet ↔ t ∈ (Y.tO u u).genSet := fun t => by
    simp [PB.Terms.ngSet, PB.Terms.genSet, genT]
  have hs0 : ∀ t t', (genT (Y.tO u u)).s0 t t' = 1 ↔
      (Y.tO u u).s0 t t' = 1 ∧ (Y.tO u u).scal t t' := fun t t' => by
    simp only [genT]
    split_ifs with hc <;> simp [hc]
  intro t ht t' ht'
  rw [hset] at ht ht'
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (genT (Y.tO u u)).s0 t t' = 1) ↔
    clsG Y u t = clsG Y u t'
  rw [hs0]
  constructor
  · rintro ⟨hrow, hs, hsc⟩
    obtain ⟨hs', hsc'⟩ := hsymm t ht t' ht' hrow hs hsc
    ext t''
    simp only [clsG, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hg, hr, h1, h2⟩
      exact ⟨hg, hr.trans hrow, htrans t' ht' t ht t'' hg hrow.symm hr.symm hs' hsc' h1 h2⟩
    · rintro ⟨hg, hr, h1, h2⟩
      exact ⟨hg, hr.trans hrow.symm, htrans t ht t' ht' t'' hg hrow hr.symm hs hsc h1 h2⟩
  · intro hcl
    have hmem : t' ∈ clsG Y u t' := ⟨ht', rfl, (hrefl t' ht').1, (hrefl t' ht').2⟩
    rw [← hcl] at hmem
    simp only [clsG, Set.mem_setOf_eq] at hmem
    obtain ⟨-, hr, h1, h2⟩ := hmem
    exact ⟨hr.symm, h1, h2⟩

def AmpVanishG (νL : X.B.I.Ginf → Measure X.B.I.Ginf) : Prop :=
  ∀ c γ ν, J2of Y u u νL γ = 0 → grpGC Y u c γ ν = 0

theorem ampInputG_of_vanish (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (h : AmpVanishG Y u νL) : PN.AmpInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) := by
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => by
    unfold J2of
    split_ifs <;> positivity
  refine ⟨fun c γ ν => div_nonneg (sq_nonneg _) (hJ γ), fun γ => hJ γ, fun c γ ν => ?_⟩
  have hset : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := by
    ext t
    simp [PB.Terms.ngSet, PB.Terms.genSet, genT]
  have hg : PN.grp (genT (Y.tO u u)) (NOfG Y u νL νB ng) c γ ν = grpGC Y u c γ ν := by
    unfold PN.grp grpGC
    rw [hset]
    rfl
  rw [hg]
  change ‖grpGC Y u c γ ν‖ ^ 2 ≤ a2GC Y u νL c γ ν * J2of Y u u νL γ
  unfold a2GC
  rcases (hJ γ).eq_or_lt with h0 | hpos
  · rw [h c γ ν h0.symm, norm_zero]
    simp
  · rw [div_mul_cancel₀ _ hpos.ne']

end Conc

def StepClassG : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), (∀ i, 3 ≤ D.host.g i) → ConcTie X Y →
    ScalEquivOn (Y.tO u u)

def StepNormalsG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.NormalsInput (genT (Y.tO u u)) (NOfG Y u νL νB ng)
          ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
            (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ)) ^ (6 * D.R.f))

def StepPointsG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.PointsInput (genT (Y.tO u u)) (NOfG Y u νL νB ng)

def StepHeightG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ),
        PN.HeightInput (genT (Y.tO u u)) (NOfG Y u νL νB ng) ((X.B.g : ℝ) ^ D.R.f)

def StepNormOneG : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS),
        PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ∧ 1 ≤ NDPt D.host.rdE γ

theorem stepHeightG_of_normOne (h : StepNormOneG) : StepHeightG := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C'₀, Cl₀, hC⟩ := h Cg cb Cw cT CT C0
  refine ⟨C'₀, Cl₀, fun C' Cl h1 h2 D large₂ X Y u hc νL νB ng γ hγ => ?_⟩
  obtain ⟨hG, hD⟩ := hC C' Cl h1 h2 D large₂ X Y u hc νL νB ng γ hγ
  refine ⟨hG, hD, ?_⟩
  have key : ((X.B.g : ℝ) ^ ((2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E)))⁻¹ ≤
      (X.B.g : ℝ) ^ D.R.f := by
    rcases Nat.eq_zero_or_pos X.B.g with h0 | hpos
    · have hN : 0 < (2 * D.R.rS + 1) * Fintype.card (InfinitePlace D.host.E) :=
        Nat.mul_pos (by omega) Fintype.card_pos
      rw [h0, Nat.cast_zero, zero_pow hN.ne', inv_zero]
      positivity
    · have hg : (1 : ℝ) ≤ X.B.g := by exact_mod_cast hpos
      exact (inv_le_one_of_one_le₀ (one_le_pow₀ hg)).trans (one_le_pow₀ hg)
  change HPt D.host.rdE (X.B.g : ℝ) ((Tu D u : ℕ) * (Tu D u : ℕ)) γ ≤
    (X.B.g : ℝ) ^ D.R.f * NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ * NDPt D.host.rdE γ
  unfold HPt
  have hGD : 0 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u : ℕ)) γ * NDPt D.host.rdE γ := by
    have := mul_le_mul hG hD zero_le_one (zero_le_one.trans hG)
    linarith
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right key hGD

theorem g_ge_three {Cg cb Cw cT CT C0 C' Cl : ℝ} {D : D7} {large₂ : SizeData₂ D} {X : HidaSetting D} {Y : Full X}
    {u u' : D.what₂.Word} (hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u') :
    ∀ i, 3 ≤ D.host.g i := by
  obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
  unfold Formalism.MainNotions.S.StandingHypotheses at hH
  dsimp only at hH
  obtain ⟨-, -, h3, h4, -, -, -, -, -, -, h11, h12, h13, h14, h15, h16, -, -, h19, -, -, -, h23, -, h25⟩ := hH
  have hm2 := D.R.two_le_m
  have hk16 : (16 : ℝ) ≤ D.R.k := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    have : 16 ≤ D.R.k := by omega
    exact_mod_cast this
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb : 1 < large₂.sc.b := by
    unfold Formalism.BasicNotions.Scale.b
    have := Real.add_one_lt_exp (ne_of_gt hL); linarith
  have hkb : (3 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (16 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    exact le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) this 8)
  intro i
  fin_cases i
  · exact_mod_cast hkb.trans h12
  · exact_mod_cast hkb.trans h14

end Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqSteps

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ChartC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundX
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem box_fundX {ι P : Type} [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (A : P → AddSubgroup (ι → ℂ)) (F : P → Set (ι → ℂ)) (hFd : ∀ p (v : ι → ℂ), ∃! a : A p, (a : ι → ℂ) + v ∈ F p)
    (x : ι → P → ℂ) :
    ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p} := by
  classical
  let w : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)
  let c : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ =>
    ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ
  have hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ' := by
    intro p γ γ' hg
    have h1 : τ p γ = τ p γ' := hτ p γ γ' hg
    have h2 : w p γ = w p γ' := by
      show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)
      rw [h1]
      congr 1
      funext v
      rw [hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]
    have hch : ∀ u u' : ι → ℂ, u = u' →
        ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ) := by
      rintro u _ rfl
      rfl
    show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'
    rw [h1, hch _ _ h2]
  have key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔
      (fun v => γ v p) = c p γ := by
    intro p γ
    obtain ⟨a, ha, huniq⟩ := hFd p (w p γ)
    have hc : c p γ = (a : ι → ℂ) + τ p γ := by
      show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ
      rw [huniq _ (hFd p (w p γ)).exists.choose_spec]
    have hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ := by
      funext v
      simp only [lawX, w, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hc, hlaw]
    constructor
    · rintro ⟨hA, hF⟩
      have e := congrArg Subtype.val (huniq ⟨_, hA⟩ hF)
      simp only at e
      rw [← e]
      abel
    · intro hg
      rw [hg, add_sub_cancel_right]
      exact ⟨a.2, ha⟩
  let Φ : (ι → P → ℂ) → (ι → P → ℂ) := fun γ v p => c p γ v
  have hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p := by
    intro k
    induction k with
    | zero => intro γ γ' p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro γ γ' p hp v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v
      rw [hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]
  have hN : ∀ p, h p < Finset.univ.sup h + 1 := fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))
  have hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ := by
    intro γ
    rw [Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]
    constructor
    · intro H
      funext v p
      exact (congrFun (H p) v).symm
    · intro H p
      funext v
      exact (congrFun (congrFun H v) p).symm
  refine ⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩
  · rw [← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]
    funext v p
    exact hit _ (Φ 0) 0 p (hN p) v
  · have e1 : Φ^[Finset.univ.sup h + 1] γ = γ := Function.iterate_fixed ((hcond γ).1 hγ) _
    funext v p
    calc γ v p = (Φ^[Finset.univ.sup h + 1] γ) v p := by rw [e1]
      _ = _ := hit _ γ 0 p (hN p) v

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ht {D : D7} {w : Point D.host.E (D.R.rS + 1)} (p : Formalism.L2.SG.RealObj.FreeE w) : ℕ := p.1.2.val - p.1.1.val

def ChartC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∃ BX : Formalism.L2.SG.RealObj.FreeE w → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → ℂ,
        (∀ p, Measurable (fun z : (Formalism.L2.SG.RealObj.FreeE w → ℂ) × (Formalism.L2.SG.RealObj.FreeE w → ℂ) => BX p z.1 z.2)) ∧
        (∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, ht q < ht p → x q = x' q ∧ y q = y' q) →
          BX p x y = BX p x' y') ∧
        (∀ p (x : Formalism.L2.SG.RealObj.FreeE w → ℂ), BX p x 0 = 0) ∧
        Measurable (Formalism.L2.SG.RealObj.stCoord X u' w γw) ∧
        MeasurableSet (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        Set.InjOn (Formalism.L2.SG.RealObj.stCoord X u' w γw) (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        (∀ x, ∃ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, Formalism.L2.SG.RealObj.stCoord X u' w γw z = x) ∧
        (∀ z₁ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, ∀ z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw,
          z₁ * z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw ∧
          Formalism.L2.SG.RealObj.stCoord X u' w γw (z₁ * z₂) =
            lawX BX (Formalism.L2.SG.RealObj.stCoord X u' w γw z₁) (Formalism.L2.SG.RealObj.stCoord X u' w γw z₂)) ∧
        (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, s⁻¹ * r * s ∈ Formalism.L2.SG.RealObj.StInf X u u' γw)

end Formalism.L2.SG.NGCut.StabilizerCovolume
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem witt_tuple {ι : Type} [Fintype ι] (x y : ι → S.V) (hx : LinearIndependent E x) (hy : LinearIndependent E y)
    (hG : ∀ i j, S.hT (x i) (x j) = S.hT (y i) (y j)) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ ∀ i, g (x i) = y i := by
  set U := Submodule.span E (Set.range x) with hU
  let b : Basis ι E U := Basis.span hx
  have hb : ∀ i, (b i : S.V) = x i := fun i => by
    show ((Basis.span hx i : U) : S.V) = x i
    rw [Basis.span_apply]
  let f : U →ₗ[E] S.V := b.constr E y
  have hfu : ∀ u : U, f u = ∑ i, b.equivFun u i • y i := fun u => b.constr_apply_fintype E y u
  have hu : ∀ u : U, (u : S.V) = ∑ i, b.equivFun u i • x i := by
    intro u
    have := congrArg Subtype.val (b.sum_repr u)
    rw [← this, Submodule.coe_sum]
    simp only [Submodule.coe_smul, hb, Basis.equivFun_apply]
  have hexp : ∀ (z : ι → S.V) (c d : ι → E), S.hT (∑ i, c i • z i) (∑ j, d j • z j) =
      ∑ i, ∑ j, star (c i) * d j * S.hT (z i) (z j) := by
    intro z c d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hiso : ∀ u v : U, S.hT (f u) (f v) = S.hT u v := by
    intro u v
    rw [hfu, hfu, hu u, hu v, hexp, hexp]
    simp only [hG]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu0
    rw [LinearMap.mem_ker, hfu] at hu0
    have hc := Fintype.linearIndependent_iff.1 hy _ hu0
    refine (Submodule.mem_bot E).2 (Subtype.ext ?_)
    rw [hu u]
    simp [hc]
  obtain ⟨g, hg, hgf⟩ := witt_extension_theorem E S.V S.hT (fun x y => (hT_swap x y).symm)
    (fun x hx => S.nondeg.1 x hx) U f hinj hiso
  refine ⟨g, hg, fun i => ?_⟩
  have := hgf (b i)
  rw [hb] at this
  rw [this]
  exact b.constr_basis E y i

def tupMU (F : FlagG S r T) (F1 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Fin (r + 1) ⊕ Fin (r + 1) → S.V :=
  Sum.elim (fun a => ∑ c, M c a • F.fvec c) (fun b => ∑ c, U c b • F1.fvec c)

theorem gram_moved (F : FlagG S r T) (F1 F2 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hM : IsUpUni M) (hU : IsUpUni U) (hZ : Zhat F F2 = Mᴴ * Zhat F F1 * U) :
    ∀ i j, S.hT (tupMU F F1 M U i) (tupMU F F1 M U j) =
      S.hT (Sum.elim F.fvec F2.fvec i) (Sum.elim F.fvec F2.fvec j) := by
  have hexp : ∀ (z w : Fin (r + 1) → S.V) (c d : Fin (r + 1) → E), S.hT (∑ i, c i • z i) (∑ j, d j • w j) =
      ∑ i, ∑ j, star (c i) * d j * S.hT (z i) (w j) := by
    intro z w c d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hFF : ∀ (G : FlagG S r T) c d, S.hT (G.fvec c) (G.fvec d) =
      if c = Fin.last r ∧ d = Fin.last r then -T else 0 := fun G c d => by
    have := brS_fvec G d c
    simp only [brS] at this
    rw [this]
    by_cases h1 : c = Fin.last r <;> by_cases h2 : d = Fin.last r <;> simp [h1, h2]
  have hFF' : ∀ (G : FlagG S r T') c d, S.hT (G.fvec c) (G.fvec d) =
      if c = Fin.last r ∧ d = Fin.last r then -T' else 0 := fun G c d => by
    have := brS_fvec G d c
    simp only [brS] at this
    rw [this]
    by_cases h1 : c = Fin.last r <;> by_cases h2 : d = Fin.last r <;> simp [h1, h2]
  have hdiag : ∀ (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : IsUpUni A) (t : E) (a b : Fin (r + 1)),
      ∑ i, ∑ j, star (A i a) * A j b * (if i = Fin.last r ∧ j = Fin.last r then t else 0) =
        if a = Fin.last r ∧ b = Fin.last r then t else 0 := by
    intro A hA t a b
    simp only [mul_ite, mul_zero, ite_and]
    rw [Finset.sum_eq_single (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · simp only [if_true, upUni_last hA]
      by_cases h1 : a = Fin.last r <;> by_cases h2 : b = Fin.last r <;> simp [h1, h2]
    · intro j _ hj; simp [hj]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  have hcross : ∀ a b, S.hT (tupMU F F1 M U (Sum.inl a)) (tupMU F F1 M U (Sum.inr b)) = S.hT (F.fvec a) (F2.fvec b) := by
    intro a b
    simp only [tupMU, Sum.elim_inl, Sum.elim_inr]
    rw [hexp]
    have h2 : S.hT (F.fvec a) (F2.fvec b) = Zhat F F2 a b := rfl
    rw [h2, hZ, Matrix.mul_apply]
    simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [Zhat, brS]
    ring
  intro i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [tupMU, Sum.elim_inl]
    rw [hexp]
    simp only [hFF]
    exact hdiag M hM (-T) a b
  · exact hcross a b
  · rw [hT_swap, hcross b a, ← hT_swap]
    rfl
  · simp only [tupMU, Sum.elim_inr]
    rw [hexp]
    simp only [hFF']
    exact hdiag U hU (-T') a b

theorem tupMU_indep (F : FlagG S r T) (F1 : FlagG S r T') (M U : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hM : IsUpUni M) (hU : IsUpUni U) (hG : Gflag F F1 ≠ 0) : LinearIndependent E (tupMU F F1 M U) := by
  have hli := PI.PairCorankPos.W.linIndep F F1 hG
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have hsum : ∑ i, g i • tupMU F F1 M U i =
      ∑ s, (Sum.elim (M *ᵥ fun a => g (Sum.inl a)) (U *ᵥ fun b => g (Sum.inr b)) s) •
        Sum.elim F.fvec F1.fvec s := by
    simp only [Fintype.sum_sum_type, tupMU, Sum.elim_inl, Sum.elim_inr, Finset.smul_sum, smul_smul, mulVec,
      dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => (U x y * g (Sum.inr y)) • F1.fvec x)]
    congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_ <;> rw [mul_comm]
  rw [hsum] at hg
  have h0 := hli _ hg
  have hMd : M.det ≠ 0 := by rw [upUni_det hM]; exact one_ne_zero
  have hUd : U.det ≠ 0 := by rw [upUni_det hU]; exact one_ne_zero
  have hl : (fun a => g (Sum.inl a)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hMd (funext fun a => h0 (Sum.inl a))
  have hr : (fun b => g (Sum.inr b)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hUd (funext fun b => h0 (Sum.inr b))
  intro s
  rcases s with a | b
  · exact congrFun hl a
  · exact congrFun hr b

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
