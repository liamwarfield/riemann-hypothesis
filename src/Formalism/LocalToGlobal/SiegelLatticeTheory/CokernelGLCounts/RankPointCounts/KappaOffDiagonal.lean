module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SupportProposition
public import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RrExistsMeasRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

def frq (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) :=
  mapLF q.1.2 (lf D (X.Fu u'))

def fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Submodule D.host.E (VS D).V :=
  (lf D (X.Fu u)).fl.Xplus ⊔ (frq X q).fl.Xplus

def pointwiseStabilizerInfinite (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Set X.B.I.Ginf :=
  Hset X.B.I (X.crd '' (fixedSubspaceOfRepresentative X q : Set (VS D).V))

end Defs

def RelRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    t.relevant → t.G = 0 →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl ∧ Gval (lf D (X.Fu u)) (frq X t.rep) = 0

def CovRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl →
    ∀ Ω : Set X.B.I.Ginf, IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' q.1.2) Ω →
    OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1 →
    ∀ h ∈ pointwiseStabilizerInfinite X q,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       (X.piU u h).comp (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1) =
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1).comp
          (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1)))

def SchurNFC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    (∀ τ, uS D u τ ≠ uS D u' τ) →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ P : X.Vpi u' →L[ℂ] X.Vpi u,
      (∀ h ∈ pointwiseStabilizerInfinite X q, (X.piU u h).comp P = P.comp (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1))) → P = 0

section Asm

variable {D : D7} {X : HidaSetting D}

theorem words_differ {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) {u u' : D.what₂.Word} (huu : u ≠ u') :
    ∀ τ, uS D u τ ≠ uS D u' τ := by
  exact h.1.2.1.2.2.2.2.2.2.2.1 u u' huu

theorem aTerm_eq_zero_of_OOt {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    (t : GTerm X u u' F0 F0' what₂ rows') (h : OOt t = 0) : aTerm cs cs' FdN FdN' t = 0 := by
  have hb : ∀ ρ ρ', blk cs cs' FdN FdN' t ρ ρ' = 0 := by
    intro ρ ρ'
    simp [blk, h]
  ext φ : 1
  simp [aTerm, aTermL, hb]
  try rfl

theorem fundOf_spec {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hF : FundExists X u u' F0 F0' what₂ rows') (t : GTerm X u u' F0 F0' what₂ rows') :
    IsSFund X.B.I (ROinf t) (FundOf t) := by
  unfold FundOf
  split_ifs with h0
  · exact h0.choose_spec
  · exact absurd (hF t) h0

end Asm

end Formalism.L2.SG.KappaOffDiagonal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstA
noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.RealObj Formalism.MainNotions.S.LocalSplitGroups

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section LinAlg

variable {r : ℕ}

theorem Dl_scale (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Formalism.L2.SG.RealObj.Dl (r := r) (fun a b => c a * Z a b * c b) l = (∏ a : Fin l, c (Fin.castLE hl a)) ^ 2 * Formalism.L2.SG.RealObj.Dl Z l := by
  simp only [Formalism.L2.SG.RealObj.Dl, dif_pos hl]

  have h : Matrix.submatrix (fun a b => c a * Z a b * c b : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.of (fun i j => c (Fin.castLE hl i) *
        Matrix.of (fun i j => c (Fin.castLE hl j) * (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) i j) i j) := by
    ext i j
    show c (Fin.castLE hl i) * Z (Fin.castLE hl i) (Fin.castLE hl j) * c (Fin.castLE hl j) =
      c (Fin.castLE hl i) * (c (Fin.castLE hl j) * Z (Fin.castLE hl i) (Fin.castLE hl j))
    ring
  rw [h, Matrix.det_mul_column, Matrix.det_mul_row]
  ring

theorem Gv_scale (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : Fin (r + 1) → ℂ)
    (hc : c (Fin.last r) = 1) :
    Formalism.L2.SG.RealObj.Gv T T' (fun a b => c a * Z a b * c b) = ‖∏ a : Fin r, c a.castSucc‖ ^ 4 * Formalism.L2.SG.RealObj.Gv T T' Z := by
  have h1 := Dl_scale Z c (r + 1) (le_refl (r + 1))
  have h0 := Dl_scale Z c r (Nat.le_succ r)
  have hp1 : (∏ a : Fin (r + 1), c (Fin.castLE (le_refl (r + 1)) a)) = ∏ a : Fin r, c a.castSucc := by
    rw [Fin.prod_univ_castSucc]
    show (∏ a : Fin r, c a.castSucc) * c (Fin.last r) = _
    rw [hc, mul_one]
  have hp0 : (∏ a : Fin r, c (Fin.castLE (Nat.le_succ r) a)) = ∏ a : Fin r, c a.castSucc := rfl
  simp only [Formalism.L2.SG.RealObj.Gv]
  rw [h1, h0, hp1, hp0, norm_mul, norm_mul, norm_pow]
  ring

private theorem norm_Dl_ZhatO_eq_norm_Dl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (l : ℕ) :
    ‖Formalism.L2.SG.RealObj.Dl (Formalism.L2.SG.RealObj.ZhatO Z) l‖ = ‖Formalism.L2.SG.RealObj.Dl Z l‖ := by
  simp only [Formalism.L2.SG.RealObj.Dl]
  split_ifs with hl
  · have h : ((Formalism.L2.SG.RealObj.ZhatO Z).submatrix (Fin.castLE hl) (Fin.castLE hl)) =
        Matrix.of (fun i j => (-1 : ℂ) ^ (r - (Fin.castLE hl j).1) *
          (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)) i j) := by
      ext i j
      rfl
    rw [h, Matrix.det_mul_row, norm_mul]
    simp
  · rfl

theorem Gv_zhatO (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Formalism.L2.SG.RealObj.Gv T T' (Formalism.L2.SG.RealObj.ZhatO Z) = Formalism.L2.SG.RealObj.Gv T T' Z := by
  simp only [Formalism.L2.SG.RealObj.Gv, norm_Dl_ZhatO_eq_norm_Dl]

end LinAlg

section Scale

theorem sum_range_sub_two (r : ℕ) : (∑ i ∈ Finset.range r, (r - i)) * 2 = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [add_mul, ih]
    ring

theorem sum_sub_two (r : ℕ) : (∑ a : Fin r, (r - a.1)) * 2 = r * (r + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - i) r]
  exact sum_range_sub_two r

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ZX_scale (u u' : D.what₂.Word) (sc : ℝ) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    ZX X u u' sc γ v = fun a b => ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹ * ZX X u u' 1 γ v a b * ((sc : ℂ) ^ (D.R.rS - b.1))⁻¹ := by
  funext a b
  simp [ZX, Formalism.L2.SG.RealObj.Zhat, frm, famSc, Formalism.L2.SG.HidaSetting.hJ, Matrix.mulVec_smul, star_smul]
  ring

theorem GX_scale (u u' : D.what₂.Word) {sc : ℝ} (hsc : 0 < sc) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    GX X u u' sc γ v = (sc ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ * GX X u u' 1 γ v := by
  have hc : ((sc : ℂ) ^ (D.R.rS - (Fin.last D.R.rS).1))⁻¹ = 1 := by simp
  have hG := Gv_scale (Tw u) (Tw u') (ZX X u u' 1 γ v) (fun a => ((sc : ℂ) ^ (D.R.rS - a.1))⁻¹) hc
  beta_reduce at hG
  simp only [GX]
  rw [ZX_scale X u u' sc γ v, hG]
  congr 1
  have hn : ‖∏ a : Fin D.R.rS, ((sc : ℂ) ^ (D.R.rS - (Fin.castSucc a).1))⁻¹‖ =
      (sc ^ (∑ a : Fin D.R.rS, (D.R.rS - a.1)))⁻¹ := by
    rw [norm_prod]
    simp only [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsc, Fin.coe_castSucc]
    rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  have hS : (∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 4 = 2 * D.R.rS * (D.R.rS + 1) := by
    have h2 := sum_sub_two D.R.rS
    calc (∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 4 = ((∑ a : Fin D.R.rS, (D.R.rS - a.1)) * 2) * 2 := by ring
      _ = 2 * D.R.rS * (D.R.rS + 1) := by rw [h2]; ring
  rw [hn, inv_pow, ← pow_mul, hS]

end Scale

section Pt

theorem prod_normSq_embS (D : D7) (x : D.host.E) :
    ∏ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ x‖ ^ 2 = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have := Formalism.MainNotions.InterlacingSignCuts.host_totallyComplex D
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [Formalism.MainNotions.InterlacingSignCuts.prod_places D] at h
  rw [← h]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩, Formalism.MainNotions.InterlacingSignCuts.plOf_apply]
  rfl

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ptC_eq (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    ptC X v w = (ptMat w).map (Formalism.MainNotions.S.embS D (X.pl v)) := by
  simp only [ptC, X.φ_eq, RingEquiv.apply_symm_apply]

theorem Dl_ptC (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    Formalism.L2.SG.RealObj.Dl (ptC X v w) l = Formalism.MainNotions.S.embS D (X.pl v) (Dmin w l) := by
  rw [ptC_eq]
  simp only [Formalism.L2.SG.RealObj.Dl, dif_pos hl, Dmin]
  rw [RingHom.map_det]
  rfl

private theorem embS_conjF_eq_conj_embS (τ : D.what₂.Tau) (x : D.host.E) :
    Formalism.MainNotions.S.embS D τ (D.conjF x) = starRingEnd ℂ (Formalism.MainNotions.S.embS D τ x) :=
  Formalism.L2.SG.Pf.emb_conjF τ x

theorem Gv_ptC (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (w : Point D.host.E (D.R.rS + 1)) :
    Gv (Tw u) (Tw u') (ptC X v w) =
      (Formalism.MainNotions.S.embS D (X.pl v) (Gpt (D.mem u).A.T (D.mem u').A.T w)).re := by
  simp only [Gv]
  rw [Dl_ptC X v w (D.R.rS + 1) le_rfl, Dl_ptC X v w D.R.rS (Nat.le_succ _)]
  simp only [Gpt, map_sub, map_mul, map_natCast, embS_conjF_eq_conj_embS, Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, Tw]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_re]

theorem embS_GPoint_im (τ : D.what₂.Tau) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).im = 0 := by
  simp only [Gpt, map_sub, map_mul, map_natCast, embS_conjF_eq_conj_embS, Complex.mul_conj]
  simp

end Pt

section Prod

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem card_places : Fintype.card (InfinitePlace X.B.I.F) = D.R.f := by
  rw [Fintype.card_congr X.pl, D.what₂.card_Tau]

theorem isPtRep_gamW {u u' : D.what₂.Word} {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, IsPtRep X u u' w γ) :
    IsPtRep X u u' w (gamW X u u' w) := by
  simp only [gamW, dif_pos h]
  exact h.choose_spec

theorem GX_gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (h : ∃ γ, IsPtRep X u u' w γ)
    (v : InfinitePlace X.B.I.F) :
    GX X u u' D.host.rdE (gamW X u u' w) v = (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹ *
      (Formalism.MainNotions.S.embS D (X.pl v) (Gpt (D.mem u).A.T (D.mem u').A.T w)).re := by
  rw [GX_scale X u u' (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) (gamW X u u' w) v]
  congr 1
  simp only [GX]
  rw [← Gv_zhatO, isPtRep_gamW X h v, Gv_ptC]

theorem prod_re_embS_GPoint (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (hT : TotPos (Gpt T T' w)) :
    ∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re =
      Real.sqrt ((|Algebra.norm ℚ (Gpt T T' w)| : ℚ) : ℝ) := by
  have hpos : ∀ τ : D.what₂.Tau, 0 < (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re := fun τ => hT τ
  have hnorm : ∀ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ (Gpt T T' w)‖ = (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re := by
    intro τ
    have e : Formalism.MainNotions.S.embS D τ (Gpt T T' w) = ((Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re : ℂ) := by
      apply Complex.ext <;> simp [embS_GPoint_im τ T T' w]
    rw [congrArg norm e, Complex.norm_real, Real.norm_of_nonneg (hpos τ).le]
  calc ∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re
      = Real.sqrt ((∏ τ : D.what₂.Tau, (Formalism.MainNotions.S.embS D τ (Gpt T T' w)).re) ^ 2) :=
        (Real.sqrt_sq (Finset.prod_nonneg fun τ _ => (hpos τ).le)).symm
    _ = Real.sqrt (∏ τ : D.what₂.Tau, ‖Formalism.MainNotions.S.embS D τ (Gpt T T' w)‖ ^ 2) := by
        rw [← Finset.prod_pow]
        simp only [hnorm]
    _ = _ := by rw [prod_normSq_embS]

theorem prod_GX_gamW (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (h : ∃ γ, IsPtRep X u u' w γ)
    (hT : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w)) :
    ∏ v, GX X u u' D.host.rdE (gamW X u u' w) v =
      ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1)))⁻¹) ^ D.R.f *
        Real.sqrt ((|Algebra.norm ℚ (Gpt (D.mem u).A.T (D.mem u').A.T w)| : ℚ) : ℝ) := by
  simp only [GX_gamW X u u' w h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_places]
  congr 1
  rw [← prod_re_embS_GPoint _ _ w hT]
  exact Fintype.prod_equiv X.pl _ _ (fun v => rfl)

end Prod

end Formalism.L2.SG.WConst
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FiniteLevelVolumeOfMeasure
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Chi2ApplyOne
noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Vol

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

def FiniteLevelVolumeEquality : Prop := (X.measG.μGf (levelUnitary X hb)).toReal = (X.B.μf X.K2).toReal

def CovolTie : Prop :=
  covolBy (G := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
    (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG =
    X.B.I.vol X.B.μf X.B.fund

theorem chi2_apply_one (hK : X.LevelSubgroupCharacter) : X.chi2 1 = 1 := by
  obtain ⟨h1, -, -, hmul, hnorm⟩ := hK
  have hm := hmul 1 h1 1 h1
  simp only [mul_one] at hm
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem e_one_re (hK : X.LevelSubgroupCharacter) : (X.B.e 1).re = ((X.B.μf X.K2).toReal)⁻¹ := by
  have h := X.e_eq 1
  have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
  change X.B.e 1 = if (1 : X.B.I.Gf) ∈ X.K2 then star (X.chi2 1) / ((X.B.μf X.K2).toReal : ℂ) else 0 at h
  rw [if_pos h1, chi2_apply_one X hK, star_one] at h
  rw [h, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]

end Vol

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) (h2 : FiniteLevelVolumeEquality X hb) (h3 : CovolTie X) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X := by
  unfold Formalism.FourierDecayAlt.S3.MassData.Dstar Formalism.L2.SG.RowsConc.DstC Formalism.MainNotions.S.AutInst.Dstar
  rw [e_one_re X hK]
  have hdeg : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).deg =
      Formalism.MainNotions.PlaceDegreeData.fdegAll X.B.I X.B.σ X.B.w := rfl
  have hvol : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG =
      covolBy (G := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) X.measG.μG := rfl
  have hkpp : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKpp =
      (bOf X hb hK FdN FdN' u u' X0 L A).μKpp := rfl
  rw [hdeg, hvol, h3, hkpp, hKpp hH, h2]
  ring

end Formalism.L2.SG.IntegralApproximation
end
end

noncomputable section

namespace Formalism.L2.SG.IntegralApproximation

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped Classical TensorProduct

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem finiteLevelVolume_of_measure (hM : X.MeasTie hb) : FiniteLevelVolumeEquality X hb := by
  unfold FiniteLevelVolumeEquality
  rw [hM.2.2.1]
  haveI : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  let e := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).toHomeomorph.toMeasurableEquiv
  have he : (X.toFin hb : X.B.I.Gf → _) = e := rfl
  have hK : levelUnitary X hb = e '' X.K2 := rfl
  rw [hK, he, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]

theorem mem_rr_iff (x : X.B.I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ↔
      toHA X.B.I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I (toHA X.B.I hb) (toHA_isBridge X.B.I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      h ∈ ratHA X.B.I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA X.B.I hb).injective hyx]

theorem covolTie_of (hM : X.MeasTie hb) : CovolTie X := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' X.B.I X.B.μf
  haveI : (X.B.I.muA X.B.μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) X.B.fund (X.B.I.muA X.B.μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨X.B.fund_spec.1, X.B.fund_spec.2.1, X.B.fund_spec.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
  let e := (toHA X.B.I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I :=
    { toFun := fun g => ⟨(toHA X.B.I hb).symm (g : HA _ _ _), (mem_rr_iff X hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA X.B.I hb x, (mem_rr_iff X hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  haveI : Countable Γ := Function.Injective.countable eΓ.injective
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((X.B.I.muA X.B.μf).map e) (X.B.I.muA X.B.μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' X.B.fund) X.measG.μG := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : X.B.I.GA) * x) = (g : HA _ _ _) * e x
    show toHA X.B.I hb ((toHA X.B.I hb).symm g * x) = (g : HA _ _ _) * toHA X.B.I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  have hmap : X.measG.μG (e '' X.B.fund) = X.B.I.muA X.B.μf X.B.fund := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ, MeasurableEquiv.map_apply, Set.preimage_image_eq _ e.injective]
  haveI : (X.measG.μG).IsHaarMeasure := by
    have hμ : X.measG.μG = (X.B.I.muA X.B.μf).map e := hM.1
    rw [hμ]
    exact (toHA X.B.I hb).isHaarMeasure_map (X.B.I.muA X.B.μf)
  haveI : (X.measG.μG).IsMulLeftInvariant := inferInstance
  haveI : MeasurableConstSMul Γ (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    ⟨fun c => (continuous_const_mul (c : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J)).measurable⟩
  unfold CovolTie covolBy
  split_ifs with h
  · have h1 : IsFundamentalDomain Γ h.choose X.measG.μG := h.choose_spec
    rw [h1.measure_eq hfd, hmap]
    rfl
  · exact absurd ⟨_, hfd⟩ h

section MassData

open Formalism.L2.SG.MassDataConc Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups

variable (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

theorem MassDataDstarX_holds (L : LocIn (TypX X)) (A : AnIn) (hH : HypX X hb FdN FdN' u u')
    (hKpp : KppVolAt X hb hK FdN FdN' u u' X0 L A) :
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Dstar = Formalism.L2.SG.RowsConc.DstC X :=
  MassDataDstarX X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq L A hH hKpp (finiteLevelVolume_of_measure X hb hH.1)
    (covolTie_of X hb hH.1)

end MassData

end Formalism.L2.SG.IntegralApproximation
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCells
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CellRelIff
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def Ak : Subgroup K := S.subgroupOf K

def πk (hD : Data W S N' K π) : K →* Ak S K where
  toFun k := ⟨⟨π k, hD.kπ k k.2⟩, by show π k ∈ S; exact hD.mem k⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

theorem πk_id (hD : Data W S N' K π) (a : Ak S K) : πk W S N' K π hD a = a := by
  obtain ⟨⟨x, hxK⟩, hxS⟩ := a
  have hxS' : x ∈ S := by simpa [Ak, Subgroup.mem_subgroupOf] using hxS
  ext
  simp [πk, hD.id x hxS']

def Hk : Subgroup K := (Hs W K g).subgroupOf K

theorem cellRel_iff (hD : Data W S N' K π) (k₁ k₂ : K) :
    (cellRel W N' K g).r (toCell W S N' K π g hD k₁) (toCell W S N' K π g hD k₂) ↔
      ∃ n ∈ (πk W S N' K π hD).ker, ∃ h ∈ Hk W K g, k₂ = n * k₁ * h := by
  show cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ ∈ K ⊓ N' ↔ _
  constructor
  · rintro ⟨hK, hN⟩
    set x := cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ with hx
    refine ⟨⟨x, hK⟩, ?_, k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      have h1 : π x = 1 := (hD.ker x).1 hN
      ext
      simp [πk, h1]
    · rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]
      refine ⟨(k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have e2 := cell_smul W S N' K π hD ((k₂ : G) * g)
      have e1 := cell_smul W S N' K π hD ((k₁ : G) * g)
      calc ((k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂ : K) : G) • g • W
          = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • ((cell π ((k₂ : G) * g))⁻¹ • (((k₂ : G) * g) • W)) := by
            rw [← mul_smul, ← mul_smul, ← mul_smul]
            congr 1
            push_cast
            rw [hx]
            group
        _ = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • W := by rw [← e2, inv_smul_smul]
        _ = g • W := by rw [mul_smul, e1, ← mul_smul]; simp
    · ext
      push_cast
      group
  · rintro ⟨n, hn, h, hh, rfl⟩
    have hπn : π (n : G) = 1 := by
      rw [MonoidHom.mem_ker] at hn
      have := congrArg (fun a : Ak S K => ((a : K) : G)) hn
      simpa [πk] using this
    have hh' : (h : G) • g • W = g • W := by
      rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf] at hh
      exact hh.2
    have hs : g⁻¹ * (h : G) * g ∈ S := by
      rw [← hD.stab]
      rw [mul_smul, mul_smul, hh', ← mul_smul]
      simp
    have key : cell π (((n * k₁ * h : K) : G) * g) = (n : G) * cell π ((k₁ : G) * g) := by
      have e : ((n * k₁ * h : K) : G) * g = (n : G) * ((k₁ : G) * g) * (g⁻¹ * (h : G) * g) := by
        push_cast
        group
      simp only [cell]
      rw [e, map_mul, map_mul, hπn, hD.id _ hs]
      group
    rw [key, mul_inv_cancel_right]
    exact ⟨n.2, (hD.ker n).2 hπn⟩

end Formalism.L2.SG.Pf.CountAb
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def cellEquiv (hD : Data W S N' K π) :
    Quotient (Setoid.ker (Formalism.L2.SG.Pf.ProdEP2Core.dcMap (Ak S K) (πk W S N' K π hD) (Hk W K g))) ≃
      Quotient (cellRel W N' K g) := by
  refine Equiv.ofBijective (Quotient.lift (fun k => (⟦toCell W S N' K π g hD k⟧ : Quotient (cellRel W N' K g)))
    (fun k₁ k₂ h => ?_)) ⟨?_, ?_⟩
  · apply Quotient.sound
    exact (cellRel_iff W S N' K π g hD k₁ k₂).2
      ((Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).1 h)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h k₁ =>
      induction y using Quotient.inductionOn with
      | h k₂ =>
        apply Quotient.sound
        have h2 := Quotient.exact hxy
        exact (Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).2
          ((cellRel_iff W S N' K π g hD k₁ k₂).1 h2)
  · intro y
    induction y using Quotient.inductionOn with
    | h c =>
      obtain ⟨k, rfl⟩ := toCell_surj W S N' K π g hD c
      exact ⟨⟦k⟧, rfl⟩

theorem card_cells (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hk W K g).map (πk W S N' K π hD)).index := by
  rw [← Nat.card_congr (cellEquiv W S N' K π g hD)]
  exact Formalism.L2.SG.Pf.ProdEP2Core.card_dc (Ak S K) (πk W S N' K π hD) (Hk W K g) (πk_id W S N' K π hD)

end Formalism.L2.SG.Pf.CountAb
end
end
