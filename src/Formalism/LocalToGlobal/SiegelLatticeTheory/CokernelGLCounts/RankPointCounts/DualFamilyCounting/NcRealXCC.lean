module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundT

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev CBlk (r : ℕ) : Type := (LsNc5.LtPair r ⊕ Fin r) ⊕ (LsNc5.LtPair r ⊕ Fin r)

def CSpc (ι : Type) (k : ℕ) {r : ℕ} : CBlk r → Type
  | Sum.inl (Sum.inl _) => ι → ℂ
  | Sum.inl (Sum.inr _) => ι → Fin (k + 1) → ℂ
  | Sum.inr (Sum.inl _) => ι → ℂ
  | Sum.inr (Sum.inr _) => ι → ℝ

section Inst

variable (ι : Type) [Fintype ι] (k : ℕ) {r : ℕ}

instance instAddCommGroupCSpc : ∀ p : CBlk r, AddCommGroup (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (AddCommGroup (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (AddCommGroup (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (AddCommGroup (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (AddCommGroup (ι → ℝ))

instance instMeasurableSpaceCSpc : ∀ p : CBlk r, MeasurableSpace (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (MeasurableSpace (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (MeasurableSpace (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (MeasurableSpace (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (MeasurableSpace (ι → ℝ))

instance instMeasurableAdd₂CSpc : ∀ p : CBlk r, MeasurableAdd₂ (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (MeasurableAdd₂ (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (MeasurableAdd₂ (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (MeasurableAdd₂ (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (MeasurableAdd₂ (ι → ℝ))

def cMeas : ∀ p : CBlk r, Measure (CSpc ι k p)
  | Sum.inl (Sum.inl _) => (volume : Measure (ι → ℂ))
  | Sum.inl (Sum.inr _) => (volume : Measure (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => (volume : Measure (ι → ℂ))
  | Sum.inr (Sum.inr _) => (volume : Measure (ι → ℝ))

instance instSigmaFiniteCMeas : ∀ p : CBlk r, SigmaFinite (cMeas ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℂ)))
  | Sum.inl (Sum.inr _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)))
  | Sum.inr (Sum.inl _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℂ)))
  | Sum.inr (Sum.inr _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℝ)))

instance instRightInvCMeas : ∀ p : CBlk r, (cMeas ι k p).IsAddRightInvariant
  | Sum.inl (Sum.inl _) => inferInstanceAs ((volume : Measure (ι → ℂ)).IsAddRightInvariant)
  | Sum.inl (Sum.inr _) => inferInstanceAs ((volume : Measure (ι → Fin (k + 1) → ℂ)).IsAddRightInvariant)
  | Sum.inr (Sum.inl _) => inferInstanceAs ((volume : Measure (ι → ℂ)).IsAddRightInvariant)
  | Sum.inr (Sum.inr _) => inferInstanceAs ((volume : Measure (ι → ℝ)).IsAddRightInvariant)

end Inst

def cHgt {r : ℕ} : CBlk r → ℕ
  | Sum.inl (Sum.inl p) => p.1.2.val - p.1.1.val
  | Sum.inl (Sum.inr b) => r + (r - b.val)
  | Sum.inr (Sum.inl p) => 2 * r + 1 + (2 * r - (p.1.1.val + p.1.2.val))
  | Sum.inr (Sum.inr a) => 2 * r + 1 + (2 * r - 2 * a.val)

section HidaSetting

variable {D : D7} (X : HidaSetting D)

def blk (u : D.what₂.Word) (s : X.B.I.Ginf) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => fun v => LsNc5.xMat X v s p.1.1 p.1.2
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < D.R.k then LsNc5.phiMat X u v s b ⟨j.val, h⟩ else LsNc5.yVec X u v s b
  | Sum.inr (Sum.inl p) => fun v => (LsNc5.mMat X v s p.1.1 p.1.2 - star (LsNc5.mMat X v s p.1.2 p.1.1)) / 2
  | Sum.inr (Sum.inr a) => fun v => (LsNc5.mMat X v s a a).im

def embV (t : D.host.E) : InfinitePlace X.B.I.F → ℂ := fun v => embS D (X.pl v) t

def rowV (u : D.what₂.Word) (x : (VS D).V) : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ := fun v j =>
  if h : j.val < D.R.k then hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (X.wfr u v ⟨j.val, h⟩)
  else hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.zR u))

def aaLb (b : Fin D.R.rS) : Set (VS D).V :=
  (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} : Set (VS D).V)

def cLat (u : D.what₂.Word) : ∀ p : CBlk D.R.rS, AddSubgroup (CSpc (InfinitePlace X.B.I.F) D.R.k p)
  | Sum.inl (Sum.inl p) => AddSubgroup.closure (embV X '' ((aaD D p.1.1 * (aaD D p.1.2)⁻¹ :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))
  | Sum.inl (Sum.inr b) => AddSubgroup.closure (rowV X u '' aaLb X b)
  | Sum.inr (Sum.inl p) => AddSubgroup.closure (embV X '' ((aaD D p.1.1 * aaD D p.1.2 :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))
  | Sum.inr (Sum.inr a) => AddSubgroup.closure ((fun t v => (embS D (X.pl v) t).im) ''
      {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
        D.host.conj t = -t})

def cVal (u : D.what₂.Word) : CBlk D.R.rS → ℝ
  | Sum.inl (Sum.inl p) => (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))
  | Sum.inl (Sum.inr b) => Tw u ^ Fintype.card (InfinitePlace X.B.I.F) *
      (2 : ℝ)⁻¹ ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.k + 1)) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ))))
  | Sum.inr (Sum.inl p) => (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))
  | Sum.inr (Sum.inr a) => |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ)))

end HidaSetting

def KapLaw : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∃ B : ∀ p : CBlk D.R.rS,
      (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) →
        CSpc (InfinitePlace X.B.I.F) D.R.k p,
    (∀ p, Measurable (fun z : (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) ×
      (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) => B p z.1 z.2)) ∧
    (∀ p (x x' y y' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q),
      (∀ q, cHgt q < cHgt p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y') ∧
    (∀ p (x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), B p x 0 = 0) ∧
    ∀ s ∈ X.NinfU u, ∀ s' ∈ X.NinfU u, blk X u (s * s') = Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u s) (blk X u s')

def KapSurj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∃ σ : (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → X.B.I.Ginf,
    Measurable σ ∧ ∀ t, σ t ∈ X.NinfU u ∧ blk X u (σ t) = t

def NOfib : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

def BlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS),
    Countable (cLat X u p) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F →
      (∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k p F = ENNReal.ofReal (cVal X u p)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCR
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RefNBox : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word),
    (Measure.pi (refNX X u)) (LsNc5.boxN X w) =
      ENNReal.ofReal ((Tw w)⁻¹ ^ (D.R.rS * Fintype.card (InfinitePlace X.B.I.F)) *
        (2 : ℝ) ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.rS * D.R.k + D.R.rS ^ 2)))

theorem refNX_haar {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) :
    IsHaarOnSet X.B.I (X.NinfU w) (Measure.pi (refNX X u)) := by
  have hR := fun v : InfinitePlace X.B.I.F => refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v)
    (X.wfr u v) (ProductExactness.zV X u v) (ProductExactness.zV X w v) (ProductExactness.Tw_pos u) (fX_ee X v) (fX_ff X v) (fX_ef X v)
    (fX_ww X u v) (fX_ew X u v) (fX_fw X u v) (fX_ez X u v) (fX_fz X u v) (frame_real_z_z_eq_neg X u v) (fX_zw X u v) (fX_ez X w v)
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v => (hR v).1
  have hco : X.NinfU w = (ProductExactness.NinfG X w : Set X.B.I.Ginf) := (ProductExactness.NinfG_coe X w).symm
  refine ⟨inferInstance, ProductExactness.PiM.pi_ne_zero _ fun v => (hR v).2.1, ?_, ?_⟩
  · rw [hco, ProductExactness.NinfG, Subgroup.coe_pi]
    exact ProductExactness.PiM.pi_conc _ _ fun v => (hR v).2.2.1
  · intro g hg
    rw [hco] at hg
    exact ProductExactness.PiM.pi_map_mul_left _ g fun v => (hR v).2.2.2 (g v) (hg v (Set.mem_univ v))

theorem covol_refN (hN : LsNc5.CovolN) (hB : RefNBox) {D : D7} (X : HidaSetting D) (u w : D.what₂.Word)
    (FdN : Set X.B.I.Ginf) (hF : IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X w) FdN) :
    ((Measure.pi (refNX X u)) FdN).toReal = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent D.R.rS D.R.k := by
  rw [hN D X w _ FdN (refNX_haar X u w) hF, hB X u w]
  set f := Fintype.card (InfinitePlace X.B.I.F) with hf
  set r := D.R.rS with hr
  set k := D.R.k with hk
  have hT : 0 < Tw (D := D) w := ProductExactness.Tw_pos w
  have hd : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have h2r : 2 * (r * (r - 1) / 2) + 2 * (r * (r + 1) / 2) = 2 * r ^ 2 := by
    have e1 : 2 * (r * (r - 1) / 2) = r * (r - 1) := Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
    have e2 : 2 * (r * (r + 1) / 2) = r * (r + 1) := Nat.mul_div_cancel' (Nat.even_mul_succ_self r).two_dvd
    rw [e1, e2]
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      ring
  have hsum : r * (r - 1) / 2 + r * (r + 1) / 2 = r ^ 2 := by omega
  unfold LsNc5.covolN
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [show ((D.mem w).A.T : ℕ) = Tw (D := D) w from rfl]
  have hpow : (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
      (2 : ℝ) ^ (f * (r * k + r ^ 2)) = 1 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← hsum]
    rw [show f * (r * k + (r * (r - 1) / 2 + r * (r + 1) / 2)) =
      f * (r * k + r * (r - 1) / 2) + f * (r * (r + 1) / 2) by ring, pow_add]
    have h1 : (0 : ℝ) < 2 ^ (f * (r * k + r * (r - 1) / 2)) := by positivity
    have h2 : (0 : ℝ) < 2 ^ (f * (r * (r + 1) / 2)) := by positivity
    field_simp
  have hTp : (Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hT.ne', one_pow]
  calc (Tw (D := D) w : ℝ) ^ (r * f) * (2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
        ((Tw (D := D) w)⁻¹ ^ (r * f) * (2 : ℝ) ^ (f * (r * k + r ^ 2)))
      = ((Tw (D := D) w : ℝ) ^ (r * f) * (Tw (D := D) w)⁻¹ ^ (r * f)) *
        ((2 : ℝ) ^ (-((f * (r * k + r * (r - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (f * (r * (r + 1) / 2)) *
          (2 : ℝ) ^ (f * (r * k + r ^ 2))) * |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by ring
    _ = |(NumberField.discr X.B.I.F : ℝ)| ^ LsNc5.covolumeExponent r k := by rw [hTp, hpow, one_mul, one_mul]

theorem covolRef_of (hN : LsNc5.CovolN) (hB : RefNBox) : CovolRef := by
  delta CovolRef
  intro D X hb FdN FdN' u u' hH
  have hd : (0 : ℝ) < |(NumberField.discr X.B.I.F : ℝ)| :=
    abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero _))
  rw [covol_refN hN hB X u _ FdN hH.2.2.1,
    covol_refN hN hB X u _ FdN' (by first | exact hH.2.2.2.1 | exact hH.2.2.2), ← Real.rpow_add hd]
  congr 1
  delta eDF LsNc5.covolumeExponent
  ring

theorem covolRef_of_steps (hC : LsNc5.CoordCovol) (hB : RefNBox) : CovolRef :=
  covolRef_of (covolN_of_coordCovol hC) hB

end Formalism.L2.SG.Pf.NcReal.JX
end
end
