module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefDecay
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovMeas
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DoubleCosetBesselBoundOfBesselUniq
noncomputable section

namespace Formalism.MainNotions.BridgeCS3dClosed

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem inputs_of (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hJ : PI.BesselMapUniq.BesselMapUniq) : Formalism.FourierDecayAlt.ThreeDimData.Inputs := by
  have hK := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth
  refine ⟨?_, hDI, hK, hJ⟩
  intro k r _ ε lam h H _ _ _ σ hlam hDS hgap hh P hP w₁ w₂ h₁ h₂
  have hSmooth (w : H) (hw : w ∈ PI.UpqRep.lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) :
      w ∈ smoothVecs (k := k) (r := r) σ := by
    obtain ⟨V, hfd, hwV, hstable⟩ := DoubleDerivativeSmoothness.kfin_of_mem_lowKSub hw
    exact hK k r ε lam H σ hlam hDS w
      ⟨V, hfd, hwV, LowestKTypeMultiplicity.kstable_Hpk hP hstable⟩

  let a := Formalism.FourierDecayAlt.ThreeDimData.aOf r h
  let m := ⌈a⌉₊
  have hn : 1 ≤ 2 * r + k + 1 := by omega
  have hnReal : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hnCube : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hnReal
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  have hsqrt : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have ha0 : 0 ≤ a := div_nonneg hh0 (by positivity)
  have ha8 : a ≤ h / 8 := by
    dsimp [a, Formalism.FourierDecayAlt.ThreeDimData.aOf]
    exact div_le_div_of_nonneg_left hh0 (by norm_num) (by linarith)
  have ham : a ≤ (m : ℝ) := Nat.le_ceil a
  have hm : ReciprocityTheory.ChartRestriction.DS.thrStar ε + (m : ℝ) < h := by
    have hmUpper : (m : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
    linarith [Formalism.L2.SG.BesselDiscreteSeries.thrStar_le hn ε]
  obtain ⟨C, Ws, -, hC⟩ :=
    ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m hm hDS
  let B := C * (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W w₁‖).sum *
    (Ws.map fun W => ‖dsigW (k := k) (r := r) σ W w₂‖).sum
  refine ⟨B, fun x hx => ?_⟩
  let g := Formalism.FourierDecayAlt.B.gN x
  have hg : 1 ≤ g := ((Formalism.FourierDecayAlt.P.norm_inverse_bound k r).2 x hx).2
  have hg0 : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hb : g ^ m * ‖inner ℂ w₂ (σ x w₁)‖ ≤ B :=
    hC w₁ (hSmooth w₁ h₁) w₂ (hSmooth w₂ h₂) x hx
  have hB : 0 ≤ B := le_trans (mul_nonneg (pow_nonneg hg0.le _) (norm_nonneg _)) hb
  have hpow : (g ^ m)⁻¹ ≤ g ^ (-a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hg0.le]
    exact Real.rpow_le_rpow_of_exponent_le hg (neg_le_neg ham)
  calc
    ‖inner ℂ w₂ (σ x w₁)‖ ≤ B * (g ^ m)⁻¹ := by
      rw [le_mul_inv_iff₀ (pow_pos hg0 _), mul_comm]
      exact hb
    _ ≤ B * g ^ (-a) := mul_le_mul_of_nonneg_left hpow hB

end Formalism.MainNotions.BridgeCS3dClosed
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HsNormSqEqHilbertSchmidtSq
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OOCore
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
  Formalism.L2.SG.Pf.JointAmplitudePoints Formalism.L2.SG.Pf.ThmBChain
open scoped ENNReal

namespace Formalism.L2.SG.Pf.OOCore

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Core

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (ν : X.B.I.Ginf → Measure X.B.I.Ginf)

def OOP (w : Point D.host.E (D.R.rS + 1)) : X.Vpi u' →L[ℂ] X.Vpi u :=
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' w)

theorem joint_amplitude_eq_normSq (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) :
    J2of Y u u' ν (toPts w) =
      Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsNormSq (OOP u u' ν w) := by
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = toPts w ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, rfl, hw⟩
  unfold J2of
  rw [dite_eq_left hex]
  have hc : hex.choose = w := toPts_injective hex.choose_spec.1
  rw [hc, Formalism.L2.SG.PackageTie.norm_hsEmb_sq]
  unfold Jw OOP
  rw [Formalism.L2.SG.Pf.LTL.hsNormSq_smul]

variable {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

end Core

end Formalism.L2.SG.Pf.OOCore
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.OOCoreHilbertSchmidt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_hilbertSchmidt_sq {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact inner_self_eq_norm_sq _
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | (rw [inner_self_eq_norm_sq_to_K]; simp [sq])

variable {D : D7} {X : HidaSetting D} (u u' : D.what₂.Word)

theorem hsNormSq_OOP_quot (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (w : Point D.host.E (D.R.rS + 1))
    (hw : ∃ γ, IsPtRep X u u' w γ) (hG : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) :
    Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) =
      ∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  have hF := hQ w hw hG
  rw [hsNormSq_eq_hilbertSchmidt_sq]
  simp only [hsNormSq_eq_hilbertSchmidt_sq]
  unfold Formalism.L2.SG.Pf.OOCore.OOP hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GXPos : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ γ, IsPtRep X u u' w γ) → ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

variable (Y : Formalism.L2.SG.Full.Full X) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

section GX

variable {D : D7} {X : HidaSetting D}

theorem frm_sc (u : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    frm X u sc v a = (((sc ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • frm X u 1 v a := by
  unfold frm famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem zx_rd (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    ZX X u u' D.host.rdE γ v a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * ZX X u u' 1 γ v a b := by
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = (D.host.rdE ^ (D.R.rS - (c : ℕ)))⁻¹ := by
    intro c
    have hc := c.isLt
    unfold rhoF
    have h1 := Real.rpow_intCast D.host.rdE (-((D.R.rS - (c : ℕ) : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast] at h1
    rw [← h1]
    congr 1
    push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hc)]
    ring
  rw [hρ a, hρ b]
  unfold ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_sc u D.host.rdE v a, frm_sc u' D.host.rdE v b, Matrix.mulVec_smul]
  unfold hJ
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  clear hρ
  push_cast
  ring

theorem gx_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ γ, IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    GX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) =
      Formalism.MainNotions.S.ThB.Gpt (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w) := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dite_eq_left hw]
    exact hw.choose_spec
  have hZ : ∀ a b, ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) a b =
      (-1 : ℂ) ^ (D.R.rS - b.val) * ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w) a b := by
    intro a b
    have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
    unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
    simp only [Matrix.map_apply] at h1
    rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
    have hs : ((-1 : ℂ) ^ (D.R.rS - b.val)) * (-1 : ℂ) ^ (D.R.rS - b.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [zx_rd, Formalism.L2.SG.Pf.RelPtR.ptMat_ptLoc τ w a b]
    have h2 : ZX X u u' 1 (gamW X u u' w) (vOf X τ) a b = (-1 : ℂ) ^ (D.R.rS - b.val) * embS D τ (ptMat w a b) := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2]
    ring
  have hD : ∀ l (hl : l ≤ D.R.rS + 1), Complex.normSq (Formalism.L2.SG.RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)) l) =
      Complex.normSq (leadMinor (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) l hl) := by
    intro l hl
    unfold Formalism.L2.SG.RealObj.Dl leadMinor
    rw [dite_eq_left hl]
    have hM : (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)).submatrix (Fin.castLE hl) (Fin.castLE hl) *
          Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE hl b).val)) := by
      ext i j
      simp [Matrix.mul_diagonal, hZ, mul_comm]
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
    simp [Complex.normSq_neg]
  unfold GX Gv Formalism.MainNotions.S.ThB.Gpt
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hD (D.R.rS + 1) le_rfl, hD D.R.rS (Nat.le_succ _)]

theorem gxPos_holds (u u' : D.what₂.Word) : GXPos (X := X) u u' := by
  intro w hb hw v
  have hv : v = vOf X (X.pl v) := (X.pl.symm_apply_apply v).symm
  rw [hv, gx_eq u u' w hw (X.pl v)]
  exact hb.2 (X.pl v)

end GX

end Formalism.L2.SG.Pf.OOCoreHilbertSchmidt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RhoSurjPf
noncomputable section

namespace Formalism.L2.SG.Pf.RhoSurjW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.AllRowsOf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i
  simp [PI.FinKW.vecV, map_sub]

theorem vecV_nsmul (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : ℕ)
    (a : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (c • a) = c • PI.FinKW.vecV X.B.I v a := by
  funext i
  simp [PI.FinKW.vecV]

theorem exists_cofactor (p : TypX X) : ∃ c : ℕ, (X.B.g : ℕ) = gOf p * c := by
  rw [X.g_eq]
  unfold gOf
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩

theorem piV_mem_KgX (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kg X.B.g) (p : TypX X) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ MassDataIdxSteps.KgX X p := by
  have hKf := (Bridge_mem_Kf_iff X.B.I hb x).2 hx.1
  rw [Kf, Subgroup.mem_iInf] at hKf
  refine ⟨hKf p.1, ?_⟩
  intro y hy
  obtain ⟨c, hc⟩ := exists_cofactor X p
  obtain ⟨u, huv, huw⟩ := PI.FinKW.local_vector_lift X.B.I p.1 y
  have huL : u ∈ X.B.I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective X.B.I u fun w => by
    by_cases hw : w = p.1
    · subst hw
      rw [huv]
      exact hy
    · rw [huw w hw]
      exact zero_mem _
  obtain ⟨z, hzL, hz⟩ := hx.2 u huL
  have hfx : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  refine ⟨c • PI.FinKW.vecV X.B.I p.1 z, nsmul_mem (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I z hzL p.1) c, ?_⟩
  have e := congrArg (PI.FinKW.vecV X.B.I p.1) hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hfx, PI.FinKW.vecV_mulVec, huv, Nat.cast_smul_eq_nsmul,
    vecV_nsmul] at e
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_smul, ← hc]
  exact e

end Loc

section Count

variable {D : D7} (X : HidaSetting D)

theorem card_target :
    Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = Nat.card (G0g D.nd) := by
  classical
  have hT : (Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod]
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.prod_typ X (fun g => (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod g)) : ℝ))]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.ggC_eq D.R (gOf p)]
    rfl
  have hG : (Nat.card (G0g D.nd) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sigma, Fin.prod_univ_two]
    have e : ∀ k : Fin 2, ∏ _v : D.nd.PlG k, (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) =
        (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g k))) : ℝ) ^ D.R.f := fun k => by
      rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
      rfl
    exact congrArg₂ (· * ·) (e 0) (e 1)
  exact_mod_cast hT.trans hG.symm

end Count

theorem reduction_map_surjective : RhoSurj := by
  intro D X
  classical
  let hb : AdBridgeIso X.B.I := (Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1
  have hK : ∀ p : TypX X, ((KvS X p : Subgroup _) : Set (MassDataIdxSteps.HAp X p)) = MassDataIdxSteps.KvX X p := by
    intro p
    obtain ⟨K, hKs, -, -, -⟩ := Formalism.L2.SG.Pf.MassDataX.stK_holds X p
    have e : KvS X p = K := by
      have e : (K : Set _) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := hKs
      rw [KvS, ← e, Subgroup.closure_eq]
    rw [e]
    exact hKs
  choose ρ hρ hker using fun p : TypX X => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p (KvS X p) (hK p)
  let ψ : KsetSub X.B.I →* ∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => KvS X p) p)).comp (phiK X hb)
  have hψ : Function.Surjective ψ := by
    intro t
    choose a ha using fun p => hρ p (t p)
    obtain ⟨k, hk⟩ := phiK_surjective X hb single_component_surjective a
    refine ⟨k, funext fun p => ?_⟩
    show ρ p (phiK X hb k p) = t p
    rw [hk]
    exact ha p
  let ι : KSub X.B.I → KsetSub X.B.I := fun x => ⟨x.1, x.2⟩
  have hψι : ∀ x y : KSub X.B.I, rhoX X x = rhoX X y → ψ (ι x) = ψ (ι y) := by
    intro x y hxy
    have h1 : rhoX X (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hg := (rhoX_eq_one_iff X _).1 h1
    have h2 : ψ (ι (x⁻¹ * y)) = 1 := by
      funext p
      show ρ p (phiK X hb (ι (x⁻¹ * y)) p) = 1
      exact (hker p _).2 (RhoSurjW.piV_mem_KgX X hb _ hg p)
    have h3 : ι (x⁻¹ * y) = (ι x)⁻¹ * ι y := rfl
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let f : (rhoX X).range → (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) :=
    fun r => ψ (ι (MonoidHom.mem_range.1 r.2).choose)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨k, hk⟩ := hψ t
    let x : KSub X.B.I := ⟨k.1, k.2⟩
    let r : (rhoX X).range := ⟨rhoX X x, x, rfl⟩
    exact ⟨r, (hψι _ x (MonoidHom.mem_range.1 r.2).choose_spec).trans hk⟩
  have hle : Nat.card (G0g D.nd) ≤ Nat.card (rhoX X).range := by
    rw [← RhoSurjW.card_target X]
    exact Nat.card_le_card_of_surjective f hf
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_le_card _ hle)

end Formalism.L2.SG.Pf.RhoSurjW
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefCCT
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CoefCCPf
open Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace Formalism.L2.SG.Pf.CoefCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.L2.SG.Pf.CoefDecay

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem exists_exp_of_gapOK {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ} (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : A ≤ h / 2) : ∃ m' : ℕ, ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h ∧ A ≤ m' := by
  obtain ⟨-, h120, -, -⟩ := hok
  have hn : 1 ≤ 2 * r + k + 1 := by omega
  have ht := Formalism.L2.SG.BesselDiscreteSeries.thrStar_le hn ε
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hn3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hn1
  refine ⟨⌈A⌉₊, ?_, Nat.le_ceil A⟩
  have hc := Nat.ceil_lt_add_one hA0
  linarith

section congr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem ev_congr {f₁ f₂ : B.Mat k r → E} (hf : ∀ y ∈ B.GV k r, f₁ y = f₂ y) :
    ∀ (ks : List Bool) (xs : List (B.Mat k r)), (∀ X ∈ xs, B.inLie k r X) →
      ∀ g ∈ B.GV k r, PI.ComplexConjugateDerivative.ev ks xs f₁ g = PI.ComplexConjugateDerivative.ev ks xs f₂ g
  | [], xs, _, g, hg => by cases xs <;> exact hf g hg
  | _ :: _, [], _, g, hg => hf g hg
  | b :: ks, X :: xs, hx, g, hg =>
    PI.ComplexConjugateDerivative.D_congr (b := b) (fun y hy => ev_congr hf ks xs (fun Y hY => hx Y (List.mem_cons_of_mem _ hY)) y hy) hg
      (hx X List.mem_cons_self)

theorem inCC_congr {A : ℝ} {m : ℕ} {f₁ f₂ : B.Mat k r → E} (hf : ∀ y ∈ B.GV k r, f₁ y = f₂ y)
    (h1 : B.InCC (k := k) (r := r) A m f₁) : B.InCC (k := k) (r := r) A m f₂ := by
  obtain ⟨c, hck, hb⟩ := h1
  refine ⟨c, fun g₀ hg₀ => ?_, fun u w hu hw hl g hg => ?_⟩
  · obtain ⟨U, f', hU, h0, hc, he⟩ := hck g₀ hg₀
    exact ⟨U, f', hU, h0, hc, fun y hy hyG => (hf y hyG).symm.trans (he y hy hyG)⟩
  · have e : B.dLR u w f₂ g = B.dLR u w f₁ g := by
      rw [PI.ComplexConjugateDerivative.dLR_eq_ev, PI.ComplexConjugateDerivative.dLR_eq_ev]
      exact (ev_congr hf _ (u ++ w) (fun X hX => by
        rcases List.mem_append.1 hX with h | h
        · exact (hu X h).1
        · exact (hw X h).1) g hg).symm
    rw [e]
    exact hb u w hu hw hl g hg

end congr

theorem coefM_translate_inCC {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (B.GV k r) σ) {A : ℝ}
    (hdec : ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C)
    {v v' : H} (hv : v ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ)
    (hv' : v' ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ) {a b : B.Mat k r} (ha : a ∈ B.GV k r)
    (hb : b ∈ B.GV k r) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (fun g => Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' (a * g * b)) := by
  have hai : a⁻¹ ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv ha
  have hdet : IsUnit a.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det ha
  have haa : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a hdet
  refine inCC_congr (f₁ := Formalism.MainNotions.S.Pv.BetaCut.coefM σ (σ a⁻¹ v) (σ b v') ξ ξ') (fun g hg => ?_)
    (coefM_inCC_of_dec hσ hdec (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hai)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv' hb) ξ ξ' m)
  rw [coefM_eq, coefM_eq]
  show ⟪σ a⁻¹ v, σ g (σ b v')⟫_ℂ • rk1 ξ ξ' = ⟪v, σ (a * g * b) v'⟫_ℂ • rk1 ξ ξ'
  congr 1
  let L : H →ₗᵢ[ℂ] H := ⟨(σ a⁻¹ : H →ₗ[ℂ] H), fun x => hσ.2.1 _ hai x⟩
  have hgb : g * b ∈ B.GV k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul hg hb
  have e1 : σ (a * g * b) v' = σ a (σ g (σ b v')) := by
    simp only [Matrix.mul_assoc, hσ.1.2 a ha _ hgb, hσ.1.2 g hg b hb,
      ContinuousLinearMap.comp_apply]
  have e2 : σ a⁻¹ (σ a (σ g (σ b v'))) = σ g (σ b v') := by
    have := hσ.1.2 _ hai _ ha
    rw [haa, hσ.1.1] at this
    have h3 := congrArg (fun T : H →L[ℂ] H => T (σ g (σ b v'))) this
    simpa using h3.symm
  rw [e1, ← L.inner_map_map v (σ a (σ g (σ b v')))]
  show ⟪σ a⁻¹ v, σ g (σ b v')⟫_ℂ = ⟪σ a⁻¹ v, σ a⁻¹ (σ a (σ g (σ b v')))⟫_ℂ
  rw [e2]

theorem coefM_smul (σ : B.Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq) (c : ℂ) :
    c • Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ' = Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' (c • ξ) ξ' := by
  funext g
  ext x
  simp only [Pi.smul_apply, Formalism.MainNotions.S.Pv.BetaCut.coefM, ContinuousLinearMap.smulRight_apply, _root_.smul_apply]
  rw [smul_comm c, smul_comm c]

theorem dec_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (m' : ℕ)
    (hm' : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m' < h) {A : ℝ} (hA : A ≤ m') [CompleteSpace H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDSHpk k r ε lam σ) :
    ∀ a ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ, ∀ b ∈ Formalism.MainNotions.S.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C := by
  obtain ⟨C, Ws, -, hC⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m' hm' hσ
  intro a ha b hb
  refine ⟨C * (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w b‖).sum *
      (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w a‖).sum, fun g hg => ?_⟩
  have h1 := PI.ComplexConjugateDerivative.one_le_gN hg
  calc B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ B.gN g ^ (m' : ℝ) * ‖⟪a, σ g b⟫_ℂ‖ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h1 hA) (norm_nonneg _)
    _ = B.gN g ^ m' * ‖⟪a, σ g b⟫_ℂ‖ := by rw [Real.rpow_natCast]
    _ ≤ _ := hC b hb a ha g hg

theorem smul_coefM_translate_inCC_kfin_gapOK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ h / 2) [CompleteSpace H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) {v v' : H}
    (hv : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v) (hv' : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v')
    {a b : B.Mat k r} (ha : a ∈ B.GV k r) (hb : b ∈ B.GV k r) (c : ℂ) (ξ : Wp) (ξ' : Wq) (m : ℕ) :
    B.InCC (k := k) (r := r) A m (fun g => (c • Formalism.MainNotions.S.Pv.BetaCut.coefM σ v v' ξ ξ') (a * g * b)) := by
  obtain ⟨m', hm', hAm⟩ := exists_exp_of_gapOK (ε := ε) hok hA0 hA
  have hks := Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.k_finite_smooth
  rw [coefM_smul]
  exact coefM_translate_inCC (Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ) (dec_of_DS hlam hgap m' hm' hAm hσ)
    (hks k r ε lam H σ (by exact hlam) hσ v hv) (hks k r ε lam H σ (by exact hlam) hσ v' hv') ha hb (c • ξ) ξ' m

end Formalism.L2.SG.Pf.CoefCC
end
end

noncomputable section

open scoped Matrix InnerProductSpace

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.CarrierT

namespace Formalism.L2.SG.Pf.CoefCCT

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ}

theorem fcT_inCC (C : Choice X θ) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (u u' : D.what₂.Word)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ) (h : Fin (nfE D) → ℝ)
    (hlam : ∀ j, Formalism.QuantumDeterminants.IsHCParam (lamD D (e (plE D j))))
    (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (h j))
    (hok : ∀ j, Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (h j)) {A₀ : ℝ} (hA0 : 0 ≤ A₀) (hA : ∀ j, A₀ ≤ h j / 2)
    (hka : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (a j))
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j))
    (j : Fin (nfE D)) (m : ℕ) :
    Formalism.FourierDecayAlt.B.InCC (k := D.R.k) (r := D.R.rS) A₀ m (fcT X C e u u' a b ξ ξ' cc j) :=
  Formalism.L2.SG.Pf.CoefCC.smul_coefM_translate_inCC_kfin_gapOK (hlam j) (hgap j) (hok j) hA0 (hA j)
    (Formalism.L2.SG.Pf.dsTr C (e (plE D j))) (hka j) (hkb j)
    (Formalism.L2.SG.RealObj.EnergyIntTor.tor_mem_UH (Formalism.L2.SG.Pf.muT_ne D))
    (Formalism.L2.SG.RealObj.EnergyIntTor.tor_mem_UH (inv_ne_zero (Formalism.L2.SG.Pf.muT_ne D))) (cc j) (ξ j) (ξ' j) m

theorem coefCC_carrierInTc (C : Choice X θ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
    (he : PlaceTie X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (Formalism.L2.SG.Pf.BaseOf.towersOf X C u u' e j).base.π
      (Formalism.L2.SG.Pf.BaseOf.towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (h : Fin (nfE D) → ℝ)
    (hlam : ∀ j, Formalism.QuantumDeterminants.IsHCParam (lamD D (e (plE D j))))
    (hgap : ∀ j, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D (e (plE D j))) (h j))
    (hok : ∀ j, Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS (h j)) (hA0 : 0 ≤ A₀) (hA : ∀ j, A₀ ≤ h j / 2)
    (hka : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (a j))
    (hkb : ∀ j, PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS)
      (sigB X (C.Q (e (plE D j))) (C.Qi (e (plE D j))) (e (plE D j))) (b j)) :
    Formalism.L2.SG.Pf.Built.CoefCC (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) :=
  fun j m => fcT_inCC C e u u' a b ξ ξ' cc h hlam hgap hok hA0 hA hka hkb j m

end Formalism.L2.SG.Pf.CoefCCT
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarVolPf
noncomputable section

namespace Formalism.L2.SG.Pf.DstarVolPf

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.Theta
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def frOf : Formalism.IndefR.Eqv.UI.Frames D (VS D) where
  ε := fun _ => Formalism.L2.SG.InstExistsPf.epsV D
  P := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose
  unit := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.1
  spec := fun v => (Formalism.L2.SG.InstExistsPf.exists_P D ((Formalism.L2.Host.tauPl D).symm v)).choose_spec.2
  Λ := Formalism.L2.SG.InstExistsPf.Lv D
  Λ_fg := Formalism.L2.SG.InstExistsPf.L_fg D
  Λ_span := Formalism.L2.SG.InstExistsPf.L_span D
  Λ_dual := Formalism.L2.SG.InstExistsPf.L_dual D

theorem instOf_eq : Formalism.L2.SG.InstExistsPf.instOf D = Formalism.IndefR.Eqv.UI.instV (frOf D) := rfl

theorem lv_eq : (frOf D).Λ = Formalism.IndefR.Eqv.UI.Lv D (VS D) := rfl

abbrev IV : Formalism.MainNotions.S.AutInst := Formalism.IndefR.Eqv.UI.instV (frOf D)

def cdProdI : ENNReal := ∏ v : InfinitePlace D.host.F, (D.s.cdScale (VS D).rank ((frOf D).ε v) : ENNReal)

def muVI (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [SigmaFinite μf] : Measure (GA D (VS D)) :=
  cdProdI D • ((Formalism.IndefR.Eqv.UI.instV (frOf D)).muA μf).map (Formalism.IndefR.Eqv.UI.brg (frOf D))

def VolMeasOf : Prop :=
  ∀ (μf : Measure (Formalism.IndefR.Eqv.UI.instV (frOf D)).Gf) [μf.IsHaarMeasure] [SigmaFinite μf],
    μf (Formalism.IndefR.Eqv.UI.instV (frOf D)).Kset = 1 →
    IsVolMeas D (VS D) (D.R.k + D.R.rS) (D.R.rS + 1) (muVI D μf)

theorem volMeasOf_of (hcd : cdScaleTie D) : VolMeasOf D := by
  intro μf _ _ hK
  have h1 : ∀ (v : InfinitePlace D.host.F) (i : Fin (D.R.k + D.R.rS)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i)) = true := fun v i => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inl i))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have h2 : ∀ (v : InfinitePlace D.host.F) (j : Fin (D.R.rS + 1)),
      (frOf D).ε v ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j)) = false := fun v j => by
    have := Formalism.L2.SG.InstExistsPf.eSgn_isLeft D ((Formalism.L2.SG.InstExistsPf.eSgn D).symm (Sum.inr j))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  exact Formalism.L2.S.S7.ZsCovMeas.isVolMeas_muV (frOf D) hcd (lv_eq D) (fun _ => (Formalism.L2.SG.InstExistsPf.eSgn D).symm)
    h1 h2 (fun v => (D.s.cdScale_pos _ _).ne') μf hK

theorem cdScale_cast {n m : ℕ} (h : n = m) (ε : Fin n → Bool) :
    D.s.cdScale n ε = D.s.cdScale m (fun i => ε (Fin.cast h.symm i)) := by
  subst h; rfl

theorem cdScale_epsV :
    D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) = D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) := by
  rw [cdScale_cast D ((Formalism.L2.SG.InstExistsPf.rank_eq D).trans (dimS_eq D.R).symm)]
  rfl

section Gen

variable {I : Formalism.MainNotions.S.AutInst} (hb : AdBridgeIso I)

theorem mem_rr_iff' (x : I.GA) :
    x ∈ Formalism.MainNotions.LeviCoordinates.rr_GF I ↔ toHA I hb x ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hGF := Formalism.L2.SG.Closed.AdBridgeGF_holds I (toHA I hb) (toHA_isBridge I hb)
  have hrat : ∀ h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J,
      h ∈ ratHA I ↔ h ∈ HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := fun h => Iff.rfl
  rw [← hrat, ← hGF, Formalism.MainNotions.LeviCoordinates.rr_mem_GF]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← (toHA I hb).injective hyx]

theorem isFD_image (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ν : Measure (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J))
    (hν : ν ≪ (I.muA μf).map (toHA I hb)) :
    IsFundamentalDomain (HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) (toHA I hb '' fund) ν := by
  haveI hBor : BorelSpace (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : (I.muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' I μf
  haveI : (I.muA μf).IsMulLeftInvariant := inferInstance
  have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF I) fund (I.muA μf) :=
    Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
  let Γ : Subgroup (HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J) := HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
  let e := (toHA I hb).toHomeomorph.toMeasurableEquiv
  let eΓ : Γ ≃ Formalism.MainNotions.LeviCoordinates.rr_GF I :=
    { toFun := fun g => ⟨(toHA I hb).symm (g : HA _ _ _), (mem_rr_iff' hb _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact g.2)⟩
      invFun := fun x => ⟨toHA I hb x, (mem_rr_iff' hb _).1 x.2⟩
      left_inv := fun g => Subtype.ext (ContinuousMulEquiv.apply_symm_apply _ _)
      right_inv := fun x => Subtype.ext (ContinuousMulEquiv.symm_apply_apply _ _) }
  have hqmp : Measure.QuasiMeasurePreserving e.toEquiv.symm ((I.muA μf).map e) (I.muA μf) := by
    refine (MeasurePreserving.quasiMeasurePreserving ⟨e.symm.measurable, ?_⟩)
    exact e.map_symm_map
  have hfd : IsFundamentalDomain Γ (e '' fund) ((I.muA μf).map e) := by
    refine hfd0.image_of_equiv e.toEquiv hqmp eΓ fun g x => ?_
    show e ((eΓ g : I.GA) * x) = (g : HA _ _ _) * e x
    show toHA I hb ((toHA I hb).symm g * x) = (g : HA _ _ _) * toHA I hb x
    rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
  exact hfd.mono hν

end Gen

theorem covol_gen (hVM : VolMeasOf D) (hVol : VolTie D) (I : Formalism.MainNotions.S.AutInst)
    (hI : I = Formalism.IndefR.Eqv.UI.instV (frOf D)) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    (fund : Set I.GA) (hf : I.IsFundDom (I.muA μf) fund) :
    I.vol μf fund / (μf I.Kset).toReal *
      ∏ _v : InfinitePlace I.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = volY0 D := by
  subst hI
  have hKc : IsCompact (IV D).Kset := Formalism.L2.SG.Closed.AutKCompact_holds (IV D)
  have hKo : IsOpen (IV D).Kset := by
    have h := (IV D).topf_open 1 le_rfl
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨hx, fun y hy => ⟨_, Formalism.L2.SG.Pf.unitaryCongruence.K_sub_mv _ hx hy, by simp⟩⟩
    · intro hx
      exact hx.1
  have hpos : 0 < μf (IV D).Kset := hKo.measure_pos μf ⟨1, Formalism.L2.SG.Pf.unitaryCongruence.K_one _⟩
  have hfin : μf (IV D).Kset < ⊤ := hKc.measure_lt_top
  set c := μf (IV D).Kset with hc
  let μ' : Measure (IV D).Gf := c⁻¹ • μf
  haveI : μ'.IsHaarMeasure := Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos.ne')
  have hfs : ∀ n, μ' (spanningSets μf n) < ⊤ := fun n => by
    show (c⁻¹ • μf) _ < ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hpos) (measure_spanningSets_lt_top μf n)
  haveI : SigmaFinite μ' :=
    ⟨⟨{ set := spanningSets μf, set_mem := fun _ => Set.mem_univ _, finite := hfs, spanning := iUnion_spanningSets μf }⟩⟩
  have hK1 : μ' (IV D).Kset = 1 := by
    show (c⁻¹ • μf) (IV D).Kset = 1
    rw [Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel hpos.ne' hfin.ne]
  have hV := hVM μ' hK1
  have hsig : (VS D).SigOK := D.sp.Y_sig 0
  have hsv : ∀ τ, (VS D).sig τ = (D.R.k + D.R.rS, D.R.rS + 1) := fun τ => D.sp.baseSpace_signature_eq τ
  obtain ⟨-, hall⟩ := hVol (VS D) _ _ hsig hsv
  obtain ⟨-, hfd⟩ := hall _ hV
  let hb : AdBridgeIso (IV D) := (Formalism.L2.SG.Closed.adelic_isomorphism_statement (IV D)).1
  have hbrg : Formalism.IndefR.Eqv.UI.brg (frOf D) = toHA (IV D) hb := rfl
  have hμA : (IV D).muA μ' = c⁻¹ • (IV D).muA μf := by
    show (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod (c⁻¹ • μf) = c⁻¹ • (Measure.pi fun v => Formalism.REAL.muG ((IV D).ε v)).prod μf
    exact Measure.prod_smul_right _
  haveI : BorelSpace (HAd (IV D)) := ⟨rfl⟩
  have hν : muVI D μ' ≪ ((IV D).muA μf).map (toHA (IV D) hb) := by
    unfold muVI
    rw [hbrg, hμA, Measure.map_smul]
    · exact (Measure.smul_absolutelyContinuous).trans Measure.smul_absolutelyContinuous
    · exact (toHA (IV D) hb).continuous.measurable.aemeasurable
  have hFD := isFD_image hb μf fund hf (muVI D μ') hν
  have key : muVI D μ' (toHA (IV D) hb '' fund) = ENNReal.ofReal (D.vol (VS D)) := hfd _ hFD
  let e := (toHA (IV D) hb).toHomeomorph.toMeasurableEquiv
  have hmeas : Measurable (toHA (IV D) hb) := (toHA (IV D) hb).continuous.measurable
  have hS : MeasurableSet (toHA (IV D) hb '' fund) := (e.measurableSet_image).2 hf.1
  have hmap : muVI D μ' (toHA (IV D) hb '' fund) = cdProdI D * (c⁻¹ * (IV D).muA μf fund) := by
    unfold muVI
    rw [Measure.smul_apply, smul_eq_mul, hbrg, hμA]
    congr 1
    erw [Measure.map_apply hmeas hS]
    rw [Set.preimage_image_eq _ (toHA (IV D) hb).injective, Measure.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 200000 in
  have hA0 : (IV D).muA μf fund ≠ 0 := by
    haveI : ((IV D).muA μf).IsHaarMeasure := Formalism.L2.SG.PoincareInHH.Cut.muA_isHaar' (IV D) μf
    haveI : ((IV D).muA μf).IsMulLeftInvariant := inferInstance
    have hfd0 : IsFundamentalDomain (Formalism.MainNotions.LeviCoordinates.rr_GF (IV D)) fund ((IV D).muA μf) :=
      Formalism.MainNotions.LeviCoordinates.rr_isFD ⟨hf.1, hf.2.1, hf.2.2⟩
    exact hfd0.measure_ne_zero (NeZero.ne _)
  have hcd0 : cdProdI D ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => by simpa using (D.s.cdScale_pos _ _).ne'
  have hci0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin.ne
  replace key := hmap.symm.trans key
  have hAT : (IV D).muA μf fund ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.mul_top hci0, ENNReal.mul_top hcd0] at key
    exact ENNReal.ofReal_ne_top key.symm
  have hL0 : cdProdI D * (c⁻¹ * (IV D).muA μf fund) ≠ 0 := mul_ne_zero hcd0 (mul_ne_zero hci0 hA0)
  have hvpos : 0 < D.vol (VS D) := by
    by_contra hle
    push_neg at hle
    rw [ENNReal.ofReal_of_nonpos hle] at key
    exact hL0 key
  have hR := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_ofReal hvpos.le, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv] at hR
  have hcdR : (cdProdI D).toReal = ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) := by
    unfold cdProdI
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    show ((D.s.cdScale (VS D).rank (Formalism.L2.SG.InstExistsPf.epsV D) : ENNReal)).toReal = _
    rw [cdScale_epsV]
    rfl
  rw [hcdR] at hR
  show ((IV D).muA μf fund).toReal / c.toReal *
      ∏ _v : InfinitePlace D.host.F, (D.s.cdScale (2 * D.R.rS + D.R.k + 1) (epsSH D.R) : ℝ) = D.vol (VS D)
  rw [← hR]
  ring

section Record

variable {D}

theorem dstarVolV_of (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVolV X :=
  covol_gen D (volMeasOf_of D hcd) hVol X.B.I (h.trans (instOf_eq D)) X.B.μf X.B.fund X.B.fund_spec

theorem dstarVol_holds (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hVol : VolTie D)
    (hcd : cdScaleTie D) (hT : dsigTie D) : Formalism.L2.SG.Pf.RowDictPf.DstarVol X :=
  Formalism.L2.SG.Pf.RowDictPf.dstarVol_of X hT (dstarVolV_of X h hVol hcd)

end Record

end Formalism.L2.SG.Pf.DstarVolPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsCountBase
noncomputable section

namespace Formalism.L2.SG.Pf.AllRowsCountBase

open Finset Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf

variable {D : D7} (X : HidaSetting D)

open Formalism.MainNotions.BridgeLemma NumberField in
theorem splits_X (k : Fin 2) : SplitsCompl X.B.I.E (D.host.g k) := by
  have hp := D.host.g_prime k
  have := span_isMaximal hp
  have hspl := splitsCompl_of_ncard D.host.E (D.host.g k) hp (by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hp) (𝓞 D.host.E), ← image_plOver _ hp,
      (injOn_asIdeal _ _).ncard_image]
    exact D.nd.g_split k)
  exact Formalism.L2.SG.ThmSOwn.splitsCompl_of_equiv X.ιE hspl

theorem hc_X (hT : AutTie D X.B X.pl) (v : NumberField.InfinitePlace X.B.I.F) : Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  exact Inh.aut_isHCParam_of_autTie hT v

theorem countBase_of (hT : AutTie D X.B X.pl) {large₂ : SizeData₂ D} {n0 : ℕ} {A C cb : ℝ}
    (hp : AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n0 A C cb) (hg1 : 4 * D.R.r < D.host.g 1) : CountBase X n0 A C cb := by
  obtain ⟨-, p2, p3, p4, p5, p6, p7, -, p9, p10, p11, p12⟩ := hp
  have hn := hT.n_eq
  have hf := hT.f_eq
  have hrd := hT.rd_eq
  have tg := X.g_eq
  have hq : ∀ v, X.B.I.pAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = true).card ∧
      X.B.I.qAt v = (univ.filter fun a : Fin D.R.r => epsS D.R a = false).card := by
    intro v
    have he := hT.eps_eq v
    constructor
    · simp only [AutInst.pAt, he]
      exact card_cast hn (fun a => epsS D.R a = true)
    · simp only [AutInst.qAt, he]
      exact card_cast hn (fun a => epsS D.R a = false)
  refine ⟨large₂.sc.b, C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE), fun k => ?_,
    fun v a c hac => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hn]; exact p2, ⟨_, _, hq, ?_⟩, p11, ?_, hc_X X hT, ?_, ?_, ?_, D.host.g_prime _, ?_, splits_X X _⟩
    · rw [hn]
      exact le_trans (Nat.pow_le_pow_left card_epsS_false 2) p3
    · rw [hrd, hn]; exact p4
    · intro v a
      rw [hT.lam_eq v a]; exact p5 _ _
    · rw [tg]
      exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    · rw [tg]
      have : gg D = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := by unfold gg; push_cast; ring
      rw [← this]; exact p6
    · rw [hn]
      fin_cases k
      · exact hg1
      · exact p7
  · rw [hT.lam_eq v a, hT.lam_eq v c]
    exact p9 _ _ _ (by rw [← hT.eps_eq v a, ← hT.eps_eq v c]; exact hac)
  · rw [hn, hf, hrd]
  · rw [hf, hn]; exact p10
  · rw [hf, hn]; exact p12
  · have h := Formalism.MainNotions.BridgeLemma.Dstar_pos D
    rw [hT.Dstar_eq] at h
    exact h

section Fam

open Formalism.MainNotions.S.CountE Formalism.MainNotions.PlaceDegreeData Formalism.L2.SG.ThmSOwn

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.L2.SG.Pf.AllRowsCountBase
end
end
