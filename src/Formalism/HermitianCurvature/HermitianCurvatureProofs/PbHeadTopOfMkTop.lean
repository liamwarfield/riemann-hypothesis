module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXHeadFam
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSupp2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PsiCStarMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameParameterRegularity

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSmooth
noncomputable section

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

open Formalism.FourierDecayAlt.P.PBI.Sm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section lemmas

variable {k : ℕ}

theorem contDiff_castM {a b : ℕ} (e : a = b) : ContDiff ℝ ∞ (fun g : B.Mat k a => D.castM e g) := by
  subst e
  simp only [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact contDiff_id

theorem ms_mMap {r : ℕ} (q₀ : (Fin r → Fin r → ℂ) × Mt k (r - r)) (h₀ : (Matrix.of q₀.1).det ≠ 0) :
    MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ := by
  have hZ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.1) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_fst
  have hμ : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => Matrix.of q.2) q₀ :=
    Formalism.FourierDecayAlt.P.PBI.ms_ofC contDiffAt_snd
  have hZi : MS (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1)ᴴ⁻¹) q₀ :=
    ms_inv (ms_conjT hZ) (by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr h₀)
  unfold U.mMap
  exact Formalism.FourierDecayAlt.P.PBI.measurable_block_three (ms_const _) (ms_const _) (ms_mul hZi (ms_const _)) (ms_const _) hμ (ms_const _)
    (ms_mul (ms_const _) hZ) (ms_const _) (ms_const _)

theorem contDiffOn_xT (r : ℕ) :
    ContDiffOn ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => xT k r (Matrix.of q.1) (Matrix.of q.2))
      {q | (Matrix.of q.1).det ≠ 0} := by
  intro q₀ h₀
  have hm := ms_mMap q₀ h₀
  have hc : ContDiffAt ℝ ∞ (fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      U.mMap k r (r - r) (Matrix.of q.1) (Matrix.of q.2)) q₀ :=
    contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun l => hm i l
  exact ((contDiff_castM (k := k) (by omega : r + (r - r) = r)).contDiffAt.comp q₀ hc).contDiffWithinAt

theorem dmin_xT (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin r) (Fin r) ℂ) (μ : B.Mat k (r - r)) :
    Dmin k r z z' (xT k r Z μ) ⟨r, by omega⟩ = Z.det := by
  unfold xT
  rw [Formalism.FourierDecayAlt.P.PBI.dmin_castM (by omega) z z' _ r (by omega) (by omega),
    Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r (r - r)]
  have e := Formalism.FourierDecayAlt.P.hat_z_on_slice k r (r - r) 0 0 Z μ
  rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
  unfold U.DjU
  rw [e]

theorem xT_GV (r : ℕ) {Z : Matrix (Fin r) (Fin r) ℂ} {μ : B.Mat k (r - r)} (hZ : Z.det ≠ 0) (hμ : μ ∈ B.GV k (r - r)) :
    xT k r Z μ ∈ B.GV k r :=
  Formalism.FourierDecayAlt.P.PBE.castM_GV _ ((Formalism.FourierDecayAlt.P.slice_membership k r (r - r)).1 Z μ hZ hμ)

theorem gf_castM {a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) :
    Gf k b z z' (D.castM e g) = Gf k a (D.castV e.symm z) (D.castV e.symm z') g := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl, Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

theorem inWb_castV {a b : ℕ} (e : a = b) {z : Fin (2 * a + k + 1) → ℂ} (h : inWb k a z) : inWb k b (D.castV e z) := by
  subst e
  rwa [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl]

end lemmas

theorem pullback_smooth_formula : PbSmooth := by
  intro Wp Wq _ _ _ _ _ _ P p G hG q₀ hq₀ hG₀
  obtain ⟨⟨hsm, ⟨R, hR⟩, -⟩, -⟩ := hG
  have hCs : IsCompact {g : B.Mat P.k P.r | B.gN g ≤ R} := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have hHC : ∀ g ∈ B.GV P.k P.r, g ∉ {g : B.Mat P.k P.r | B.gN g ≤ R} → G g = 0 := by
    intro g hg hn
    by_contra hne
    exact hn (hR g hg hne)
  have hΩ := PBQ.isOpen_domP P.k P.r P.r p.T.base.z p.T.base.z'
  have hP := proper_left_variables_domain Wp Wq P p P.r le_rfl _ hCs
  have hG₀' : Matrix.of q₀.2 ∈ B.GV P.k (P.r - P.r) := hG₀.1
  have hgf : 0 < Gf P.k P.r p.T.base.z p.T.base.z' (xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2)) := by
    unfold xT
    rw [gf_castM]
    have e := Formalism.FourierDecayAlt.P.level_function_slice P.k P.r (P.r - P.r)
      (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z) (D.castV (by omega : P.r = P.r + (P.r - P.r)) p.T.base.z')
      (inWb_castV _ p.T.base.z_mem) (inWb_castV _ p.T.base.z'_mem) 0 0 (Matrix.of q₀.1) (Matrix.of q₀.2)
    rw [Formalism.FourierDecayAlt.P.LeftFubiniLemmas.rn_zero, inv_one, Matrix.one_mul, Matrix.mul_one] at e
    rw [e, MkCptPf.lowV_top p.T _, MkCptPf.lowV_top' p.T _, MkCptPf.gf_eq_ggl (by omega)]
    exact mul_pos (Complex.normSq_pos.2 hq₀.1) hq₀.2
  have hyΩ : xT P.k P.r (Matrix.of q₀.1) (Matrix.of q₀.2) ∈ PBQ.domP P.k P.r P.r p.T.base.z p.T.base.z' := by
    refine ⟨fun l hl1 hl2 => ?_, hgf⟩
    have hl : l = ⟨P.r, by omega⟩ := Fin.ext (by show (l : ℕ) = P.r; omega)
    rw [hl, dmin_xT]; exact hq₀.1
  have hyG := xT_GV P.r hq₀.1 hG₀'
  have hz : p.T.base.z = D.castV (by omega : P.r + (P.r - P.r) = P.r) (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) :=
    (p.T.z_lev P.r le_rfl).symm
  obtain ⟨V, f', hV, hyV, hf', hag⟩ := partial_bessel_smooth_compact_support P.k P.r (P.r - P.r) P.r Wp Wq (p.T.bs P.r) p.T.base
    (by omega) hz G _ hsm hCs hHC _ hΩ hP _ hyΩ hyG
  have hxc := contDiffOn_xT (k := P.k) P.r
  have hOD : IsOpen {q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) | (Matrix.of q.1).det ≠ 0} :=
    isOpen_ne_fun (Continuous.matrix_det (continuous_fst)) continuous_const
  refine ⟨{q | (Matrix.of q.1).det ≠ 0} ∩
      (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)) ⁻¹' V,
    fun q => f' (xT P.k P.r (Matrix.of q.1) (Matrix.of q.2)), hxc.continuousOn.isOpen_inter_preimage hOD hV,
    ⟨hq₀.1, hyV⟩, hf'.comp (hxc.mono Set.inter_subset_left) (fun q hq => hq.2), fun q hq hqG => ?_⟩
  exact hag _ hq.2 (xT_GV P.r hq.1 hqG.1)

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem pullback_smooth : CutEX.PbSmooth := CutEX.pullback_smooth_formula

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXRadSliceTop
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem radial_slice_top : CutEX.RadSliceTop := by
  intro Wp Wq _ _ _ _ _ _ P p G hG h hh
  have hc : P.r - P.r = P.r - D.ptSize h := by rw [hh.2]
  have hcpt : KB.CptCoef (p.T.bs P.r) (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    cases P with
    | mk k r T T' u u' =>
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0
        exact PBE.slice_level_zero_compact_support k 0 Wp Wq p.T G hG.1 (Nat.zero_le _) [] h hc hh (fun x => x.elim0)
      · exact PBE.slice_pos_cpt k r Wp Wq p.T G hG.1 r le_rfl h0 [] h hc hh (fun x => x.elim0)
  obtain ⟨R, hR⟩ := hcpt.2.1
  have hJ : P5.JFOK (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z'
      (D.castF hc (D.sliceAt P.k P.r p.T.base.z p.T.base.z' G h)) := by
    refine ⟨fun A m => JFxG.cptInCC_G hcpt.1 (PBE.isCompact_gN_le _ _ R) (fun g hg hgC => ?_) A m, hcpt.2.2⟩
    by_contra hne
    exact hgC (hR g hg hne)
  obtain ⟨Φ, hΦ⟩ := P5.radJFExists Wp Wq (JC.parLev P P.r) _ _ _ _ (p.T.bs P.r) _
    (JCTx5.isPlace_lev P p.T ⟨P.r, Nat.lt_succ_self _⟩ p.hP) rfl rfl rfl rfl hJ
  exact ⟨Φ, hΦ⟩

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbRight2
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbRight

theorem castM_nset {k a b : ℕ} (e : a = b) {g : B.Mat k a} (hg : g ∈ Nset k a) : D.castM e g ∈ Nset k b := by
  subst e
  have : D.castM rfl g = g := by
    ext i j
    simp [D.castM]
  rw [this]
  exact hg

end Formalism.FourierDecayAlt.P.CutEXPbRight

namespace Formalism.FourierDecayAlt.P

open CutEX

private theorem castM_mul_eq_mul_castM {k a b : ℕ} (e : a = b) (g h : B.Mat k a) :
    D.castM e (g * h) = D.castM e g * D.castM e h := by
  subst e
  ext i j
  simp [D.castM]

theorem pullback_right_action : CutEX.PbRight := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z u μ hu
  have hm : D.castM (by omega) (U.muP P.k P.r (P.r - P.r) u) ∈ Nset P.k P.r :=
    CutEXPbRight.castM_nset _ (BigCellDiagonalMap.leviElement_nset u hu)
  unfold CutEX.pbTop CutEX.psiU PBQ.pbT CutEX.xT
  rw [← Ux4.mMap_mul_muP, castM_mul_eq_mul_castM]
  exact PBQ.pbF_right _ _ _ _ _ _ hm

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXTopPt
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutEXTop

theorem domR_pt (k i r' : ℕ) (hr' : r' = 0) (zs zs' : Fin (2 * r' + k + 1) → ℂ) (x : (Fin (i + r') → ℂ) × Q.Mx k (i + r'))
    (hx : x ∈ Q.DomR k (i + r') (liftVec k i r' zs) (liftVec k i r' zs')) :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = ιLev k i r' g := by
  subst hr'
  obtain ⟨-, hxG, hxP⟩ := hx
  have himg := Formalism.FourierDecayAlt.P.level_group_image k i 0
  have hxG' : x.2 ∈ Q.Glev k (i + 0) ⟨i, by omega⟩ := hxG
  rw [himg] at hxG'
  obtain ⟨g, hgU, hgx⟩ := hxG'
  refine ⟨g, ⟨hgU, fun a => a.elim0⟩, ?_, hgx.symm⟩
  rw [← Formalism.FourierDecayAlt.P.WordCorrespondence.ggl_lift zs zs' g, hgx]
  exact hxP

theorem domR_pt_cast (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0) {z z' : Fin (2 * n + k + 1) → ℂ}
    {zs zs' : Fin (2 * r' + k + 1) → ℂ} (hz : D.castV hn (liftVec k i r' zs) = z)
    (hz' : D.castV hn (liftVec k i r' zs') = z') (x : (Fin n → ℂ) × Q.Mx k n) (hx : x ∈ Q.DomR k n z z') :
    ∃ g : Q.Mx k r', g ∈ Q.Glev k r' (Fin.last r') ∧ 0 < Q.GGl k r' zs zs' g ∧ x.2 = D.castM hn (ιLev k i r' g) := by
  subst hn
  subst hz
  subst hz'
  obtain ⟨g, h1, h2, h3⟩ := domR_pt k i r' hr' zs zs' x hx
  exact ⟨g, h1, h2, h3⟩

theorem gv_iff_glev (k ρ : ℕ) (hρ : ρ = 0) (γ : B.Mat k ρ) : γ ∈ B.GV k ρ ↔ γ ∈ Q.Glev k ρ (Fin.last ρ) := by
  subst hρ
  constructor
  · intro h
    exact ⟨h, fun a => a.elim0⟩
  · intro h
    exact h.1

end Formalism.FourierDecayAlt.P.CutEXTop

open Formalism.FourierDecayAlt.P.CutEXTop in
theorem Formalism.FourierDecayAlt.P.top_point_existence : Formalism.FourierDecayAlt.P.CutEX.TopPt := by
  intro Wp Wq _ _ _ _ _ _ P p
  refine ⟨fun x hx => ?_, fun γ => gv_iff_glev P.k (P.r - P.r) (by omega) γ⟩
  exact domR_pt_cast P.k P.r P.r (P.r - P.r) (by omega) (by omega) (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) x hx
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralPositive
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.VecVAppendSingletonEqVecVSliceAt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OuterInt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section inst

variable {k r : ℕ} (σ : Equiv.Perm (Fin r))

instance borelRC : BorelSpace (U.RC k r 0) := Prod.borelSpace

instance borelXiH : BorelSpace (U.XiH r 0 σ) := by
  have : BorelSpace ((U.LW σ → ℂ) × (G.UT r → ℂ)) := Prod.borelSpace
  have : BorelSpace ((Fin 0 → Fin r → ℂ) × (Fin r → Fin 0 → ℂ)) := Prod.borelSpace
  exact Prod.borelSpace

end inst

section cont

variable {k r : ℕ}

theorem lowS_cont (w : Equiv.Perm (Fin r)) : Continuous (StabilizerDisintegration.lowS w) := by
  unfold StabilizerDisintegration.lowS C2.lowOf
  refine continuous_const.add ?_
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.of_apply]
  refine continuous_finsetSum _ fun q _ => ?_
  split_ifs
  · exact continuous_apply q
  · exact continuous_const

theorem Amat_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) : Continuous (Amat σ d) := by
  unfold Amat
  exact (continuous_const.matrix_mul (lowS_cont σ.symm)).matrix_mul continuous_const

theorem Amat_inv_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) :
    Continuous fun x => (Amat σ d x)⁻¹ := by
  have e : (fun x => (Amat σ d x)⁻¹) = fun x => (Amat σ d x).adjugate := by
    funext x; exact Dx2.SL.inv_adj _ (StabilizerDisintegration.UC.det_UT (conjS_UT hd x))
  rw [e]; exact (Amat_cont σ d).matrix_adjugate

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : B.Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi; rw [Complex.norm_exp]; simp

theorem norm_Gpsi (β x : ℂ) : ‖G.psi β x‖ = 1 := by
  unfold G.psi; rw [Complex.norm_exp]; simp

theorem norm_psiStar (σ : Equiv.Perm (Fin r)) (z z' : Fin (2 * (r + 0 + 0) + k + 1) → ℂ) (ξ : U.Xi k r 0 0 σ) :
    ‖U.psiStar k 0 σ z z' ξ‖ = 1 := by
  rw [psiStar_zero, norm_mul, norm_mul, norm_psi, norm_star, norm_psi, norm_Gpsi]; norm_num

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) : Continuous fun g : B.Mat k r => psi k r z c g := by
  unfold psi ell
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul ?_))))
  refine continuous_finsetSum _ fun a _ => ?_
  split_ifs
  · exact (continuous_apply _).comp (continuous_apply _)
  · fun_prop

theorem psiStar_cont (σ : Equiv.Perm (Fin r)) (z z' : Fin (2 * (r + 0 + 0) + k + 1) → ℂ) :
    Continuous (U.psiStar k 0 σ z z') := by
  have e : U.psiStar k 0 σ z z' = fun ξ : U.Xi k r 0 0 σ => psi k r z cStd (U.Rn k r 0 ξ.1.1) *
      star (psi k r z' cStd (U.Rn k r 0 ξ.1.2)) *
      G.psi U.betaU (U.subS (U.wP σ * U.lowW σ ξ.2.2.1 * (U.wP σ)⁻¹) + U.supS (G.upper ξ.2.2.2)) := by
    funext ξ; exact psiStar_zero σ z z' ξ
  rw [e]
  refine ((((psi_cont z cStd).comp ((Dx2.SplitF.rn_cont r 0).comp (continuous_fst.comp continuous_fst))).mul
    (continuous_star.comp ((psi_cont z' cStd).comp ((Dx2.SplitF.rn_cont r 0).comp
      (continuous_snd.comp continuous_fst))))).mul ?_)
  unfold G.psi
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (Continuous.add ?_ ?_)))))
  · unfold U.subS
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · exact ((((continuous_const.matrix_mul ((Dx2.SL.cont_lowW σ).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))).matrix_mul continuous_const)).matrix_elem _ _)
    · exact continuous_const
  · unfold U.supS
    refine continuous_finsetSum _ fun a _ => ?_
    split_ifs
    · exact ((StabilizerDisintegration.UC.cont_upper.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_elem _ _)
    · exact continuous_const

def gaX (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (γ : B.Mat k 0) (ξ : U.Xi k r 0 0 σ) : B.Mat k (r + 0 + 0) :=
  U.gaXi k 0 σ d ξ (fun a => a.elim0) γ

theorem gaX_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) (γ : B.Mat k 0) :
    Continuous (gaX σ d γ) := by
  have h := (gaXi_cont (k := k) σ d hd).comp (Continuous.prodMk_left (X := U.Xi k r 0 0 σ) γ)
  exact h

theorem FgaX_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ)
    (hd : ∀ i, d i ≠ 0) (F : B.Mat k r → E) (hFc : ContinuousOn F (B.GV k r)) (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) :
    Continuous fun ξ : U.Xi k r 0 0 σ => F (gaX σ d γ ξ) := by
  have hm : ∀ ξ : U.Xi k r 0 0 σ, gaX σ d γ ξ ∈ B.GV k (r + 0 + 0) := fun ξ => gaXi_mem_GV σ d hd ξ γ hγ
  have h := ContinuousOn.comp_continuous (f := gaX σ d γ) (s := B.GV k (r + 0 + 0)) hFc (gaX_cont σ d hd γ) hm
  exact h

instance muXi_sfinite (σ : Equiv.Perm (Fin r)) : SFinite (U.muXi k r 0 0 σ) := by
  unfold U.muXi; infer_instance

end cont

section inner

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]

def conjL (S : B.RealPlaceData k r Wp Wq) (h h' : Mt k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (S.π (Matrix.of h))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (S.π' (Matrix.of h')⁻¹))

theorem conjL_apply (S : B.RealPlaceData k r Wp Wq) (h h' : Mt k r) (X : Wq →L[ℂ] Wp) :
    conjL S h h' X = (S.π (Matrix.of h)).comp (X.comp (S.π' (Matrix.of h')⁻¹)) := rfl

theorem norm_conjL_le (S : B.RealPlaceData k r Wp Wq) (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z)
    (hh' : Matrix.of h' ∈ UWset k r S.z') (X : Wq →L[ℂ] Wp) : ‖conjL S h h' X‖ ≤ ‖X‖ := by
  rw [conjL_apply]
  have h1 : ‖S.π (Matrix.of h)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [S.π_unitary _ hh v, one_mul]
  have hi : (Matrix.of h')⁻¹ ∈ UWset k r S.z' := WeylGroupFacts.uw_inv hh'
  have h2 : ‖S.π' (Matrix.of h')⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [S.π'_unitary _ hi v, one_mul]
  calc ‖(S.π (Matrix.of h)).comp (X.comp (S.π' (Matrix.of h')⁻¹))‖
      ≤ ‖S.π (Matrix.of h)‖ * (‖X‖ * ‖S.π' (Matrix.of h')⁻¹‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖X‖ * 1) := by gcongr
    _ = ‖X‖ := by ring

theorem chiL_integrable (w0 : Equiv.Perm (Fin r)) : Integrable (chiL w0) := by
  unfold chiL
  refine (integrableOn_const (C := (1 : ℝ)) ?_).integrable_indicator (MeasurableSet.univ_pi fun _ => boxC_meas)
  rw [volume_pi, Measure.pi_pi]
  simp [boxC_vol]


set_option maxHeartbeats 1000000 in
theorem inner_int (S : B.RealPlaceData k r Wp Wq) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ)
    (h h' : Mt k r) (hh : Matrix.of h ∈ UWset k r S.z) (hh' : Matrix.of h' ∈ UWset k r S.z') :
    Integrable (fun q : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) =>
        theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
          D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2))))
        ((QN k r).prod (QN k r)) ∧
      ∫ q, theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
          D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2)))
        ∂((QN k r).prod (QN k r)) =
        conjL S h h' (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of h))⁻¹ * γ0 * midB r 0 (Matrix.of h'))) ∧
      ∫ q, ‖theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
          D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2)))‖
        ∂((QN k r).prod (QN k r)) ≤ M * (U.muXi k r 0 0 σ Bs).toReal := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  set y1 := midB r 0 (Matrix.of h) with hy1
  set y1' := midB r 0 (Matrix.of h') with hy1'
  have hhL : Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0) := by rw [← hz]; exact hh
  have hhL' : Matrix.of h' ∈ UWset k (r + 0) (liftVec k r 0 z0') := by rw [← hz']; exact hh'
  have hy1W : y1 ∈ UWset k 0 z0 := uw_mid r 0 z0 _ hhL
  have hy1W' : y1' ∈ UWset k 0 z0' := uw_mid r 0 z0' _ hhL'
  have uy1 : IsUnit y1.det := gv_unit hy1W.1
  have uy1' : IsUnit y1'.det := gv_unit hy1W'.1
  have hγ' : y1⁻¹ * γ0 * y1' ∈ B.GV k 0 := by
    have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k 0
    exact hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hy1W.1) _ hγ0) _ hy1W'.1
  have hAUT : ∀ x, Amat σ d x ∈ C2.UTset r := conjS_UT hd
  have hAc : ∀ i j, Measurable fun x => Amat σ d x i j := fun i j => ((Amat_cont σ d).matrix_elem i j).measurable
  have hAi : ∀ i j, Measurable fun x => (Amat σ d x)⁻¹ i j :=
    fun i j => ((Amat_inv_cont σ d hd).matrix_elem i j).measurable
  have hmp := phiC_mp σ y1 y1' (Amat σ d) hAUT hAc hAi hy1W.1 hy1W'.1
  have hemb := phiC_emb σ y1 y1' (Amat σ d) hAUT hAc hAi uy1 uy1'
  set g : (U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ)) → (Wq →L[ℂ] Wp) := fun q =>
    theta0 S.z σ.symm (TN k r ((h, q.1), (h', q.2))) •
      D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F (TN k r ((h, q.1), (h', q.2))) with hg
  set φ : U.Xi k r 0 0 σ → (Wq →L[ℂ] Wp) := fun ξ =>
    U.psiStar k 0 σ S.z S.z' ξ • F (U.gaXi k 0 σ d ξ (fun a => a.elim0) (y1⁻¹ * γ0 * y1')) with hφ
  have hcomp : g ∘ phiC σ y1 y1' (Amat σ d) = fun p => chiL σ.symm p.1 • conjL S h h' (φ p.2) := by
    funext p
    rw [conjL_apply]
    exact integrand_pw S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F h h' hh hh' p

  have hφc : Continuous φ := (psiStar_cont σ S.z S.z').smul (FgaX_cont σ d hd F hFc _ hγ')
  have hφb : ∀ ξ, ‖φ ξ‖ ≤ Bs.indicator (fun _ => M) ξ := by
    intro ξ
    rw [hφ, norm_smul, norm_psiStar, one_mul]
    exact hdom ξ _ hγ'
  have hφi : Integrable φ (U.muXi k r 0 0 σ) := by
    refine Integrable.mono' ((integrableOn_const (C := M) hBsf.ne).integrable_indicator hBs)
      hφc.aestronglyMeasurable (Filter.Eventually.of_forall hφb)
  have hGi : Integrable (fun ξ => conjL S h h' (φ ξ)) (U.muXi k r 0 0 σ) := (conjL S h h').integrable_comp hφi
  have hpi : Integrable (fun p : (C2.Lstidx σ.symm → ℂ) × U.Xi k r 0 0 σ => chiL σ.symm p.1 • conjL S h h' (φ p.2))
      ((volume : Measure (C2.Lstidx σ.symm → ℂ)).prod (U.muXi k r 0 0 σ)) :=
    (chiL_integrable σ.symm).smul_prod hGi
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmp.integrable_comp_emb hemb, hcomp]; exact hpi
  · rw [← hmp.integral_comp hemb g]
    change ∫ p, (g ∘ phiC σ y1 y1' (Amat σ d)) p ∂_ = _
    rw [hcomp]
    dsimp only
    rw [integral_prod_smul (chiL σ.symm) (fun ξ => conjL S h h' (φ ξ)), chiL_int, one_smul,
      (conjL S h h').integral_comp_comm hφi]
    rfl
  · have e1 := hmp.integral_comp hemb (fun q => ‖g q‖)
    rw [← e1]
    have e2 : (fun p => ‖g (phiC σ y1 y1' (Amat σ d) p)‖) = fun p => chiL σ.symm p.1 * ‖conjL S h h' (φ p.2)‖ := by
      funext p
      have := congrFun hcomp p
      simp only [Function.comp_apply] at this
      rw [this, norm_smul, Real.norm_of_nonneg (chiL_nonneg _ _)]
    rw [e2, integral_prod_mul (chiL σ.symm) (fun ξ => ‖conjL S h h' (φ ξ)‖), chiL_int, one_mul]
    calc ∫ ξ, ‖conjL S h h' (φ ξ)‖ ∂(U.muXi k r 0 0 σ) ≤ ∫ ξ, Bs.indicator (fun _ => M) ξ ∂(U.muXi k r 0 0 σ) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((integrableOn_const (C := M) hBsf.ne).integrable_indicator hBs)
            (Filter.Eventually.of_forall fun ξ => (norm_conjL_le S h h' hh hh' _).trans (hφb ξ))
      _ = M * (U.muXi k r 0 0 σ Bs).toReal := by
          rw [integral_indicator hBs, setIntegral_const, smul_eq_mul, mul_comm, Measure.real]

end inner

end Formalism.FourierDecayAlt.P.PBM
end
end

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section outer

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]


set_option maxHeartbeats 1000000 in
theorem outer_int (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ) :
    Integrable (fun p => theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS ∧
      ∫ p, theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p ∂S.μSS =
        ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hsW : SigmaFinite S.μW := Dx2.OrbJ.sigmaF S.haarW
  have hsW' : SigmaFinite S.μW' := Dx2.OrbJ.sigmaF S.haarW'
  have hfW : IsFiniteMeasure S.μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure S.μW' := ⟨by rw [hW1']; exact ENNReal.one_lt_top⟩
  set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ
  have hγG : γ ∈ B.GV k r := by
    have := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
    exact this
  set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf
  have hfm : AEStronglyMeasurable f S.μSS :=
    (theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)

  have hSS := muSS_eq S hN
  set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP
  have hfm' : AEStronglyMeasurable f (P.map (TN k r)) := by rw [← hSS]; exact hfm
  have hTm : AEMeasurable (TN k r) P := TN_meas.aemeasurable
  set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2
  have hsw := Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)
  set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) :=
    fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2
  have hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α := Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r)
      (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by
    funext x; rfl
  have hfTm : AEStronglyMeasurable (f ∘ TN k r) P := hfm'.comp_aemeasurable hTm
  have hG2m : AEStronglyMeasurable G2 P2 := by
    rw [hG2e]
    exact hfTm.comp_measurePreserving (hsw.symm _)

  have hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  have hin := fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' =>
    inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2
  have hG2i : Integrable G2 P2 := by
    rw [integrable_prod_iff hG2m]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with x hx using (hin x hx).1
    · refine Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hin x hx).2.2

  have hfTi : Integrable (f ∘ TN k r) P := by
    have := (hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)
    rw [← this, ← hG2e]; exact hG2i
  refine ⟨?_, ?_⟩
  · rw [hSS]; exact (integrable_map_measure hfm' hTm).2 hfTi
  · rw [hSS, integral_map hTm hfm']
    have e := (hsw.symm _).integral_comp' (f ∘ TN k r)
    change ∫ x, (f ∘ TN k r) x ∂P = _
    rw [← e]
    change ∫ x, G2 x ∂P2 = _
    rw [hP2, integral_prod G2 hG2i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx using (hin x hx).2.1

theorem orbJ_mMap (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0))
    (w : Equiv.Perm (Fin (r + 1))) (dd : Fin (r + 1) → ℂ) (hdd : ∀ a, dd a ≠ 0)
    (hZw : Zhat k r S.z S.z' (U.mMap k r 0 (U.hMat σ d) γ0) = C2.monoP w dd)
    (hw : ∀ a : Fin r, w.symm a.castSucc = (σ a).castSucc)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hFc : ContinuousOn F (B.GV k r)) (hr : 1 ≤ r) (R : ℝ)
    (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    D.orbJ S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) F =
      ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
        ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  obtain ⟨M, Bs, hBs, hBsf, hdom⟩ := slice_dom k r hr σ d hd F hFc R hFs
  obtain ⟨hint, heq⟩ := outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom
  have hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
  have hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc := by simpa using hw
  have hnc := theta0_normCut S hγG hdd hZw σ.symm hw'
  have hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧
      Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS :=
    ⟨_, hnc, hint⟩
  unfold D.orbJ
  rw [dite_eq_left hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel
    (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc
    hex.choose_spec.2 hint, heq]

end outer

end Formalism.FourierDecayAlt.P.PBM
end
end

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section helpers

variable {k : ℕ}

theorem cast_cancel (a : ℕ) (h1 : a = 0) (h2 : 0 = a) (γ : B.Mat k 0) : h1 ▸ D.castM h2 γ = γ := by
  subst h1; exact Dx2.MN.castM_rfl γ

theorem phiFun_tr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R j ρ' : ℕ) (hj : j = R) (hρ : ρ' = 0)
    (σ : Equiv.Perm (Fin j)) (d : Fin j → ℂ) (z z' : Fin (2 * R + k + 1) → ℂ) (F : B.Mat k R → E)
    (e1 : R = j + 0 + ρ') (e2 : j + 0 + ρ' = R) (γ : B.Mat k ρ') :
    U.PhiFun (s := 0) k ρ' σ d (D.castV e1 z) (D.castV e1 z') (D.castF e2 F) (fun a => a.elim0) γ =
      U.PhiFun (s := 0) k 0 (hj ▸ σ) (hj ▸ d) z z' F (fun a => a.elim0) (hρ ▸ γ) := by
  subst hj; subst hρ
  have h1 : D.castV e1 z = z := Dx2.Tower.castV_rfl z
  have h2 : D.castV e1 z' = z' := Dx2.Tower.castV_rfl z'
  have h3 : D.castF e2 F = F := by funext g; exact congrArg F (Dx2.MN.castM_rfl g)
  rw [h1, h2, h3]

theorem ptMatN_one (ζ : ℂ) : D.ptMatN [(1, ζ)] (0 + 1) = Matrix.of fun _ _ => ζ := by
  ext a b
  have ha : a.val = 0 := by have := a.isLt; omega
  have hb : b.val = 0 := by have := b.isLt; omega
  simp [D.ptMatN, D.ptEntry, ha, hb]

theorem ptMatN_append_head (h : C.LPt) (ζ : ℂ) (R : ℕ) (hR : D.ptSize h = R) :
    D.ptMatN (h ++ [(1, ζ)]) R = D.ptMatN h R := by
  ext a b
  simp only [D.ptMatN, ptEntry_append, hR, a.isLt, b.isLt, and_self, if_true]

theorem isLocPt_app (h : C.LPt) (R : ℕ) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0) :
    D.IsLocPt (h ++ [(1, ζ)]) (R + 1) := by
  refine ⟨fun b hb => ?_, CompactCoefficientAppend.ptSize_app h R hh ζ⟩
  rcases List.mem_append.1 hb with hb | hb
  · exact hh.1 b hb
  · simp at hb; subst hb; exact ⟨le_refl _, hζ⟩

theorem Tz_lift (R : ℕ) (v : Fin (2 * 0 + k + 1) → ℂ) : Tz k (R + 0) (liftVec k R 0 v) = Tz k 0 v := by
  unfold Tz; rw [herm_lift]

end helpers

section master

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem lev_inv {k R : ℕ} (y : B.Mat k 0) (hy : IsUnit y.det) : ιLev k R 0 y⁻¹ = (ιLev k R 0 y)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Dx2.Tower.lev_mul, Matrix.nonsing_inv_mul _ hy, Dx2.Tower.lev_one]


set_option maxHeartbeats 1000000 in
theorem vecV_append_singleton_eq_vecV_sliceAt (k R ρ : ℕ) (hρ : ρ = 0) (e : R + ρ = R) (S : B.RealPlaceData k R Wp Wq) (S0 : B.RealPlaceData k ρ Wp Wq)
    (hzL : D.castV e (liftVec k R ρ S0.z) = S.z) (hzL' : D.castV e (liftVec k R ρ S0.z') = S.z')
    (hπ : ∀ y, S0.π y = S.π (D.castM e (ιLev k R ρ y))) (hπ' : ∀ y, S0.π' y = S.π' (D.castM e (ιLev k R ρ y)))
    (hN : S.μN = D.muN k R) (hW1 : S.μW Set.univ = 1) (hW1' : S.μW' Set.univ = 1)
    (hW01 : S0.μW Set.univ = 1) (hW01' : S0.μW' Set.univ = 1) (hN0 : S0.μN = D.muN k ρ)
    (ν' : Fin (2 * R + k + 1) → ℂ) (m₀ : B.Mat k R) (ν'r : Fin (2 * ρ + k + 1) → ℂ) (m₀r : B.Mat k ρ)
    (hν : D.castV e (liftVec k R ρ ν'r) = ν') (hm : D.castM e (ιLev k R ρ m₀r) = m₀)
    (hFb : D.IsBaseFrame S ν' m₀) (hF0 : D.IsBaseFrame S0 ν'r m₀r)
    (h : C.LPt) (hh : D.IsLocPt h R) (ζ : ℂ) (hζ : ζ ≠ 0)
    (F : B.Mat k R → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef S F) (hR : 1 ≤ R) (e' : ρ = R - D.ptSize h) :
    D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = D.vecV S0 ν'r m₀r (D.castF e' (D.sliceAt k R S.z S.z' F h)) [(1, ζ)] := by
  subst hρ
  have hzS : S.z = liftVec k R 0 S0.z := by rw [← hzL]; exact (Dx2.Tower.castV_rfl _).symm
  have hzS' : S.z' = liftVec k R 0 S0.z' := by rw [← hzL']; exact (Dx2.Tower.castV_rfl _).symm
  have hνS : ν' = liftVec k R 0 ν'r := by rw [← hν]; exact Dx2.Tower.castV_rfl _
  have hmS : m₀ = ιLev k R 0 m₀r := by rw [← hm]; exact Dx2.MN.castM_rfl _
  have hT : Tz k R S.z = Tz k 0 S0.z := by rw [hzS]; exact Tz_lift R S0.z
  have hT' : Tz k R S.z' = Tz k 0 S0.z' := by rw [hzS']; exact Tz_lift R S0.z'
  obtain ⟨hZh, hdR, hQmono, hdd, hw⟩ := CompactCoefficientAppend.perm_app h R hh ζ hζ
  set σR := hh.2 ▸ D.ptPerm h with hσR
  set dR := hh.2 ▸ D.ptDiag h with hdRdef
  set Z := U.hMat σR dR with hZdef
  have hZu : IsUnit Z.det := by rw [hZdef, hMat_monoP]; exact C2x2.isUnit_det_monomialMatrix _ _ hdR
  have hq := isLocPt_app h R hh ζ hζ
  have hG : D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) =
      Complex.normSq (D.ptMatN h R).det * (Complex.normSq ζ - Tz k R S.z * Tz k R S.z') := by
    unfold D.ptG
    rw [ptMatN_append_one h ζ R hh.2, det_extendOne, ptMatN_append_head h ζ R hh.2, Complex.normSq_mul]
    ring
  have hdetpos : 0 < Complex.normSq (D.ptMatN h R).det := by
    rw [← hZh]; exact Complex.normSq_pos.2 hZu.ne_zero
  by_cases hζT : Complex.normSq ζ ≤ Tz k R S.z * Tz k R S.z'
  · have hL : D.vecV S ν' m₀ F (h ++ [(1, ζ)]) = 0 := by
      unfold D.vecV
      rw [dite_eq_right]
      rintro ⟨_, hpos⟩
      rw [hG] at hpos
      nlinarith
    rw [hL, vector_level_zero_degenerate rfl S0 ν'r m₀r _ ζ (by rw [← hT, ← hT']; exact hζT)]
  push_neg at hζT
  have hζT0 : Tz k 0 S0.z * Tz k 0 S0.z' < Complex.normSq ζ := by rw [← hT, ← hT']; exact hζT
  obtain ⟨γ0, hγ0G, hZ0, hD0⟩ := exists_frame_level_zero rfl S0 ν'r m₀r hF0 ζ hζT0
  rw [vector_level_zero_eq_jacquet rfl S0 ν'r m₀r hF0 _ ζ hζT0 γ0 hγ0G hZ0 hD0, jacquet_integral_level_zero rfl S0 hN0 _ γ0]
  have hZ0' : Zhat k 0 S0.z S0.z' γ0 = Matrix.of fun _ _ => ζ := by rw [hZ0, ptMatN_one]
  have hγG : U.mMap k R 0 Z γ0 ∈ B.GV k R := (Formalism.FourierDecayAlt.P.slice_membership k R 0).1 Z γ0 hZu.ne_zero hγ0G
  have hZhat : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) = D.ptMatN (h ++ [(1, ζ)]) (R + 1) := by
    have h1 := zhat_mMap (j := R) S.z S.z' S.z_mem S.z'_mem Z γ0
    refine h1.trans ?_
    rw [hzS, hzS', lowV_liftVec, lowV_liftVec, hZ0', ptMatN_append_one h ζ R hh.2, hZh]
  have hDγ : D.IsDFrame S ν' m₀ (U.mMap k R 0 Z γ0) := by
    rw [hνS, hmS]
    exact dFrame_mMap S S0 hzS hzS' ν'r m₀r Z hZu γ0 (gv_unit hγ0G) ζ hζ hZ0' hD0
  have hpos : 0 < D.ptG (Tz k R S.z * Tz k R S.z') R (h ++ [(1, ζ)]) := by
    rw [hG]; exact mul_pos hdetpos (by linarith)
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k R Wp Wq S ν' m₀ F _ hq _ hFb hpos hγG hZhat hDγ]
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k R Wp Wq S _ _ hq hγG hZhat
  obtain ⟨hFc, Rb, hFs⟩ := CompactCoefficientAppend.cptCoef_cont_supp S F hF
  have hZw : Zhat k R S.z S.z' (U.mMap k R 0 Z γ0) =
      C2.monoP (hq.2 ▸ D.ptPerm (h ++ [(1, ζ)])) (hq.2 ▸ D.ptDiag (h ++ [(1, ζ)])) := by
    rw [hZhat]; exact hQmono
  rw [orbJ_mMap S hN hW1 hW1' S0.z S0.z' hzS hzS' σR dR hdR γ0 hγ0G hrel _ _ hdd hZw hw F hFc hR Rb hFs]

  have hsW0 : SigmaFinite S0.μW := Dx2.OrbJ.sigmaF S0.haarW
  have hsW0' : SigmaFinite S0.μW' := Dx2.OrbJ.sigmaF S0.haarW'
  have hH := haar_lev R 0 e S0.z S.z hzL S.μW S0.μW S.haarW S0.haarW hW1 hW01
  have hH' := haar_lev R 0 e S0.z' S.z' hzL' S.μW' S0.μW' S.haarW' S0.haarW' hW1' hW01'
  rw [hH, hH', Measure.map_prod_map _ _ (levMt_cont R 0 e).measurable (levMt_cont R 0 e).measurable,
    ((levMt_emb R 0 e).prodMap (levMt_emb R 0 e)).integral_map]
  have hae : ∀ᵐ y ∂(S0.μW.prod S0.μW'), Matrix.of y.1 ∈ UWset k 0 S0.z ∧ Matrix.of y.2 ∈ UWset k 0 S0.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S0.μW) (ν := S0.μW')).ae (Dx2.OrbJ.ae_mem S0.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  obtain ⟨y1, y2⟩ := y
  have hlev : ∀ x : Mt k 0, Matrix.of (levMt R 0 e x) = ιLev k R 0 (Matrix.of x) := by
    intro x; simp only [levMt, Equiv.apply_symm_apply]; exact Dx2.MN.castM_rfl _
  simp only [Prod.map_apply, conjL_apply, hlev, midB_lev]
  have hy2u : IsUnit (Matrix.of y2).det := gv_unit hy.2.1
  rw [← lev_inv _ hy2u, hπ (Matrix.of y1), hπ' (Matrix.of y2)⁻¹, Dx2.MN.castM_rfl, Dx2.MN.castM_rfl]
  congr 2

  show _ = D.sliceAt k R S.z S.z' F h (D.castM e' ((Matrix.of y1)⁻¹ * γ0 * Matrix.of y2))
  unfold D.sliceAt
  rw [dite_eq_left (by rw [hh.2]), phiFun_tr R (D.ptSize h) (R - D.ptSize h) hh.2 (by rw [hh.2]; simp),
    cast_cancel]

end master

end Formalism.FourierDecayAlt.P.PBM
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopUnipotentIntegralRankZero
noncomputable section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CompactCoefficientAppend

theorem locPt_zero {h : C.LPt} {n : ℕ} (hh : D.IsLocPt h n) (hn : n = 0) : h = [] := by
  rcases h with _ | ⟨b, t⟩
  · rfl
  · exfalso
    have h1 := (hh.1 b (by simp)).1
    have h2 := hh.2
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_cons] at h2
    omega

theorem top_unipotent_integral_zero (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r)) (hR : P.r = 0)
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have hh0 : h = [] := locPt_zero hh hR
  subst hh0
  rcases P with ⟨k, r, T, T', u, u'⟩
  dsimp only at hR
  subst hR
  have e1 : p.ν' = ν'r := by
    rw [← hν]
    funext i
    simp only [D.castV, liftVec]
    rw [dite_eq_left (by simp; omega)]
    exact congrArg ν'r (Fin.ext (by simp))
  have e2 : p.m₀ = m₀r := by
    rw [← hm]
    ext i j
    simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev]
    rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    exact congrArg₂ m₀r (Fin.ext (by simp)) (Fin.ext (by simp))
  have e3 : D.castF (by simp) (D.sliceAt k 0 p.T.base.z p.T.base.z' F []) = F := by
    funext γ
    simp only [D.castF]
    refine (Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k 0 _ _ p.T.base.z_mem p.T.base.z'_mem F _).trans ?_
    exact congrArg F (Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl γ)
  simp only [List.nil_append]
  rw [e3]
  subst e1
  subst e2
  rfl

end Formalism.FourierDecayAlt.P.CompactCoefficientAppend

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

theorem top_unipotent_integral_positive (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (h : C.LPt) (ζ : ℂ) (hh : D.IsLocPt h P.r)
    (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (m₀r : B.Mat P.k (P.r - P.r))
    (hF : KB.CptCoef p.T.base F) (hζ : ζ ≠ 0)
    (hν : D.castV (by omega) (liftVec P.k P.r (P.r - P.r) ν'r) = p.ν')
    (hm : D.castM (by omega) (ιLev P.k P.r (P.r - P.r) m₀r) = p.m₀) (hR : 1 ≤ P.r) :
    p.V F (h ++ [(1, ζ)]) =
      D.vecV (p.T.bs P.r) ν'r m₀r
        (D.castF (by simp [hh.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F h)) [(1, ζ)] := by
  have h0 := p.hT 0 (Nat.zero_le _)
  have hr := p.hT P.r le_rfl
  exact vecV_append_singleton_eq_vecV_sliceAt P.k P.r (P.r - P.r) (Nat.sub_self _) (by omega) p.T.base (p.T.bs P.r)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    h0.2.2 h0.1 h0.2.1 hr.1 hr.2.1 hr.2.2 p.ν' p.m₀ ν'r m₀r hν hm p.hF
    (CompactCoefficientAppend.baseFrame_last p ν'r m₀r hν hm) h hh ζ hζ F hF hR _

theorem highestUnipotentIntegral : PBI.HighestUnipotentIntegral := by
  intro Wp Wq _ _ _ _ _ _ P p F h ζ hh ν'r m₀r hF hζ hν hm
  by_cases hR : P.r = 0
  · exact CompactCoefficientAppend.top_unipotent_integral_zero Wp Wq P p F h ζ hh ν'r m₀r hR hF hζ hν hm
  · exact top_unipotent_integral_positive Wp Wq P p F h ζ hh ν'r m₀r hF hζ hν hm (by omega)

end Formalism.FourierDecayAlt.P.PBM

namespace Formalism.FourierDecayAlt.P

theorem top_unipotent_integral : PBI.HighestUnipotentIntegral := PBM.highestUnipotentIntegral

end Formalism.FourierDecayAlt.P
end
end

namespace Formalism.FourierDecayAlt.P

theorem pb_exhPic_of_mkTop (hMk : CutEX.MkTop) : PBI.ExhPic :=
  CutEX.exhPic_of_leaves CutEX.exceptional_assumption_holds unipotent_weight_top slice_top_exhaustion pullback_smooth
    pullback_right_action pullback_support pullback_equivalence hMk compact_truncation_construction top_point_existence
    determinant_exceptional_holds head_family_exhaustion radial_slice_top radial_of_function_exceptional radial_extension_exceptional
    residue_top_exceptional_level frame_parameter_regularity (pb_radWordSliceOfHeadPic head_picture) level_zero_picture_of_slice

theorem pb_headTop_of_mkTop (hMk : CutEX.MkTop) : KB.HeadTop :=
  pb_headTop_of top_unipotent_integral (pb_exhPic_of_mkTop hMk)

end Formalism.FourierDecayAlt.P
