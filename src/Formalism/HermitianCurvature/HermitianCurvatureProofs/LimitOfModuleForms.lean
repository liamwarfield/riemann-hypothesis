module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMapApplyFirstBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainX1

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
open Filter Topology

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem limit_of_module_forms : Formalism.FourierDecayAlt.KB.FormLimit := by
  intro Cb
  obtain ⟨Cl, _, hL⟩ := PBE.belowTop
  obtain ⟨Ct, hT⟩ := PBE.formLimit_top Cb
  refine ⟨max Cl Ct, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P0 p f χ ε A N cut hDD hχ hε hf hfA hA hcut
  refine ⟨fun n => PBE.cutCpt P0 p.T.base f χ ε cut hχ hε hf hcut n, ?_⟩
  intro i w hwc hw a b
  have hX : 0 ≤ ((P0.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3) := by
    positivity
  rcases lt_trichotomy i (P0.r + 1) with hlt | heq | hgt
  · exact hL (max Cl Ct) (le_max_left _ _) Wp Wq P0 p f χ ε A N cut hχ hε hf hfA hA hcut i (by omega) w hw a b
  · subst heq
    refine hT Wp Wq P0 p f χ ε A N cut hDD hχ hε hf hfA ?_ hcut w hwc hw a b
    refine le_trans ?_ hA
    have := mul_le_mul_of_nonneg_right (le_max_right Cl Ct) hX
    nlinarith
  · have h0 : ∀ F, p.RR F i w a b = 0 := by
      intro F
      unfold KB.Pl.RR D.RRplace
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [h0]
    exact tendsto_const_nhds

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal
namespace Formalism.FourierDecayAlt.P.CutMP

theorem energy_reality_holds : EnergyReal :=
  ER.energyReal_of_capAdjInt (ER.capAdjInt_of_scalar ER.capacity_adjoint_scalar)

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

theorem haarSmul {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Mt k r)} (h : B.IsHaarOn U μ) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hcT : c ≠ ∞) : B.IsHaarOn U (c • μ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.conc, smul_zero]
  · intro a ha
    rw [Measure.map_smul c (B2x5.measurable_lmulM a).aemeasurable, h.left a ha]
  · intro a ha
    rw [Measure.map_smul c (B2x5.measurable_rmulF a).aemeasurable, h.right a ha]
  · intro K hK
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hcT) (h.finite_compact K hK)
  · intro h0
    apply h.ne_zero
    have := congrArg (fun ν : Measure (Mt k r) => c⁻¹ • ν) h0
    simpa [smul_smul, ENNReal.inv_mul_cancel hc0 hcT] using this

section norm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem massW_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW.ne_zero

theorem massW'_ne_zero (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ 0 :=
  Measure.measure_univ_ne_zero.2 Bs.haarW'.ne_zero

theorem massW_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z_mem Bs.T_pos Bs.haarW
  exact measure_ne_top _ _

theorem massW'_ne_top (Bs : B.RealPlaceData k r Wp Wq) : Bs.μW' Set.univ ≠ ∞ := by
  have := Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.haar_finite Formalism.FourierDecayAlt.P.B2x3.compactW Bs.z'_mem Bs.T'_pos Bs.haarW'
  exact measure_ne_top _ _

def normS (Bs : B.RealPlaceData k r Wp Wq) : B.RealPlaceData k r Wp Wq :=
  { Bs with
    μW := (Bs.μW Set.univ)⁻¹ • Bs.μW
    μW' := (Bs.μW' Set.univ)⁻¹ • Bs.μW'
    μN := D.muN k r
    haarW := haarSmul Bs.haarW (ENNReal.inv_ne_zero.2 (massW_ne_top Bs)) (ENNReal.inv_ne_top.2 (massW_ne_zero Bs))
    haarN := Formalism.FourierDecayAlt.P.Dx2.MN.haar r
    haarW' := haarSmul Bs.haarW' (ENNReal.inv_ne_zero.2 (massW'_ne_top Bs))
      (ENNReal.inv_ne_top.2 (massW'_ne_zero Bs)) }

theorem normS_μW_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW Set.univ = 1 := by
  show ((Bs.μW Set.univ)⁻¹ • Bs.μW) Set.univ = 1
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW_ne_zero Bs) (massW_ne_top Bs)]

theorem normS_μW'_univ_eq_one (Bs : B.RealPlaceData k r Wp Wq) : (normS Bs).μW' Set.univ = 1 := by
  show ((Bs.μW' Set.univ)⁻¹ • Bs.μW') Set.univ = 1
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel (massW'_ne_zero Bs) (massW'_ne_top Bs)]

end norm

theorem towerAt : Formalism.FourierDecayAlt.P.PTie.TowerAt := by
  intro k r Wp Wq _ _ _ _ Bs
  obtain ⟨T, hT, hN⟩ := Formalism.FourierDecayAlt.P.exists_level_tower k r Wp Wq (normS Bs) (normS_μW_univ_eq_one Bs) (normS_μW'_univ_eq_one Bs) rfl
  exact ⟨T, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, by rw [hT]; rfl, hN⟩

section frame

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem herm_mulVec' {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hg]

theorem frameVec_facts (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r)
    (hF : D.IsBaseFrame Bs ν' m₀) :
    inWb k r (m₀ *ᵥ ν') ∧ herm (Hpk k r) (m₀ *ᵥ ν') Bs.z = 0 ∧ herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by
  obtain ⟨hw, hz, hn, hm, hmz⟩ := hF
  have hU : m₀ᴴ * Hpk k r * m₀ = Hpk k r := hm.1
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.inWb_mulVec hm hw, ?_, by rw [herm_mulVec' hU]; exact hn⟩
  have h0 : herm (Hpk k r) (m₀ *ᵥ ν') (m₀ *ᵥ Bs.z') = 0 := by rw [herm_mulVec' hU]; exact hz
  rw [hmz] at h0
  set c : ℂ := ((√(Tz k r Bs.z' / Tz k r Bs.z) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (Real.sqrt_pos.mpr (div_pos Bs.T'_pos Bs.T_pos)).ne'
  have e : herm (Hpk k r) (m₀ *ᵥ ν') (c • Bs.z) = star c * herm (Hpk k r) (m₀ *ᵥ ν') Bs.z := by
    unfold herm
    rw [star_smul, smul_dotProduct, smul_eq_mul]
  rw [e] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (star_eq_zero.mp h) hc0
  · exact h

theorem frame_of (Bs : B.RealPlaceData k r Wp Wq) : ∃ (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r),
    D.IsBaseFrame Bs ν' m₀ := by
  obtain ⟨Fb, hBw, hBo, hBz⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists Bs.z'_mem Bs.T'_pos
  set T : ℝ := Tz k r Bs.z with hTdef
  set T' : ℝ := Tz k r Bs.z' with hT'def
  have hT : 0 < T := Bs.T_pos
  have hT' : 0 < T' := Bs.T'_pos
  set c : ℝ := √(T' / T) with hc
  have hcc : c * c = T' / T := Real.mul_self_sqrt (div_pos hT' hT).le
  have hcw : inWb k r ((c : ℂ) • Bs.z) := Formalism.FourierDecayAlt.P.Qx8.inWb_smul Bs.z_mem _
  have hz' : herm (Hpk k r) Bs.z' Bs.z' = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_self']; push_cast; rfl
  have hcz : herm (Hpk k r) ((c : ℂ) • Bs.z) ((c : ℂ) • Bs.z) = ((-T' : ℝ) : ℂ) := by
    rw [Formalism.FourierDecayAlt.P.Qx8.herm_smul_left', Formalism.FourierDecayAlt.P.Qx8.herm_smul_right', Formalism.FourierDecayAlt.P.Qx8.herm_self']
    have hs : star (c : ℂ) = c := Complex.conj_ofReal c
    rw [hs, ← hTdef]
    have hTne : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have e1 : (c : ℂ) * (c : ℂ) = (T' : ℂ) / (T : ℂ) := by
      rw [← Complex.ofReal_mul, hcc]; push_cast; rfl
    rw [show (c : ℂ) * ((c : ℂ) * -(T : ℂ)) = -((c : ℂ) * (c : ℂ)) * (T : ℂ) by ring, e1]
    push_cast
    field_simp
  obtain ⟨m, hm, hmz, -⟩ := Formalism.FourierDecayAlt.P.Qx8.move Bs.z'_mem hcw (-T') (by linarith) hz' hcz
  refine ⟨Fb ⟨0, by have := Bs.k_pos; omega⟩, m, hBw _, hBz _ _ (List.mem_singleton_self _), ?_, hm, hmz⟩
  rw [hBo, ite_eq_left rfl]

end frame

end Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature

namespace Formalism.FourierDecayAlt.P

theorem exists_normalized_tower : Formalism.FourierDecayAlt.P.PTie.TowerAt := HaarMassHermitianCurvature.towerAt

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjCont
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_sgs (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) (g : B.Mat k r) :
    Gf k r D.z D.z' (B.sgs p g) = Gf k r D.z D.z' g := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hn1 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ ∈ Q.Nlev k r 0 := by
    refine ⟨Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn, ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact (Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb.n_inv_mem hn).1
  have hn2 : (Matrix.of p.2.2 : B.Mat k r) ∈ Q.Nlev k r 0 := by
    refine ⟨hn', ?_⟩
    rw [Formalism.FourierDecayAlt.P.CutMP.ER.CAS.level_zero_set_eq_group]
    exact hn'.1
  have e1 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hh))
    (Formalism.FourierDecayAlt.P.CutMP.h_mem_Sset D.z' hh') ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * g * Matrix.of p.2.2)
  have e2 := Formalism.FourierDecayAlt.P.CutMP.gf_SgS D (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z hn1)
    (Formalism.FourierDecayAlt.P.CutMP.n_mem_Sset D.z' hn2) g
  unfold B.sgs
  rw [← e2, ← e1]
  congr 1
  simp only [mul_assoc]

theorem sgs_mem (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {g : B.Mat k r}
    (hg : g ∈ B.GV k r) : B.sgs p g ∈ B.GV k r := by
  rw [Formalism.FourierDecayAlt.P.B5.sgs_eq]
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
    (Formalism.FourierDecayAlt.P.NFRadRedLocSec.uh_inv_mem (Formalism.FourierDecayAlt.P.B5.inSS_left D hp)) hg) (Formalism.FourierDecayAlt.P.B5.inSS_right D hp)

theorem sgs_continuous (p : B.SS k r) : Continuous (B.sgs p : B.Mat k r → B.Mat k r) := by
  unfold B.sgs
  exact (((continuous_const : Continuous fun _ : B.Mat k r =>
    (Matrix.of p.1.1 : B.Mat k r)⁻¹ * (Matrix.of p.1.2 : B.Mat k r)⁻¹).matrix_mul continuous_id).matrix_mul
    continuous_const).matrix_mul continuous_const

theorem suppIn_rho (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p) {F : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hF : B.SuppIn (B.GPos D) F) : B.SuppIn (B.GPos D) (B.rho D p F) := by
  intro x hx
  have hxG : x ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.B5.GV_closed (k := k) (r := r)).closure_subset_iff.2 (by exact fun y hy => hy.1) hx
  have hsub : {g | g ∈ B.GV k r ∧ B.rho D p F g ≠ 0} ⊆ B.sgs p ⁻¹' {g | g ∈ B.GV k r ∧ F g ≠ 0} := by
    intro y hy
    refine ⟨sgs_mem D hp hy.1, fun h0 => hy.2 ?_⟩
    unfold B.rho
    rw [h0]
    simp
  have h1 : x ∈ B.sgs p ⁻¹' closure {g | g ∈ B.GV k r ∧ F g ≠ 0} :=
    (sgs_continuous p).closure_preimage_subset _ (closure_mono hsub hx)
  have h2 := hF h1
  refine ⟨hxG, ?_⟩
  have := h2.2
  rwa [gf_sgs D hp] at this

variable [FiniteDimensional ℂ Wq]

theorem ckOn_opAdj (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hs : B.SmoothCoef (B.GPos D) Θ)
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn ⊤ (B.GV k r) F) (hFs : B.SuppIn (B.GPos D) F) :
    B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) := by
  unfold B.opAdj
  refine Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_list_sum Θ
    (fun T g => ((-1 : ℂ) ^ T.word.length) • B.Rw T.word.reverse (fun x => T.coefAdj x (F x)) g) (fun T hT => ?_)
  exact Formalism.FourierDecayAlt.P.JCx2.ckOn_smul' _ (Formalism.FourierDecayAlt.P.JFxI.ckOn_Rw_top' (Formalism.FourierDecayAlt.P.B5.ckOn_coef (hs T hT).2 hF hFs)
    T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)))

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

open Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC

theorem adjoint_continuity_holds : AdjCont := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ hs f hf _ hfs p hp
  exact ⟨Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_opAdj D Θ hs (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hf) (suppIn_rho D hp hfs)),
    Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp (ckOn_opAdj D Θ hs hf hfs))⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtNormPow
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.GaugeNormPower

open Formalism.QuantumDeterminants

theorem hasDerivAt_normPow (z v : ℂ) (hz : z ≠ 0) (n : ℕ) :
    HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ n)
      ((n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2)) 0 := by
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hsq : HasDerivAt (fun t : ℝ => ‖z + t • v‖ ^ 2) (2 * (v * conj z).re) 0 := by
    have := hline.norm_sq
    simpa [Complex.inner] using this
  have h0 : (fun t : ℝ => ‖z + t • v‖ ^ 2) 0 ≠ 0 := by simpa using pow_ne_zero 2 hz'
  have hsqrt := hsq.sqrt h0
  have hn : (fun t : ℝ => √(‖z + t • v‖ ^ 2)) = fun t => ‖z + t • v‖ := by
    funext t; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [hn] at hsqrt
  have hv : (n : ℝ) * ‖z + (0 : ℝ) • v‖ ^ (n - 1) * (2 * (v * conj z).re / (2 * √(‖z + (0 : ℝ) • v‖ ^ 2))) =
      (n : ℝ) * ‖z‖ ^ n * ((v * conj z).re / ‖z‖ ^ 2) := by
    simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg _)]
    rcases n with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
      ring
  have hp := (hsqrt.pow n).congr_deriv hv
  exact hp

theorem hasDerivAt_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    HasDerivAt (fun t : ℝ => ∏ a, ‖(c + t • (Pi.single l v : Fin r → ℂ)) a‖ ^ n a)
      ((n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2)) 0 := by
  classical
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (f := fun a (t : ℝ) => ‖c a + t • (Pi.single l v : Fin r → ℂ) a‖ ^ n a)
    (fun a _ => hasDerivAt_normPow (c a) ((Pi.single l v : Fin r → ℂ) a) (hc a) (n a))
  have hv : (∑ i, (∏ j ∈ Finset.univ.erase i, ‖c j + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) j‖ ^ n j) •
        ((n i : ℝ) * ‖c i‖ ^ n i * (((Pi.single l v : Fin r → ℂ) i * conj (c i)).re / ‖c i‖ ^ 2))) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
    rw [Finset.sum_eq_single l]
    · simp only [Pi.single_eq_same, zero_smul, add_zero, smul_eq_mul]
      rw [← Finset.mul_prod_erase Finset.univ (fun a => ‖c a‖ ^ n a) (Finset.mem_univ l)]
      ring
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h; exact absurd (Finset.mem_univ l) h
  exact h.congr_deriv hv

theorem fderiv_prodPow (r : ℕ) (n : Fin r → ℕ) (c : Fin r → ℂ) (hc : c ∈ OmX r) (l : Fin r) (v : ℂ) :
    DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c ∧
    fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v) =
      (n l : ℝ) * (∏ a, ‖c a‖ ^ n a) * ((v * conj (c l)).re / ‖c l‖ ^ 2) := by
  classical
  have hd : DifferentiableAt ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c := by
    have := HasFDerivAt.finsetProd (u := Finset.univ) (x := c)
      (g := fun a (x : Fin r → ℂ) => ‖x a‖ ^ n a)
      (fun a _ => (((differentiableAt_apply (𝕜 := ℝ) a c).norm ℂ (hc a)).pow (n a)).hasFDerivAt)
    exact this.differentiableAt
  refine ⟨hd, ?_⟩
  have hline : HasDerivAt (fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ)) (Pi.single l v) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l v : Fin r → ℂ)).const_add c
  have hc0 : c + (0 : ℝ) • (Pi.single l v : Fin r → ℂ) = c := by simp
  have h1 : HasDerivAt ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) ∘ fun t : ℝ => c + t • (Pi.single l v : Fin r → ℂ))
      (fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l v)) 0 := by
    have hd' := hd.hasFDerivAt
    rw [← hc0] at hd'
    have := hd'.comp_hasDerivAt (0 : ℝ) hline
    rwa [hc0] at this
  exact h1.unique (hasDerivAt_prodPow r n c hc l v)

theorem gauge_scalar (z : ℂ) (hz : z ≠ 0) (m : ℕ) (P : ℝ) :
    z * ((1 / 2 : ℂ) * ((((m : ℝ) * P * ((1 * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ) -
      Complex.I * (((m : ℝ) * P * ((Complex.I * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ))) = (P : ℂ) * ((m : ℂ) / 2) := by
  have h1 : (1 * conj z).re = z.re := by simp
  have h2 : (Complex.I * conj z).re = z.im := by simp
  have hc : ((z.re : ℂ)) - Complex.I * (z.im : ℂ) = conj z := by apply Complex.ext <;> simp
  have hzz : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hN0 : (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [h1, h2]
  push_cast
  calc _ = ((m : ℂ) * P / 2) * (z * ((z.re : ℂ) - Complex.I * (z.im : ℂ))) / (‖z‖ : ℂ) ^ 2 := by ring
    _ = (P : ℂ) * ((m : ℂ) / 2) := by
      have hN1 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [hc, hzz]; field_simp

end Formalism.FourierDecayAlt.P.GaugeNormPower

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.GaugeNormPower

theorem gauge_positivity : PBN.GaugeP := by
  intro E _ _ r n H c hc hH l
  obtain ⟨hψ, hψ'⟩ := fderiv_prodPow r n c hc l 1
  obtain ⟨-, hψI⟩ := fderiv_prodPow r n c hc l Complex.I
  have hfun : (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') =
      (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H := by
    funext c'; exact Complex.coe_smul _ _
  rw [hfun]
  have hD : ∀ w, fderiv ℝ ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H) c w =
      (∏ a, ‖c a‖ ^ n a) • fderiv ℝ H c w + fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c w • H c := by
    intro w
    rw [(hψ.hasFDerivAt.smul hH.hasFDerivAt).fderiv]
    simp
  have hs : c l * ((1 / 2 : ℂ) * (((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l 1) : ℝ) : ℂ) -
      Complex.I * ((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l Complex.I) : ℝ) : ℂ))) =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) * ((n l : ℂ) / 2) := by
    rw [hψ', hψI]
    exact gauge_scalar (c l) (hc l) (n l) _
  simp only [pOp, if_pos hc, wirt]
  rw [hD, hD]
  simp only [← Complex.coe_smul]
  linear_combination (norm := module) hs • H c

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RootVectorActionCutoff
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section alg

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}

def cI (p : Fin (2 * r + k + 1)) : Fin (mdim k r 0) := ⟨p.val, by have := p.isLt; simp [mdim]; omega⟩

theorem posL_cI (p : Fin (2 * r + k + 1)) : posL k r 0 (cI p) = p := Fin.ext (by simp [posL, cI])

theorem cI_inj : Function.Injective (cI (k := k) (r := r)) := fun p q h => Fin.ext (by
  have := congrArg Fin.val h; simpa [cI] using this)


variable (E) in
abbrev SA (hD : IsOpen D) : Subalgebra ℂ (Module.End ℂ (VS k r 0 D E)) :=
  Algebra.adjoin ℂ (Set.range fun p : Fin (mdim k r 0) × Fin (mdim k r 0) => Eh (E := E) (i := 0) hD p.1 p.2)

def EA (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : SA E hD :=
  ⟨Eh hD (cI p) (cI q), Algebra.subset_adjoin ⟨(cI p, cI q), rfl⟩⟩

theorem EA_val (hD : IsOpen D) (p q : Fin (2 * r + k + 1)) : (EA (E := E) hD p q : Module.End ℂ (VS k r 0 D E)) =
    Eh hD (cI p) (cI q) := rfl

theorem EA_gl (hD : IsOpen D) : GlRel (EA (E := E) hD) := by
  intro a b c d
  apply Subtype.ext
  have h := Eh_gl (E := E) (i := 0) hD (cI a) (cI b) (cI c) (cI d)
  simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, EA_val]
  rw [h]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos (congrArg cI hbc), if_pos hbc]; rfl
    · rw [if_neg (fun e => hbc (cI_inj e)), if_neg hbc]; rfl
  · by_cases hda : d = a
    · rw [if_pos (congrArg cI hda), if_pos hda]; rfl
    · rw [if_neg (fun e => hda (cI_inj e)), if_neg hda]; rfl

def La (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) : SA E hD →ₗ[ℂ] E where
  toFun x := ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g
  map_add' x y := by simp
  map_smul' c x := by simp

theorem La_apply (hD : IsOpen D) (v : VS k r 0 D E) (g : Mx k r) (x : SA E hD) :
    La hD v g x = ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) g := rfl

theorem leftEq_SA (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (x : SA E hD) :
    ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) →
      LeftEq k r z 0 D ((x : Module.End ℂ (VS k r 0 D E)) v : Mx k r → E) := by
  obtain ⟨x, hx⟩ := x
  show ∀ v : VS k r 0 D E, LeftEq k r z 0 D (v : Mx k r → E) → LeftEq k r z 0 D (x v : Mx k r → E)
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨p, rfl⟩ := hy
    intro v hv g hg n hn
    have hng : n * g ∈ Glev k r 0 ∩ D := ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩
    rw [ev_E hD p.1 p.2 v hng, ev_E hD p.1 p.2 v hg]
    exact ((generator_action_preserved E k r z 0 D p.1 p.2 (v : Mx k r → E) (v : Mx k r → E) 1 hD v.2.1 v.2.1).2.1 hN hv) g hg n hn
  | algebraMap c =>
    intro v hv g hg n hn
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg n hn, smul_comm]
  | add y₁ y₂ _ _ h₁ h₂ =>
    intro v hv g hg n hn
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h₁ v hv g hg n hn, h₂ v hv g hg n hn, smul_add]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    intro v hv
    exact h₁ _ (h₂ v hv)

abbrev Tor (hD : IsOpen D) (j : ℕ) : Subalgebra ℂ (SA E hD) :=
  Algebra.adjoin ℂ {x | ∃ l : Fin r, j ≤ l.val ∧ x = EA hD (eI k r l) (eI k r l)}

theorem comm_Tor (hD : IsOpen D) (j : ℕ) (p q : Fin (2 * r + k + 1))
    (hp : ∀ l : Fin r, j ≤ l.val → p ≠ eI k r l) (hq : ∀ l : Fin r, j ≤ l.val → q ≠ eI k r l) (P : SA E hD)
    (hP : P ∈ Tor hD j) : Commute (EA hD p q) P := by
  induction hP using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    have h := EA_gl (E := E) hD p q (eI k r l) (eI k r l)
    rw [if_neg (hq l hl), if_neg (fun e => hp l hl e.symm), sub_zero] at h
    exact sub_eq_zero.1 h
  | algebraMap c => exact Algebra.commute_algebraMap_right c _
  | add y₁ y₂ _ _ h₁ h₂ => exact h₁.add_right h₂
  | mul y₁ y₂ _ _ h₁ h₂ => exact h₁.mul_right h₂

theorem Tor_mono (hD : IsOpen D) {j j' : ℕ} (h : j ≤ j') : Tor (E := E) hD j' ≤ Tor hD j :=
  Algebra.adjoin_mono fun _ ⟨l, hl, e⟩ => ⟨l, h.trans hl, e⟩

theorem EA_mem_Tor (hD : IsOpen D) (l : Fin r) {j : ℕ} (h : j ≤ l.val) :
    EA (E := E) hD (eI k r l) (eI k r l) ∈ Tor hD j :=
  Algebra.subset_adjoin ⟨l, h, rfl⟩

end alg

section qm

theorem map_qminor {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) :
    φ (qminor E a b u) = qminor (fun p q => φ (E p q)) a b u := by
  unfold qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  congr 1
  funext k
  simp only [Function.comp_apply, Tm, map_add]
  split_ifs <;> simp

theorem qminor_reindex {A : Type} [Ring A] [Algebra ℂ A] {n n' t : ℕ} (E : Fin n' → Fin n' → A) (ι : Fin n → Fin n')
    (hι : Function.Injective ι) (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun p q => E (ι p) (ι q)) a b u = qminor E (ι ∘ a) (ι ∘ b) u := by
  unfold qminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  congr 1
  congr 1
  funext l
  simp only [Tm, Function.comp_apply]
  by_cases h : a (σ l) = b l
  · rw [if_pos h, if_pos (congrArg ι h)]
  · rw [if_neg h, if_neg (fun e => h (hι e))]

end qm

section main

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)

theorem gauge_last (c : Fin r → ℂ) :
    (∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1)) =
      ∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) :=
  Finset.prod_congr rfl fun a _ => if_pos a.isLt

theorem resG_last (J : Mx k r → E) (c : Fin r → ℂ) (g : Mx k r) :
    Q.resG k r (Fin.last r) J c g = ((∏ a : Fin r, ‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ) • J (wCell k r (Fin.last r) c * g) := by
  unfold Q.resG
  rw [gauge_last]

theorem root_vector_action_cutoff (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (hRR : RightRuleE) {f : Mx k r → E}
    (hf : SmoothLev k r 0 D f) (hRf : RightEq k r z' 0 D f) (a b : Fin r) (hab : a.val < b.val) :
    ((EA hD (eI k r a) (eI k r b) : SA E hD) : Module.End ℂ (VS k r 0 D E)) ⟨cut k r 0 D f, cut_mem hD hf⟩ =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • ⟨cut k r 0 D f, cut_mem hD hf⟩ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r 0 ∩ D
  · rw [EA_val, ev_E hD _ _ _ hg]
    have hloc := (good_eh (E := E) hD (cI (eI k r a)) (cI (eI k r b))).loc (cut k r 0 D f) f
      (fun x hx => cut_of_mem f hx) g hg
    simp only [posL_cI] at hloc
    rw [posL_cI, posL_cI]
    show EH k r (eI k r a) (eI k r b) (cut k r 0 D f) g = (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [hloc, hRR E k r z' D f hz' hD hf hRf g hg a b hab, cut_of_mem f hg]
  · show ((Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩ : VS k r 0 D E) : Mx k r → E) g =
      (if b.val = a.val + 1 then (1 : ℂ) else 0) • cut k r 0 D f g
    rw [(Eh hD (cI (eI k r a)) (cI (eI k r b)) ⟨cut k r 0 D f, cut_mem hD hf⟩).2.2 g hg,
      show cut k r 0 D f g = 0 from Set.indicator_of_notMem hg f, smul_zero]

end main

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationAlgebraicHolds
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix Polynomial
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem gv_facts {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 ∧ Hpk k r * g = (g⁻¹)ᴴ * Hpk k r ∧ gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
  obtain ⟨-, hHH, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
  have hg0 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg0, hHH]
  have hr : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp hl
  have hinv : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv hl
  have hgi : g⁻¹ * g = 1 := by rw [hinv]; exact hl
  have hig : g * g⁻¹ = 1 := by rw [hinv]; exact hr
  refine ⟨hgi, hig, ?_, ?_⟩
  · calc Hpk k r * g = ((g⁻¹)ᴴ * gᴴ) * Hpk k r * g := by
          rw [← Matrix.conjTranspose_mul, hig, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hg0]
  · calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hig, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg0]

theorem conjugation_algebraic_holds : ConjAlg := by
  intro k r g hg
  obtain ⟨hgi, hig, hHg, hgH⟩ := gv_facts hg
  refine ⟨fun A hA => ?_, fun A hA => ?_, fun A h0 => ?_, fun A X => ?_⟩
  · unfold B.inLie at hA ⊢
    have e1 : (g * A * g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (Aᴴ * Hpk k r) * g⁻¹ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [hgH]
    have e2 : Hpk k r * (g * A * g⁻¹) = (g⁻¹)ᴴ * (Hpk k r * A) * g⁻¹ := by
      simp only [← Matrix.mul_assoc]
      rw [hHg]
    rw [e1, e2, ← Matrix.add_mul, ← Matrix.mul_add, hA, Matrix.mul_zero, Matrix.zero_mul]
  · obtain ⟨n, hn⟩ := hA
    refine ⟨n, ?_⟩
    have hp : ∀ m : ℕ, (g * A * g⁻¹) ^ m = g * A ^ m * g⁻¹ := by
      intro m
      induction m with
      | zero => simp [hig]
      | succ m ih =>
        rw [pow_succ, ih, pow_succ]
        calc g * A ^ m * g⁻¹ * (g * A * g⁻¹) = g * A ^ m * (g⁻¹ * g) * A * g⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = g * (A ^ m * A) * g⁻¹ := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hp, hn, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    apply h0
    calc A = (g⁻¹ * g) * A * (g⁻¹ * g) := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
      _ = g⁻¹ * (g * A * g⁻¹) * g := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
  · have e : (g * A * g⁻¹) * (g * X * g⁻¹) = g * (A * X * g⁻¹) := by
      calc (g * A * g⁻¹) * (g * X * g⁻¹) = g * A * (g⁻¹ * g) * X * g⁻¹ := by simp only [Matrix.mul_assoc]
        _ = g * (A * X * g⁻¹) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelPointCoordinates
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section cell

variable {k ρ : ℕ}

theorem finRange_one_add (ρ : ℕ) :
    List.finRange (1 + ρ) = (⟨0, by omega⟩ : Fin (1 + ρ)) :: (List.finRange ρ).map PBH.shS := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    rcases i with _ | i
    · simp
    · simp [PBH.shS]

theorem weyl_cell_shift_eq_level_embedding (a : Fin ρ) (x : ℂ) : w1 k (1 + ρ) (PBH.shS a) x = ιLev k 1 ρ (w1 k ρ a x) := by
  ext ⟨p, hp⟩ ⟨q, hq⟩
  have ha := a.isLt
  unfold w1 ιLev
  simp only [eI, esI, PBH.shS, Fin.mk.injEq]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega)

theorem iota_list_prod (l : List (Mx k ρ)) : ιLev k 1 ρ l.prod = (l.map (ιLev k 1 ρ)).prod := by
  induction l with
  | nil => simpa using Formalism.FourierDecayAlt.P.Dx2.Tower.lev_one (k := k) 1 ρ
  | cons a l ih => rw [List.prod_cons, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, ih, List.map_cons, List.prod_cons]

theorem wCell_consC (t : ℂ) (c : Fin ρ → ℂ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) =
      w1 k (1 + ρ) ⟨0, by omega⟩ t * ιLev k 1 ρ (wCell k ρ (Fin.last ρ) c) := by
  unfold wCell
  rw [List.filter_eq_self.2 (fun a _ => by simp),
    List.filter_eq_self.2 (fun a _ => by simp), finRange_one_add, iota_list_prod]
  rw [List.map_cons, List.prod_cons, PBH.consC_zero, List.map_map, List.map_map]
  congr 2
  refine List.map_congr_left (fun a _ => ?_)
  simp only [Function.comp, PBH.consC_sh, weyl_cell_shift_eq_level_embedding]

theorem weyl_cell_zero_eq_embedding {t : ℂ} (ht : t ≠ 0) :
    w1 k (1 + ρ) ⟨0, by omega⟩ t = U.mMap k 1 ρ (Matrix.of fun _ _ => t) 1 := by
  have hinv : ((Matrix.of fun _ _ : Fin 1 => t)ᴴ)⁻¹ = Matrix.of fun _ _ : Fin 1 => (star t)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    ext a b
    fin_cases a; fin_cases b
    simp [Matrix.mul_apply, ht]
  ext i l
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective i
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective l
  rw [U.mMap, PBH.weyl_lift_eq_pair, Matrix.mul_one, Matrix.one_mul, hinv, Ux3.block3_apply]
  have hX : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inl (Sum.inl x)) = ⟨0, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_first_val]; simp)
  have hV : ∀ v : Fin (2 * ρ + k + 1), U.eB k 1 ρ (Sum.inl (Sum.inr v)) = ⟨1 + v.val, by omega⟩ := fun v =>
    Fin.ext (by rw [Ux3.block_index_middle_val])
  have hS : ∀ x : Fin 1, U.eB k 1 ρ (Sum.inr x) = ⟨2 * (1 + ρ) + k, by omega⟩ := fun x =>
    Fin.ext (by rw [Ux3.block_index_last_val]; have := x.isLt; simp; omega)
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.of_apply, Matrix.one_apply, hX, hV, hS] <;>
    unfold w1 <;>
    simp only [eI, esI, Fin.ext_iff] <;>
    (have hx := x.isLt; have hy := y.isLt; split_ifs <;> first | rfl | (exfalso; omega) | (simp_all; done) | (simp_all; omega))

theorem cell_iota {t : ℂ} (ht : t ≠ 0) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    wCell k (1 + ρ) (Fin.last (1 + ρ)) (PBH.consC t c) * ιLev k 1 ρ g =
      U.mMap k 1 ρ (Matrix.of fun _ _ => t) (wCell k ρ (Fin.last ρ) c * g) := by
  rw [wCell_consC, Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mul, weyl_cell_zero_eq_embedding ht,
    ← Formalism.FourierDecayAlt.P.Dx2.MN.embG_eq, Formalism.FourierDecayAlt.P.Ux4.mMap_mul_embG, Matrix.one_mul]

theorem gauge_consC (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ a : Fin (1 + ρ), (if a.val < (Fin.last (1 + ρ)).val then ‖PBH.consC t c a‖ ^ (Mdim k (1 + ρ) a - 1)
      else 1 : ℝ)) =
      ‖t‖ ^ (2 * (1 + ρ) + k) *
        ∏ a : Fin ρ, (if a.val < (Fin.last ρ).val then ‖c a‖ ^ (Mdim k ρ a - 1) else 1 : ℝ) := by
  rw [Finset.prod_congr rfl (fun a _ => if_pos (by rw [Fin.val_last]; exact a.isLt)),
    Finset.prod_congr rfl (fun (a : Fin ρ) _ => if_pos (by rw [Fin.val_last]; exact a.isLt))]
  rw [← Fintype.prod_equiv (finCongr (Nat.add_comm ρ 1))
    (fun a : Fin (ρ + 1) => ‖PBH.consC t c (finCongr (Nat.add_comm ρ 1) a)‖ ^
      (Mdim k (1 + ρ) (finCongr (Nat.add_comm ρ 1) a) - 1)) _ (fun _ => rfl)]
  rw [Fin.prod_univ_succ]
  refine congrArg₂ (· * ·) ?_ ?_
  · have h0 : finCongr (Nat.add_comm ρ 1) (0 : Fin (ρ + 1)) = ⟨0, by omega⟩ := Fin.ext rfl
    rw [h0, PBH.consC_zero]
    congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    have hs : finCongr (Nat.add_comm ρ 1) a.succ = PBH.shS a := Fin.ext (by simp [PBH.shS])
    rw [hs, PBH.consC_sh]
    congr 1
    simp only [Mdim, PBH.shS]
    omega

theorem resG_consC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℂ} (ht : t ≠ 0)
    (J : Mx k (1 + ρ) → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k (1 + ρ) (Fin.last (1 + ρ)) J (PBH.consC t c) (ιLev k 1 ρ g) =
      ((‖t‖ ^ (2 * (1 + ρ) + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ)) c g := by
  unfold resG
  rw [cell_iota ht, smul_smul, gauge_consC, ← Complex.ofReal_mul]

theorem resG_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (hn : n = 1 + ρ) {t : ℂ} (ht : t ≠ 0)
    (J : Mx k n → E) (c : Fin ρ → ℂ) (g : Mx k ρ) :
    resG k n (Fin.last n) J (fun l => PBH.consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn.symm (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) c g := by
  subst hn
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact resG_consC ht J c g

end cell

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBP

theorem pb_radHead_of_headPic (hHP : HeadPic) : KB.RadHead :=
  pb_radHead_of module_form_eq_radial_form_one exists_zeta_normalized_haar hHP

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftCapelliAsGenerators
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem clag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Bs : Fin k → Fin (2 * r + k + 1) → ℂ) (w : ℂ) (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun i : Fin k => fun y : Q.Mx k r → E =>
      (if id (σ i) = id i then (w - ((i : ℕ) : ℂ)) • y else 0) +
        Q.LZ (Hpk k r) (Q.unitB (Hpk k r) Bs (id (σ i)) (id i)) y) =
      (capGens (zgB Bs) σ).map (fun gn => genOpL (E := E) gn w) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, genOpL, capGen, zgB, Q.LZ, id, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero, Pi.add_apply]
  split_ifs <;> simp

theorem left_capelli_as_generators : CapLAsGens := by
  intro k r E _ _ Bs w f g
  simp only [Q.capLft, Q.qmFrev, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [List.map_reverse, List.foldr_reverse, clag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorAsGenerators
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff Topology

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cvag_posL_iff {k r : ℕ} (a b : Fin (Q.mdim k r 0)) : Q.posL k r 0 a = Q.posL k r 0 b ↔ a = b := by
  simp [Q.posL, Fin.ext_iff]

theorem cvag_list {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : ℂ)
    (σ : Equiv.Perm (Fin (Q.mdim k r 0))) :
    (List.ofFn fun i : Fin (Q.mdim k r 0) =>
      Top (Q.EH (E := E) k r) (u - ((i : ℕ) : ℂ)) (Q.posL k r 0 (σ i)) (Q.posL k r 0 i)) =
      (capGens (zgCV k r) σ).map (fun gn => genOpR (E := E) gn u) := by
  unfold capGens
  rw [List.map_ofFn]
  congr 1
  funext i F h
  simp only [Function.comp_apply, Formalism.QuantumDeterminants.Top, genOpR, capGen, zgCV, Q.EH, EabH, cvag_posL_iff, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, one_smul, add_zero]
  split_ifs <;> simp

theorem capelli_vector_as_generators : CVAsGens := by
  intro k r E _ _ Y f g
  simp only [Q.CV, Q.capL, qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [cvag_list]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
