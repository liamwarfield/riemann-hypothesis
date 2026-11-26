module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NegMulCCancel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableCsmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixBlockThreeMul
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section what₂

variable {k p ρ : ℕ}

theorem block_three_mul_apply_last (A11 : Matrix (Fin p) (Fin p) ℂ) (A12 : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin p) (Fin p) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (a : Fin p) (c : Fin (2 * (p + ρ) + k + 1)) :
    (U.blk3 A11 A12 A13 A21 A22 A23 0 0 1 * g) (U.eB k p ρ (Sum.inr a)) c = g (U.eB k p ρ (Sum.inr a)) c := by
  rw [Matrix.mul_apply, ← (U.eB k p ρ).sum_comp]
  rw [Finset.sum_eq_single (Sum.inr a)]
  · rw [Ux3.block3_apply]; simp
  · intro q _ hq
    rw [Ux3.block3_apply]
    rcases q with (q | q) | q
    · simp
    · simp
    · have : q ≠ a := fun h => hq (by rw [h])
      simp [Matrix.one_apply, this.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zh_row (a : Fin p) : (⟨2 * (p + ρ) + k - a.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1)) =
    U.eB k p ρ (Sum.inr ⟨p - 1 - a.val, by omega⟩) := by
  ext; rw [Ux3.block_index_last_val]; simp; omega

theorem corner_matrix_block_three_mul (A11 : Matrix (Fin p) (Fin p) ℂ) (A12 : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (A13 : Matrix (Fin p) (Fin p) ℂ) (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (A22 : B.Mat k ρ)
    (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    U.Zh k p ρ (U.blk3 A11 A12 A13 A21 A22 A23 0 0 1 * g) = U.Zh k p ρ g := by
  ext a b
  simp only [U.Zh]
  rw [zh_row, block_three_mul_apply_last]

theorem zh_rn_mul (x : U.RC k p ρ) (g : B.Mat k (p + ρ)) : U.Zh k p ρ (U.Rn k p ρ x * g) = U.Zh k p ρ g := by
  rw [Ux3.rn_eq]; exact corner_matrix_block_three_mul _ _ _ _ _ _ g

theorem zh_embG_mul (y : B.Mat k ρ) (g : B.Mat k (p + ρ)) : U.Zh k p ρ (U.embG k p ρ y * g) = U.Zh k p ρ g := by
  unfold U.embG; exact corner_matrix_block_three_mul _ _ _ _ _ _ g

end what₂

section zh

variable {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem zh_sP_mul (Bj : B.RealPlaceData k ρ Wp Wq) (x : XP k p ρ) (g : B.Mat k (p + ρ)) :
    U.Zh k p ρ (sP Bj x * g) = U.Zh k p ρ g := by
  unfold sP
  split_ifs
  · rw [Matrix.mul_assoc, zh_rn_mul, zh_embG_mul]
  · rw [Matrix.one_mul]

theorem zh_mul_UW (z : Fin (2 * (p + ρ) + k + 1) → ℂ) (g h : B.Mat k (p + ρ)) (hh : h ∈ UWset k (p + ρ) z) :
    U.Zh k p ρ (g * h) = U.Zh k p ρ g := by
  ext a b
  simp only [U.Zh, Matrix.mul_apply]
  have hcol : ∀ c : Fin (2 * (p + ρ) + k + 1), h c ⟨b.val, by omega⟩ = if c.val = b.val then 1 else 0 := by
    intro c
    have h1 := congrFun (hh.2.1 ⟨b.val, by omega⟩).1 c
    have e : eI k (p + ρ) ⟨b.val, by omega⟩ = ⟨b.val, by omega⟩ := rfl
    rw [e] at h1
    rw [← Formalism.FourierDecayAlt.P.PBM.mulVec_bvec_apply h ⟨b.val, by omega⟩ c, h1]
    unfold bvec
    by_cases hcb : c.val = b.val
    · rw [if_pos hcb, Pi.single_apply, if_pos (Fin.ext hcb)]
    · rw [if_neg hcb, Pi.single_apply, if_neg (fun h' => hcb (congrArg Fin.val h'))]
  rw [Finset.sum_eq_single ⟨b.val, by omega⟩]
  · rw [hcol, if_pos rfl, mul_one]
  · intro c _ hc
    rw [hcol, if_neg (fun h' => hc (Fin.ext h')), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem nblk_upper (nn : B.Mat k (p + ρ)) (hn : nn ∈ Nset k (p + ρ)) :
    Matrix.of (fun c b : Fin p => nn ⟨c.val, by omega⟩ ⟨b.val, by omega⟩) =
      G.upper (fun q : G.UT p => nn ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
  ext c b
  simp only [Matrix.of_apply, G.upper, G.strictUpper, Matrix.add_apply, Matrix.one_apply]
  rcases lt_trichotomy c b with hcb | rfl | hcb
  · rw [if_neg (ne_of_lt hcb), dite_eq_left hcb, zero_add]
  · rw [LeftFubiniLemmas.n_col nn hn c _ le_rfl, if_pos rfl, if_pos rfl, dite_eq_right (lt_irrefl _), add_zero]
  · rw [LeftFubiniLemmas.n_col nn hn b _ (le_of_lt hcb), if_neg (by simp only; omega), if_neg (ne_of_gt hcb),
      dite_eq_right (not_lt.mpr (le_of_lt hcb)), add_zero]

end zh

section support

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem pb_head_support (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)) (hCs : IsCompact Cs)
    (hH : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) :
    ∃ R : ℝ, ∀ v : U.LW σ → ℂ, R < ‖v‖ → ∀ g ∈ B.GV k n,
      U.Zh k p ρ (D.castM e.symm g) = LeftFubiniLemmas.lhOf σ v * U.hMat σ d → pbF Bj B0 e H g = 0 := by
  subst e
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 p 0 σ d hd
  have hcont : Continuous (fun c : B.Mat k (p + ρ) => U.mx (U.Zh k p ρ c)) := by
    have e1 : (fun c : B.Mat k (p + ρ) => U.mx (U.Zh k p ρ c)) =
        fun c => ‖(fun a b => c ⟨2 * (p + ρ) + k - a.val, by omega⟩ ⟨b.val, by omega⟩ : Fin p → Fin p → ℂ)‖ := rfl
    rw [e1]
    refine continuous_norm.comp ?_
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply (⟨b.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1))).comp
      (continuous_apply (⟨2 * (p + ρ) + k - a.val, by omega⟩ : Fin (2 * (p + ρ) + k + 1)))
  obtain ⟨M, hM⟩ := hCs.exists_bound_of_continuousOn hcont.continuousOn
  set M0 : ℝ := max M 0 with hM0
  set C0 : ℝ := max C2 0 with hC0
  refine ⟨C0 * M0 ^ p, fun v hv g hg hZ => ?_⟩
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl] at hZ
  unfold pbF
  rw [← integral_zero (XP k p ρ) (Wq →L[ℂ] Wp)]
  refine integral_congr_ae ?_
  filter_upwards [ae_goodP Bj] with x hx
  show pbI Bj B0 rfl H g x = 0
  unfold pbI
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  have hK : PBG.Kr B0 H (sP Bj x * g) = 0 := by
    unfold PBG.Kr
    rw [← integral_zero (Mt k (p + ρ) × Mt k (p + ρ)) (Wq →L[ℂ] Wp)]
    refine integral_congr_ae ?_
    filter_upwards [PBG.ae_inR B0] with ξ hξ
    show _ = 0
    have hc : sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs := by
      intro hcC
      have hZc : U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1) =
          U.headH σ d v (fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩) := by
        rw [zh_mul_UW _ _ _ hξ.1, LeftFubiniLemmas.zh_mul_N _ _ hξ.2, zh_sP_mul, hZ, nblk_upper _ hξ.2,
          (LeftFubiniLemmas.head_hermitian_eq p σ d v _).1]
      set η : U.XiH p 0 σ := ((fun i => i.elim0, fun _ i => i.elim0),
        (v, fun q : G.UT p => (Matrix.of ξ.2 : B.Mat k (p + ρ)) ⟨q.1.1.val, by omega⟩ ⟨q.1.2.val, by omega⟩)) with hη
      have hZj : U.ZjH σ d η (fun i => i.elim0) = U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1) := by
        rw [hZc, LeftFubiniLemmas.lower_corner_hermitian_zero]
      have hb := (hC2 η (fun i => i.elim0)).2.2.1
      rw [hZj] at hb
      have hm := hM _ hcC
      rw [Real.norm_eq_abs, abs_le] at hm
      have hmx0 : 0 ≤ U.mx (U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1)) := norm_nonneg _
      have h1 : U.mx (U.Zh k p ρ (sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1)) ≤ M0 := hm.2.trans (le_max_left _ _)
      have h2 : ‖v‖ ≤ C0 * M0 ^ p := by
        refine hb.trans ?_
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hmx0 h1 p) (pow_nonneg hmx0 _) (le_max_right _ _)
      exact absurd hv (not_lt.mpr h2)
    have hGV : sP Bj x * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∈ B.GV k (p + ρ) := by
      have hs : sP Bj x ∈ B.GV k (p + ρ) := by
        unfold sP
        rw [if_pos hx]
        refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (LeftFubiniLemmas.rn_nset _).1 ?_
        rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
        exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_GV p ρ _
          (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.1.1) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hx.2.1))
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hs hg) hξ.2.1) hξ.1.1
    rw [hH _ hGV hc, ContinuousLinearMap.zero_comp, smul_zero]
  rw [hK, ContinuousLinearMap.comp_zero, smul_zero]

end support

end Formalism.FourierDecayAlt.P.PBQ
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem theta_transfer_on_function : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : Mat k r → (Wq →L[ℂ] Wp)) (Θ : DiffOp k r Wp Wq)
    (UU : Set (Mat k r)), UU ⊆ Om k r D.z D.z' → opOrder Θ ≤ m → Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A m → InCC A m F →
    (∀ p, D.inSS p → ∀ g ∈ UU, opApply Θ (rho D p F) g = rho D p (opApply Θ F) g) →
    ∀ g ∈ UU, opApply Θ (JF D F) g = JF D (opApply Θ F) g := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F Θ UU hUU ho hT hF hC g hgU
  have hg : g ∈ Om k r D.z D.z' := hUU hgU
  have hW := Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak
  have hR := Formalism.FourierDecayAlt.P.rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hCo : CkOn (opOrder Θ : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast ho) hCk
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp g hgU]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

end Formalism.FourierDecayAlt.P

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section adj

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opAdj_local (Θ : B.DiffOp k r Wp Wq) {U : Set (B.Mat k r)} (hU : IsOpen U) {f f' : B.Mat k r → (Wq →L[ℂ] Wp)}
    (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) : ∀ g ∈ U, g ∈ B.GV k r → B.opAdj Θ f g = B.opAdj Θ f' g := by
  intro g hg hgG
  unfold B.opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hU
    (f := fun x => T.coefAdj x (f x)) (f' := fun x => T.coefAdj x (f' x))
    (fun x hx hxG => by simp only [he x hx hxG]) g hg hgG]

theorem adjComm_at (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) (D : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq)
    (hSC : B.SmoothCoef (B.GPos D) Θ) (hC : B.Commutes D (B.GPos D) Θ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV k r) F) (p : B.SS k r) (hp : D.inSS p) (g : B.Mat k r) (hg : g ∈ B.GPos D) :
    B.opAdj Θ (B.rho D p F) g = B.rho D p (B.opAdj Θ F) g := by
  set y := B.sgs p g with hy
  have hyG : y ∈ B.GV k r := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_GV D hp hg.1
  have hyP : 0 < Gf k r D.z D.z' y := by
    rw [hy, Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.gf_sgs D hp g]; exact hg.2
  have hWo : IsOpen {x : B.Mat k r | 0 < Gf k r D.z D.z' x} := isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.BetaSesquilinearity.Gf_cont _ _)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hWo y hyP
  have hbx : ∃ b : ContDiffBump y, b.rIn = ε / 4 ∧ b.rOut = ε / 2 := ⟨⟨ε / 4, ε / 2, by positivity, by linarith⟩, rfl, rfl⟩
  obtain ⟨b, hbi, hbo⟩ := hbx
  set f₁ : B.Mat k r → (Wq →L[ℂ] Wp) := fun x => ((b x : ℝ) : ℂ) • F x with hf₁
  have hbc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hf₁C : B.CkOn ⊤ (B.GV k r) f₁ := Formalism.FourierDecayAlt.P.CutMP.JA.gcut_ckOn_smul hbc hF
  have hf₁cs : HasCompactSupport f₁ := by
    have h0 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
    exact h0.smul_right
  have hf₁S : B.SuppIn (B.GPos D) f₁ := by
    have hcl : IsClosed (Metric.closedBall y (ε / 2) ∩ B.GV k r) := Metric.isClosed_closedBall.inter Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_closed
    have hsub : {x | x ∈ B.GV k r ∧ f₁ x ≠ 0} ⊆ Metric.closedBall y (ε / 2) ∩ B.GV k r := by
      intro x hx
      refine ⟨?_, hx.1⟩
      by_contra hxb
      apply hx.2
      have : b x = 0 := by
        apply b.zero_of_le_dist
        rw [Metric.mem_closedBall, not_le] at hxb
        rw [hbo]; exact hxb.le
      simp [hf₁, this]
    refine (closure_minimal hsub hcl).trans ?_
    intro x hx
    refine ⟨hx.2, hball ?_⟩
    have := hx.1
    rw [Metric.mem_closedBall] at this
    rw [Metric.mem_ball]
    linarith
  have hmain := hAC k r Wp Wq D Θ hSC hC f₁ hf₁C hf₁cs hf₁S p hp g hg
  have hone : ∀ x ∈ Metric.ball y (ε / 4), f₁ x = F x := by
    intro x hx
    have : b x = 1 := b.one_of_mem_closedBall (by rw [hbi]; exact Metric.ball_subset_closedBall hx)
    simp [hf₁, this]
  have hL : B.opAdj Θ (B.rho D p f₁) g = B.opAdj Θ (B.rho D p F) g := by
    have hgV : g ∈ B.sgs p ⁻¹' Metric.ball y (ε / 4) := by
      rw [Set.mem_preimage, ← hy]; exact Metric.mem_ball_self (by positivity)
    have hVo : IsOpen (B.sgs p ⁻¹' Metric.ball y (ε / 4)) :=
      Metric.isOpen_ball.preimage (Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AC.sgs_continuous p)
    refine opAdj_local Θ hVo (fun x hx _ => ?_) g hgV hg.1
    have hx' : B.sgs p x ∈ Metric.ball y (ε / 4) := hx
    unfold B.rho
    rw [hone _ hx']
  have hR : B.opAdj Θ f₁ y = B.opAdj Θ F y :=
    opAdj_local Θ Metric.isOpen_ball (fun x hx _ => hone x hx) y (Metric.mem_ball_self (by positivity)) hyG
  rw [← hL, hmain]
  unfold B.rho
  rw [← hy, hR]

end adj

theorem thetaJ_apply {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hT : Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ)) (hC : B.Commutes Bs (B.GPos Bs) Θ) (hFA : B.InCC A (B.opOrder Θ) F) :
    ∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g := by
  have hOmG : JF.Om k r Bs.z Bs.z' ⊆ B.GPos Bs := jdc_om_sub_gpos Bs
  have hCOm : B.Commutes Bs (JF.Om k r Bs.z Bs.z') Θ := fun p hp f' hf' g hg => hC p hp f' hf' g (hOmG hg)
  exact fun g hg => Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ Bs A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT hFA hCOm g hg

theorem theta_transfer_apply_holds : ThetaJApply := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ A F hT _hS hC _hF hI
  exact thetaJ_apply Bs Θ A F hT hC hI

theorem thetaJ_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : ThetaJ := by
  intro k r Wp Wq _ _ _ _ _ _ Bs Θ A F UU hT hSC hC hF hFA hUU _hCk
  have hOmG : JF.Om k r Bs.z Bs.z' ⊆ B.GPos Bs := jdc_om_sub_gpos Bs
  have hCOm : B.Commutes Bs (JF.Om k r Bs.z Bs.z') Θ := fun p hp f' hf' g hg => hC p hp f' hf' g (hOmG hg)
  refine ⟨fun g hg => Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ Bs A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT hFA hCOm g hg, ?_⟩
  intro g hgU
  have hg : g ∈ JF.Om k r Bs.z Bs.z' := hUU hgU
  have hSCo : B.SmoothCoef (JF.Om k r Bs.z Bs.z') Θ := fun T hT' =>
    ⟨Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hOmG (hSC T hT').1, Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hOmG (hSC T hT').2⟩
  obtain ⟨Θ', hord, hrep⟩ := Formalism.FourierDecayAlt.P.adjoint_leibniz_expansion k r Wp Wq Bs Θ hSCo
  have hsub := Formalism.FourierDecayAlt.P.JFxI.om_sub_gv (k := k) (r := r) Bs.z Bs.z'
  have hFm : B.CkOn (B.opOrder Θ : ℕ∞) (JF.Om k r Bs.z Bs.z') F :=
    Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hsub (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top hF)
  have e1 : B.JF Bs (B.opAdj Θ F) g = B.JF Bs (B.opApply Θ' F) g := by
    change ∫ p, JF.xiP Bs p • B.rho Bs p (B.opAdj Θ F) g ∂Bs.μSS = ∫ p, JF.xiP Bs p • B.rho Bs p (B.opApply Θ' F) g ∂Bs.μSS
    apply integral_congr_ae
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
    have hx' := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs hp hg
    unfold B.rho
    rw [hrep F hFm _ hx']
  have hCF : ∀ p, Bs.inSS p → ∀ x ∈ JF.Om k r Bs.z Bs.z',
      B.opApply Θ' (B.rho Bs p F) x = B.rho Bs p (B.opApply Θ' F) x := by
    intro p hp x hx
    have hρ : B.CkOn (B.opOrder Θ : ℕ∞) (JF.Om k r Bs.z Bs.z') (B.rho Bs p F) :=
      Formalism.FourierDecayAlt.P.JFxI.ckOn_sub hsub (Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (Formalism.FourierDecayAlt.P.B5.ckOn_rho Bs hp hF))
    rw [hrep _ hρ x hx, adjComm_at hAC Bs Θ hSC hC F hF p hp x (hOmG hx)]
    have hx' := Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs hp hx
    unfold B.rho
    rw [hrep F hFm _ hx']
  have e2 := Formalism.FourierDecayAlt.P.theta_transfer_on_function k r Wp Wq Bs A (B.opOrder Θ) F Θ' _ subset_rfl (le_of_eq hord) hT hFA hCF g hg
  have hW := (Formalism.FourierDecayAlt.P.WeakDominationWordBounds.orbital_derivative_words_weak k r Wp Wq Bs A (B.opOrder Θ) F hT hFA).1
  have hJck : B.CkOn (B.opOrder Θ : ℕ∞) (JF.Om k r Bs.z Bs.z') (B.JF Bs F) := by
    intro g₀ hg₀
    obtain ⟨U, F', a, b, c, d⟩ := hW g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀.1, hg₀.2⟩
    exact ⟨U, F', a, b, by exact_mod_cast c, fun x hx hxG => d x hx ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 x).2 hxG)⟩
  rw [e1, ← e2, hrep _ hJck g hg]

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.QminorZero
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN.MC

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2

section claim

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

theorem torus_step (hTC : TorusCell) (hGP : GaugeP) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (l : Fin r) (x : SA E hD) (c : Fin r → ℂ) (hc : c ∈ OmX r) :
    Q.resG k r (Fin.last r) (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
      y • Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c g₀ +
        pOp l (fun c' => Q.resG k r (Fin.last r) (((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E)) c' g₀) c := by
  have hγ := hcell c hc
  set h : Mx k r → E := ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) with hh
  set H : (Fin r → ℂ) → E := fun c' => h (wCell k r (Fin.last r) c' * g₀) with hH
  have e1 : (((Tm (EA hD) ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) (eI k r l) (eI k r l) * x : SA E hD) :
      Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c * g₀) =
      ((y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ)) • H c + pOp l H c := by
    simp only [Tm, Subalgebra.coe_mul, Subalgebra.coe_add, Module.End.mul_apply, LinearMap.add_apply, EA_val,
      Submodule.coe_add, Pi.add_apply, ite_true, if_true, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
      Submodule.coe_smul, Pi.smul_apply]
    rw [ev_E hD _ _ _ hγ, posL_cI, hTC E k r D h hD ((x : Module.End ℂ (VS k r 0 D E)) v₀).2.1 c hc g₀ hg₀ hγ.2 l]
  rw [resG_last, e1]
  simp only [resG_last]
  rw [hGP E r (fun a => Mdim k r a - 1) H c hc (hdiff x c hc) l]
  have hw : (y + ((2 * r + k : ℕ) : ℂ) / 2) - ((l : ℕ) : ℂ) = y + ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    have hl := l.isLt
    have e : Mdim k r l - 1 = 2 * (r - l.val) + k := by simp [Mdim]
    rw [e]
    push_cast [Nat.cast_sub hl.le]
    ring
  rw [hw]
  module

end claim

theorem qminor_one {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 1 → Fin n) (u : ℂ) :
    qminor E a b u = Tm E u (a 0) (b 0) := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp [List.ofFn_succ]

theorem qminor_zero {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (a b : Fin 0 → Fin n) (u : ℂ) :
    qminor E a b u = 1 := by
  unfold qminor
  rw [Fintype.sum_unique]
  simp

section vab

variable {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem vAB_succ (y : ℂ) (i : ℕ) (hi : i < r) (G : (Fin r → ℂ) → V) :
    (Q.vAB r y (i + 1)).1 G = (fun c => y • (Q.vAB r y i).1 G c + pOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) c -
      cOp ⟨i, hi⟩ ((Q.vAB r y i).2 G) c) ∧
    (Q.vAB r y (i + 1)).2 G = ciOp ⟨i, hi⟩ ((Q.vAB r y i).1 G) := by
  simp only [Q.vAB, dif_pos hi]
  exact ⟨funext fun c => rfl, trivial⟩

end vab

section claim2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)} (hD : IsOpen D)
  (v₀ : VS k r 0 D E) (g₀ : Mx k r) (y : ℂ)

theorem leftEq_cut (z : Fin (2 * r + k + 1) → ℂ) (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hLf : LeftEq k r z 0 D f) : LeftEq k r z 0 D (cut k r 0 D f) := by
  intro g hg n hn
  rw [cut_of_mem f ⟨Formalism.FourierDecayAlt.P.Qx3.glev_mul hn.2 hg.1, hN g hg n hn⟩, cut_of_mem f hg]
  exact hLf g hg n hn

theorem claim (hRR : RightRuleE) (hLR : LeftRuleCell) (hTC : TorusCell) (hGP : GaugeP)
    (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D)
    {f : Mx k r → E} (hf : SmoothLev k r 0 D f) (hLf : LeftEq k r z 0 D f) (hRf : RightEq k r z' 0 D f)
    (hv : v₀ = ⟨cut k r 0 D f, cut_mem hD hf⟩) (hg₀ : g₀ ∈ Glev k r (Fin.last r))
    (hcell : ∀ c ∈ OmX r, wCell k r (Fin.last r) c * g₀ ∈ Glev k r 0 ∩ D)
    (hdiff : ∀ x : SA E hD, ∀ c ∈ OmX r,
      DifferentiableAt ℝ (fun c' => ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) (wCell k r (Fin.last r) c' * g₀)) c)
    (hWS : ∀ x : SA E hD, resW ((x : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ ∈ WSm r E) :
    ∀ (m : ℕ) (hm : m ≤ r), ∀ P ∈ Tor hD m, ∀ c ∈ OmX r,
      Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r m hm) (C3.xR k r m hm) (y + ((2 * r + k : ℕ) : ℂ) / 2) * P :
          SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        (Q.vAB r y m).1 (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) c := by
  have hLv : LeftEq k r z 0 D (v₀ : Mx k r → E) := by rw [hv]; exact leftEq_cut z hN hLf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm P hP c hc
  rcases m with _ | _ | m
  · rw [qminor_zero, one_mul]
    rfl
  · rw [qminor_one]
    have hx0 : C3.xR k r 1 hm 0 = eI k r ⟨0, by omega⟩ := by ext; simp [C3.xR, eI]
    have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨0, by omega⟩ P c hc
    simp only [Fin.val_mk, Nat.cast_zero, sub_zero] at hts
    rw [hx0, hts, (vAB_succ y 0 (show 0 < r by omega) _).1]
    simp [Q.vAB, cOp]
  · have hm2 : m + 2 ≤ r := hm
    have hP1 : P ∈ Tor hD (m + 1) := Tor_mono hD (by omega) hP
    have hP0 : P ∈ Tor hD m := Tor_mono hD (by omega) hP
    set u : ℂ := y + ((2 * r + k : ℕ) : ℂ) / 2 with hu
    set LaP : SA E hD →ₗ[ℂ] E := (La hD v₀ (wCell k r (Fin.last r) c * g₀)).comp (LinearMap.mulRight ℂ P) with hLaP
    have hLaP_apply : ∀ x, LaP x = La hD v₀ (wCell k r (Fin.last r) c * g₀) (x * P) := fun x => rfl
    have hnot : ∀ (a : ℕ) (ha : a < m + 2), ∀ l' : Fin r, m + 2 ≤ l'.val → eI k r ⟨a, by omega⟩ ≠ eI k r l' := by
      intro a ha l' hl' e
      have := congrArg Fin.val e
      simp [eI] at this
      omega
    have hR0 : ∀ (x : SA E hD) (l : ℕ) (hl : l < m),
        LaP (x * EA hD (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0 := by
      intro x l hl
      rw [hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot l (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨l, by omega⟩ ⟨m + 1, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, map_zero]
      rfl
    have hR1 : ∀ x : SA E hD, LaP (x * EA hD (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = LaP x := by
      intro x
      rw [hLaP_apply, hLaP_apply, mul_assoc, (comm_Tor hD (m + 2) _ _ (hnot m (by omega)) (hnot (m + 1) (by omega)) P hP).eq,
        ← mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply]
      conv_lhs => rw [hv]
      rw [root_vector_action_cutoff hD z' hz' hRR hf hRf ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by simp), if_pos (by simp), one_smul, ← hv]
    have hL : ∀ (x : SA E hD) (q : ℕ) (hq : q ≤ m),
        LaP (EA hD (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
          (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • LaP x := by
      intro x q hq
      rw [hLaP_apply, hLaP_apply, mul_assoc, La_apply, La_apply, Subalgebra.coe_mul, Module.End.mul_apply, EA_val,
        ev_E hD _ _ _ (hcell c hc), posL_cI, posL_cI]
      have hsm := (((x * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀).2.1
      have hle := leftEq_SA hD z hN (x * P) v₀ hLv
      rw [hLR E k r z D _ hz hD hN hsm hle c hc g₀ hg₀ (hcell c hc).2 ⟨m + 1, by omega⟩ ⟨q, by omega⟩ (by simp; omega)]
      congr 1
      by_cases hqm : q = m
      · subst hqm
        simp
      · rw [if_neg (by simp; omega), if_neg hqm]
    have hX := Formalism.FourierDecayAlt.P.PBN.chainX1' k r c (EA (E := E) hD) LaP (EA_gl (E := E) hD) m hm2 u hR0 hR1 hL

    set T := Tm (EA (E := E) hD) (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) with hT
    have hTmem : T ∈ Tor hD (m + 1) := by
      rw [hT]
      unfold Tm
      rw [if_pos rfl]
      exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (EA_mem_Tor hD ⟨m + 1, by omega⟩ le_rfl)
    have hTP : T * P ∈ Tor hD (m + 1) := Subalgebra.mul_mem _ hTmem hP1
    have ih1 := ih (m + 1) (by omega) (by omega) (T * P) hTP c hc
    have ih0 := ih m (by omega) (by omega) P hP0 c hc

    have eL : Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 2) hm) (C3.xR k r (m + 2) hm) u * P :
        SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ =
        Q.resG k r (Fin.last r) (((qminor (EA hD) (C3.xR k r (m + 1) (by omega)) (C3.xR k r (m + 1) (by omega)) u *
          (T * P) : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • Q.resG k r (Fin.last r)
          (((qminor (EA hD) (C3.xR k r m (by omega)) (C3.xR k r m (by omega)) u * P : SA E hD) :
            Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c g₀ := by
      rw [resG_last, resG_last, resG_last]
      have key : ∀ (s t : ℂ) (a b d : E), a = b - t • d → s • a = s • b - t • (s • d) := by
        intro s t a b d h
        rw [h, smul_sub, smul_comm]
      apply key
      have h2 := hX
      simp only [hLaP_apply, La_apply, mul_assoc] at h2
      exact h2
    rw [eL, ih1, ih0]

    obtain ⟨G', hG'def⟩ : ∃ G' : (Fin r → ℂ) → E,
        G' = resW ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) g₀ := ⟨_, rfl⟩
    have hG' : G' ∈ WSm r E := hG'def ▸ hWS P
    have hGG' : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ = G' c' := by
      intro c' hc'
      rw [hG'def, wsm_resG_eq _ _ hc']
    have hTS : ∀ c' ∈ OmX r,
        Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀ =
          (pOp ⟨m + 1, by omega⟩ G' + y • G') c' := by
      intro c' hc'
      have hts := torus_step hD v₀ g₀ y hTC hGP hg₀ hcell hdiff ⟨m + 1, by omega⟩ P c' hc'
      rw [hT, hts, Pi.add_apply, Pi.smul_apply, hGG' c' hc',
        pOp_locO ⟨m + 1, by omega⟩ (fun c'' hc'' => hGG' c'' hc'') hc', add_comm]
    have vAB_loc : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
        ∀ c ∈ OmX r, (Q.vAB r y i).1 f₁ c = (Q.vAB r y i).1 f₂ c ∧
          (Q.vAB r y i).2 f₁ c = (Q.vAB r y i).2 f₂ c := by
      intro i
      induction i with
      | zero =>
        intro f₁ f₂ h c hc
        exact ⟨h c hc, rfl⟩
      | succ i ih =>
        intro f₁ f₂ h c hc
        by_cases hi : i < r
        · simp only [Q.vAB, dif_pos hi]
          refine ⟨?_, ?_⟩
          · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, cOp]
            rw [(ih f₁ f₂ h c hc).1, (ih f₁ f₂ h c hc).2,
              pOp_locO _ (fun c' hc' => (ih f₁ f₂ h c' hc').1) hc]
          · simp only [ciOp]
            rw [(ih f₁ f₂ h c hc).1]
        · simp only [Q.vAB, dif_neg hi]
          exact ih f₁ f₂ h c hc
    have hl1 := vAB_loc (m + 1)
      (fun c' => Q.resG k r (Fin.last r) (((T * P : SA E hD) : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀)
      (pOp ⟨m + 1, by omega⟩ G' + y • G') hTS c hc
    have hl0 := vAB_loc m
      (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) G' hGG' c hc
    have hl2 := vAB_loc (m + 2)
      (fun c' => Q.resG k r (Fin.last r) ((P : Module.End ℂ (VS k r 0 D E)) v₀ : Mx k r → E) c' g₀) G' hGG' c hc
    rw [hl1.1, hl0.1, hl2.1]
    have hpG : pOp ⟨m + 1, by omega⟩ G' ∈ WSm r E := opL_mem ⟨m + 1, by omega⟩ 0 hG'
    rw [(vAB_lin y (m + 1) hpG hG' y).1, (vAB_comm y ⟨m + 1, by omega⟩ (m + 1) le_rfl hG').2.2.1]
    rw [(vAB_succ y (m + 1) (by omega) G').1, (vAB_succ y m (by omega) G').2]
    simp only [Pi.add_apply, Pi.smul_apply, cOp, ciOp, div_eq_mul_inv, mul_smul]
    abel

end claim2

end Formalism.FourierDecayAlt.P.PBN.MC
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProdOfFnMap
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ToStdAppendBlk
namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blk (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) * c)] := by
  intro h b
  induction h generalizing b with
  | nil => simp [D.toStd, D.ptSize]
  | cons blk rest ih =>
    obtain ⟨s', t⟩ := blk
    simp only [List.cons_append, D.toStd, ih (b + s'), D.ptSize, List.map_cons,
      List.sum_cons, add_assoc]

theorem slv_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) {P P' : C.LPt} (e : P = P') (hP : D.ptSize P = i) (hP' : D.ptSize P' = i) :
    KB.slv T F i hi w P hP = KB.slv T F i hi w P' hP' := by
  subst e; rfl

theorem psd_shift {Y : Finset C.LPt} {k : C.LPt → C.LPt → ℂ} (blk : ℕ × ℂ)
    (hk : TB.PSDOn (Y.image fun h => h ++ [blk]) k) : TB.PSDOn Y fun p q => k (p ++ [blk]) (q ++ [blk]) := by
  have hinj : Set.InjOn (fun h : C.LPt => h ++ [blk]) Y := fun x _ y _ hxy => List.append_cancel_right hxy
  rw [PBA.psd_iff_qf] at hk ⊢
  obtain ⟨hh, hq⟩ := hk
  refine ⟨fun x hx y hy => hh _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy), fun c => ?_⟩
  have e : PBA.qf Y (fun p q => k (p ++ [blk]) (q ++ [blk])) c =
      PBA.qf (Y.image fun h => h ++ [blk]) k (fun z => c z.dropLast) := by
    unfold PBA.qf
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp
  rw [e]; exact hq _

section lam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamB (S : C.HidaSetting E Wp Wq) (b s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1)

theorem stdS_blk (S : C.HidaSetting E Wp Wq) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ) :
    stdS S (H ++ [(s, t)]) = stdS S H ++ [(s, lamB S b s * t)] := by
  unfold stdS lamB
  rw [toStd_append_blk, hH, show 1 + (b - 1) = b by omega]

theorem norm_lamB (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) :
    ‖lamB S b s‖ = ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) := by
  unfold lamB
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact zpow_nonneg (by positivity) _

theorem lamB_ne (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) : lamB S b s ≠ 0 := by
  intro h
  have := norm_lamB S hg b s
  rw [h, norm_zero] at this
  exact (zpow_pos (by positivity : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi)) _).ne this

end lam

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_blk (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ)
    (hP : D.IsLocPt (H ++ [(s, t)]) j) :
    ∃ hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j,
      uB S p F v ε j hj w (H ++ [(s, t)]) = (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S H ++ [(s, lamB S b s * t)]) hX.2 := by
  have hgpos := g_pos_of_built hB
  have e := stdS_blk S b s hb H hH t
  have hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j := by
    rw [← e]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 j).2 hP
  refine ⟨hX, ?_⟩
  rw [uB_pos S p F v ε j hj w _ hP]
  congr 1
  exact slv_congr _ _ _ _ _ e _ _

theorem deg_uB_lift (hDL : KB.DegLift) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b) (a : List C.Letter) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (H H' : C.LPt) (hH : D.ptSize H = b - 1) (hH' : D.ptSize H' = b - 1) (t t' : ℂ) :
    ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) =
      ∑ n : Fin K → Fin (2 * (j - s) + s + 1), ((∏ c, F7.lagCo (grid c) (n c) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun c => grid c (n c))
          (uB S p F v ε j hj (KB.plusW (List.ofFn fun c => grid c (n c)) a) (H ++ [(s, t)]))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun c => grid c (n c)) a) (H' ++ [(s, t')])) := by
  by_cases hloc : D.IsLocPt (H ++ [(s, t)]) j ∧ D.IsLocPt (H' ++ [(s, t')]) j
  · obtain ⟨hP, hP'⟩ := hloc
    obtain ⟨hX, eX⟩ := uB_blk hB F v ε j hj a b s hb H hH t hP
    obtain ⟨hX', eX'⟩ := uB_blk hB F v ε j hj a b s hb H' hH' t' hP'
    have hdeg := hDL (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j s hj a (stdS S H) (stdS S H')
      (lamB S b s * t) (lamB S b s * t') hX hX' K grid (hF v ε hε) hinj
    rw [rr_eq_form (p v) (F v ε) j hj a _ _ hX hX'] at hdeg
    set Dh : ℂ := (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S (H' ++ [(s, t')])) / bS S (H' ++ [(s, t')]) : ℝ) : ℂ)) with hDh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a _ hX)
      (slv_nv (p v) (hF v ε hε) j hj a _ hX')
    rw [eX, eX', form_smul_l (p v) j hj a _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hs hs']
    have hL : ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (Dh * (conj Dh' * (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2)
          (KB.slv (p v).T (F v ε) j hj a _ hX'.2))) =
        Dh * conj Dh' * (((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
          (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2) (KB.slv (p v).T (F v ε) j hj a _ hX'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨hXp, eXp⟩ := uB_blk hB F v ε j hj (KB.plusW ys a) b s hb H hH t hP
    obtain ⟨hXm, eXm⟩ := uB_blk hB F v ε j hj (KB.minusW ys a) b s hb H' hH' t' hP'
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) _ hX)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) _ hX')
    rw [eXp, eXm, pj_smul (p v) j hj a ys _ _ _ _ hp hm]
    ring
  · have h0 : ∀ w : List C.Letter, uB S p F v ε j hj w (H ++ [(s, t)]) = 0 ∨
        uB S p F v ε j hj w (H' ++ [(s, t')]) = 0 := by
      intro w
      by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
      · exact Or.inr (uB_neg S p F v ε j hj w _ fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj w _ hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj a (H' ++ [(s, t')]))
    have lhs0 : (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) = 0 := by
      rcases h0 a with h0 | h0
      · rw [h0, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) (H' ++ [(s, t')]))
    by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) _ fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) _ hh, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section blockL

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

def uS (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) :
    Wd.Ix (Fin w.length) → B.Mat S.G.k (S.G.r - j) → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :=
  uY S p F v ε j hj w (Y.image fun h => h ++ [blk]) (h ++ [blk])

theorem uS_mem (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (Y : Finset C.LPt) (blk : ℕ × ℂ) (h : C.LPt) (hh : h ∈ Y) :
    uS S p F v ε j hj w Y blk h = uB S p F v ε j hj w (h ++ [blk]) :=
  uY_mem S p F v ε j hj w _ _ (Finset.mem_image_of_mem _ hh)

theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem prod_ofFn_map' {K : ℕ} (g0 : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn g0).map g).prod = ∏ c, g (g0 c) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

end blockL

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end
