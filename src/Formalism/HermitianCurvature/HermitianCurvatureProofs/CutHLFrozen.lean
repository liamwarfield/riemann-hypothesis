module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFrozen
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section comm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem comm_Tm (Eu : Fin n → Fin n → A) (hG : GlRel Eu) (p a b : Fin n) (ha : a ≠ p) (hb : b ≠ p) (v : ℂ) :
    Commute (Eu p p) (Tm Eu v a b) := by
  unfold Tm
  refine Commute.add_right ?_ ?_
  · split_ifs
    · exact (Algebra.commutes v (Eu p p)).symm
    · exact Commute.zero_right _
  · have h := hG p p a b
    rw [if_neg (Ne.symm ha), if_neg hb, sub_zero] at h
    exact sub_eq_zero.mp h

theorem comm_qminor (Eu : Fin n → Fin n → A) (hG : GlRel Eu) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (p : Fin n)
    (ha : ∀ i, a i ≠ p) (hb : ∀ i, b i ≠ p) : Commute (Eu p p) (qminor Eu a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ (fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact comm_Tm Eu hG p _ _ (ha _) (hb i) _

end comm

section aa

variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

theorem AAx_congr_rows (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi xi' : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (u : ℂ)
    (h : ∀ a : Fin r, a.val < m → xi a = xi' a) : C3.AAx k r Eu xi m hm u = C3.AAx k r Eu xi' m hm u := by
  unfold C3.AAx
  simp only [show ∀ a : Fin m, xi (Fin.castLE hm a) = xi' (Fin.castLE hm a) from fun a => h _ a.isLt]

theorem AAv_congr_rows (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y y' : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ)
    (h : ∀ a : Fin r, a.val < m → y a = y' a) : C3.AAv k r Eu y m hm ℓ = C3.AAv k r Eu y' m hm ℓ := by
  unfold C3.AAv
  simp only [show ∀ a : Fin m, y (Fin.castLE hm a) = y' (Fin.castLE hm a) from fun a => h _ a.isLt]

theorem comm_AAx (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel Eu)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j + 1 ≤ r) (u : ℂ)
    (h0 : ∀ a : Fin r, a.val < j → xi a (eI k r ⟨j, by omega⟩) = 0) :
    Commute (Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)) (C3.AAx k r Eu xi j (by omega) u) := by
  unfold C3.AAx
  refine Commute.sum_right _ _ _ (fun c _ => ?_)
  split_ifs with hc
  · by_cases hp : ∃ l, c l = eI k r ⟨j, by omega⟩
    · obtain ⟨l, hl⟩ := hp
      have hdet : (of fun (a l : Fin j) => xi (Fin.castLE (by omega) a) (c l)).det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero l
        intro a
        simp only [of_apply, hl]
        exact h0 _ a.isLt
      simp only [hdet, zero_smul]
      exact Commute.zero_right _
    · push_neg at hp
      refine Commute.smul_right ?_ _
      refine comm_qminor Eu hG _ _ u _ (fun i => ?_) hp
      have := i.isLt
      simp only [C3.xR, eI, ne_eq, Fin.ext_iff, Fin.coe_castLE]
      omega
  · exact Commute.zero_right _

theorem comm_AAv (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel Eu)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j + 1 ≤ r) (ℓ : ℂ)
    (h0 : ∀ a : Fin r, a.val < j → y a (esI k r ⟨j, by omega⟩) = 0) :
    Commute (Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)) (C3.AAv k r Eu y j (by omega) ℓ) := by
  unfold C3.AAv
  refine Commute.sum_right _ _ _ (fun c _ => ?_)
  split_ifs with hc
  · by_cases hp : ∃ l, c l = esI k r ⟨j, by omega⟩
    · obtain ⟨l, hl⟩ := hp
      have hdet : (of fun (a l : Fin j) => y (Fin.castLE (by omega) a) (c l)).det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero l
        intro a
        simp only [of_apply, hl]
        exact h0 _ a.isLt
      simp only [hdet, zero_smul]
      exact Commute.zero_right _
    · push_neg at hp
      refine Commute.smul_right ?_ _
      refine comm_qminor Eu hG _ _ _ _ hp (fun i => ?_)
      have := i.isLt
      simp only [C3.sR, esI, ne_eq, Fin.ext_iff, Fin.coe_castLE]
      omega
  · exact Commute.zero_right _

end aa

section what₂

variable {k r j : ℕ}

private theorem x0_esI_apply_eq_dite_Z {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (a : Fin r) (ha : a.val < j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r a) q = if h : q.val < j then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0 := by
  simp only [x0, Dx2.Split.castM_apply, U.mMap, U.blk3, reindex_apply, submatrix_apply]
  have he : (U.eB k (j + 1) (r - (j + 1))).symm (Fin.cast (by omega) (esI k r a)) =
      Sum.inr ⟨j - a.val, by omega⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [U.eB, esI, Fin.ext_iff]
    omega
  rw [he]
  rcases hq : (U.eB k (j + 1) (r - (j + 1))).symm (Fin.cast (by omega) q) with (l | l) | l
  all_goals rw [Equiv.symm_apply_eq] at hq
  all_goals have hv := congrArg Fin.val hq
  all_goals simp [U.eB] at hv
  · rw [fromBlocks_apply₂₁, fromCols_apply_inl, StandardCharacterExists.wMat_mul_apply]
    have hr : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = Fin.castAdd 1 ⟨a.val, ha⟩ := by
      ext
      simp
      omega
    rw [hr]
    simp only [zfull, U.blk2, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    by_cases hl : l.val < j
    · have hl' : l = Fin.castAdd 1 ⟨l.val, hl⟩ := by
        ext
        simp
      rw [hl', finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, dite_eq_left (by omega)]
      congr 1
      ext
      simp [hv]
    · have hl' : l = Fin.natAdd j 0 := by
        ext
        simp
        omega
      rw [hl', finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂, dite_eq_right (by omega)]
      rfl
  · rw [fromBlocks_apply₂₁, fromCols_apply_inr, dite_eq_right (by omega)]
    rfl
  · rw [fromBlocks_apply₂₂, dite_eq_right (by omega)]
    rfl

private theorem xi0_apply_eq_esI_apply {k r : ℕ} (g : B.Mat k r) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    PBG.xi0 g a p = g (esI k r a) p := by
  have hH : ∀ s, Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
    intro s
    have := a.isLt
    have := s.isLt
    simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
    have hd : 2 * r + k - (a : ℕ) + a = 2 * r + k := Nat.sub_add_cancel (by omega)
    generalize 2 * r + k - (a : ℕ) = d at *
    split_ifs <;> first | rfl | omega
  simp [PBG.xi0, herm, bvec, mulVec, dotProduct, Pi.single_apply, hH]

private theorem sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) (a : Fin r)
    (p : Fin (2 * r + k + 1)) :
    GBasic.sgn k r (GBasic.sig k r p) * PBG.y0 g a p = star (g (esI k r a) (GBasic.sig k r p)) := by
  have hs : GBasic.sig k r (GBasic.sig k r p) = p := by
    have := p.isLt
    ext
    simp only [GBasic.sig]
    split_ifs with h1 h2 h2 <;> simp only [Fin.val_mk] at * <;> omega
  have hn : GBasic.sgn k r (eI k r a) = 1 := by
    have := a.isLt
    rw [GBasic.sgn, if_neg]
    simp only [eI, Fin.val_mk]
    omega
  have he : GBasic.sig k r (eI k r a) = esI k r a := by
    have := a.isLt
    ext
    simp [GBasic.sig, eI, esI]
  have hu := B2x5.isUnit_det_GV hg
  have h1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc (gᴴ * Hpk k r), Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (GBasic.sig k r p)) (eI k r a)
  rw [C2x6.Hpk_mul_apply, C2x6.mul_Hpk_apply] at h2
  rw [hs, he, hn, mul_one, conjTranspose_apply] at h2
  have hy : PBG.y0 g a p = g⁻¹ p (eI k r a) := by
    simp [PBG.y0, bvec, mulVec, dotProduct, Pi.single_apply]
  rw [hy, h2]

theorem xi0_row_independent_of_tau (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin r) (ha : a.val < j) : PBG.xi0 (x0 k r j hj Z τ' γ) a = PBG.xi0 (x0 k r j hj Z τ γ) a := by
  funext p
  rw [xi0_apply_eq_esI_apply, xi0_apply_eq_esI_apply, x0_esI_apply_eq_dite_Z hj Z τ' γ a ha, x0_esI_apply_eq_dite_Z hj Z τ γ a ha]

theorem xi0_x0_eI_j_eq_zero (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin r) (ha : a.val < j) : PBG.xi0 (x0 k r j hj Z τ γ) a (eI k r ⟨j, by omega⟩) = 0 := by
  rw [xi0_apply_eq_esI_apply, x0_esI_apply_eq_dite_Z hj Z τ γ a ha, dite_eq_right]
  simp [eI]

theorem y0_row_independent_of_tau (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ τ' : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) (a : Fin r) (ha : a.val < j) :
    PBG.y0 (x0 k r j hj Z τ' γ) a = PBG.y0 (x0 k r j hj Z τ γ) a := by
  funext p
  have hs : GBasic.sgn k r (GBasic.sig k r p) ≠ 0 := by
    unfold GBasic.sgn
    split_ifs <;> norm_num
  apply mul_left_cancel₀ hs
  rw [sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ' hγ), sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ hγ),
    x0_esI_apply_eq_dite_Z hj Z τ' γ a ha, x0_esI_apply_eq_dite_Z hj Z τ γ a ha]

theorem y0_x0_esI_j_eq_zero_of_det_ne_zero (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) (a : Fin r) (ha : a.val < j) :
    PBG.y0 (x0 k r j hj Z τ γ) a (esI k r ⟨j, by omega⟩) = 0 := by
  have hs : GBasic.sgn k r (GBasic.sig k r (esI k r ⟨j, by omega⟩)) ≠ 0 := by
    unfold GBasic.sgn
    split_ifs <;> norm_num
  apply mul_left_cancel₀ hs
  rw [sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ hγ), x0_esI_apply_eq_dite_Z hj Z τ γ a ha, dite_eq_right, mul_zero, star_zero]
  have : j + 1 ≤ r := hj
  have hse : (GBasic.sig k r (esI k r ⟨j, by omega⟩)).val = j := by
    unfold GBasic.sig
    rw [if_pos (Or.inr (by simp only [esI]; omega))]
    simp only [esI]
    omega
  rw [hse]
  omega

end what₂

theorem frozen_X_identity : FrozenX := by
  intro A _ _ k r j hj Eu Z τ τ' u γ hG hZ hτ hτ' hγ
  exact ⟨AAx_congr_rows Eu _ _ j _ u (fun a ha => xi0_row_independent_of_tau hj Z τ τ' γ a ha),
    comm_AAx Eu hG _ j hj u (fun a ha => xi0_x0_eI_j_eq_zero hj Z τ γ a ha)⟩

theorem frozen_V_identity : FrozenV := by
  intro A _ _ k r j hj Eu Z τ τ' ℓ γ hG hZ hτ hτ' hγ
  exact ⟨AAv_congr_rows Eu _ _ j _ ℓ (fun a ha => y0_row_independent_of_tau hj hZ hτ hτ' hγ a ha),
    comm_AAv Eu hG _ j hj ℓ (fun a ha => y0_x0_esI_j_eq_zero_of_det_ne_zero hj hZ hτ hγ a ha)⟩

end Formalism.FourierDecayAlt.P.CutHL
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JslHsInnerSelfNorm
open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section JSL

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

private theorem opL_eq_zero_of_eventuallyEq_zero {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin m)
    (j : Fin 6) (f : (Fin m → ℂ) → E) (x : Fin m → ℂ) (h : f =ᶠ[𝓝 x] 0) : opL l j f x = 0 := by
  have h0 : f x = 0 := h.eq_of_nhds
  have hd : fderiv ℝ f x = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply (0 : E)
  fin_cases j
  · show pOp l f x = 0
    unfold pOp QuantumDeterminants.wirt
    rw [hd]
    simp
  · show cOp l f x = 0
    simp [cOp, h0]
  · show ciOp l f x = 0
    simp [ciOp, h0]
  · show pbOp l f x = 0
    unfold pbOp QuantumDeterminants.wirtBar
    rw [hd]
    simp
  · show cbOp l f x = 0
    simp [cbOp, h0]
  · show cbiOp l f x = 0
    simp [cbiOp, h0]

theorem jsl_wOp_lc (X : ActualOps k r z z' π π') (l : Fin r) (js : List (Fin 6)) :
    ∀ Φ ∈ lcSub k r z z' π π', wOp X l js Φ ∈ lcSub k r z z' π π' := by
  have hmem : ∀ Ψ : RadSp k r z z' π π', Ψ ∈ lcSub k r z z' π π' ↔ ∀ c ∈ OmX r, LCptAt Ψ c :=
    fun Ψ => Iff.rfl
  have hop : ∀ j, ∀ Ψ ∈ lcSub k r z z' π π', X.op l j Ψ ∈ lcSub k r z z' π π' := by
    intro j Ψ hΨ
    rw [hmem] at hΨ ⊢
    intro c hc
    obtain ⟨U', hU', hcU, K, hK, hKG, h0⟩ := hΨ c hc
    refine ⟨U', hU', hcU, K, hK, hKG, fun c' hc' g hg hgK => ?_⟩
    rw [X.op_apply]
    show opL l j (fun c'' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c'' g) c' = 0
    apply opL_eq_zero_of_eventuallyEq_zero
    filter_upwards [hU'.mem_nhds hc'] with c'' hc''
    exact h0 c'' hc'' g hg hgK
  induction js with
  | nil =>
    intro Φ hΦ
    simpa [wOp] using hΦ
  | cons j js ih =>
    intro Φ hΦ
    show X.op l j (wOp X l js Φ) ∈ lcSub k r z z' π π'
    exact hop j _ (ih Φ hΦ)

theorem jsl_hsInner_self_norm (C : Wq →L[ℂ] Wp) : ‖B.hsInner C C‖ = ‖B.hsVec C‖ ^ 2 := by
  rw [B.hsInner, inner_self_eq_norm_sq_to_K]
  simp [norm_pow]

theorem jsl_hs_comb_le {K : ℕ} (a : Fin K → ℂ) (A : Fin K → (Wq →L[ℂ] Wp)) :
    ‖B.hsInner (∑ i, a i • A i) (∑ i, a i • A i)‖ ≤ (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsInner (A i) (A i)‖ := by
  have hlin : B.hsVec (∑ i, a i • A i) = ∑ i, a i • B.hsVec (A i) := by
    change hsVecLin (∑ i, a i • A i) = ∑ i, a i • hsVecLin (A i)
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  rw [jsl_hsInner_self_norm, hlin]
  simp_rw [jsl_hsInner_self_norm]
  calc ‖∑ i, a i • B.hsVec (A i)‖ ^ 2 ≤ (∑ i, ‖a i • B.hsVec (A i)‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
    _ ≤ (K : ℝ) * ∑ i, ‖a i • B.hsVec (A i)‖ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i • B.hsVec (A i)‖)
    _ = (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsVec (A i)‖ ^ 2 := by
        simp [norm_smul, mul_pow]

theorem jsl_pairAt_comb_le (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {K : ℕ}
    (a : Fin K → ℂ) (u : RadSp k r z z' π π') (v : Fin K → RadSp k r z z' π π')
    (hv : ∀ i, v i ∈ lcSub k r z z' π π') (x : Fin r → ℂ)
    (hx : ∀ g, (u : Fn k r (Wq →L[ℂ] Wp)) x g = ∑ i, a i • (v i : Fn k r (Wq →L[ℂ] Wp)) x g) :
    ‖pairAt μ u u x‖ ≤ (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖pairAt μ (v i) (v i) x‖ := by
  have hint : ∀ i, Integrable (fun g : Mt k r => ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
      ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖) μ := fun i => (int_lc μ hμ (hv i) (hv i) x).norm
  rw [norm_pairAt_selfI]
  simp only [norm_pairAt_selfI]
  calc ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
        ((u : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖ ∂μ
      ≤ ∫ g : Mt k r, (K : ℝ) * ∑ i, ‖a i‖ ^ 2 * ‖B.hsInner ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))
        ((v i : Fn k r (Wq →L[ℂ] Wp)) x (Matrix.of g))‖ ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((integrable_finsetSum _ fun i _ => (hint i).const_mul _).const_mul _) (ae_of_all _ fun g => ?_)
        dsimp only
        rw [hx]; exact jsl_hs_comb_le _ _
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => (hint i).const_mul _]
        simp only [integral_const_mul]

private theorem integral_norm_ofReal_eq_norm_integral_of_nonneg {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) : ∫ a, ‖((f a : ℝ) : ℂ)‖ ∂ν = ‖∫ a, ((f a : ℝ) : ℂ) ∂ν‖ := by
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (hf _)]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hf)]

theorem jsl_int_norm_self (μ : Measure (Mt k r)) (i : Fin (r + 1)) (v : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ∫ c' : Cf r i, ‖wtI i c' * pairAt μ v v (glue i c c')‖ =
      ‖∫ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c')‖ := by
  have key : ∀ c' : Cf r i, wtI i c' * pairAt μ v v (glue i c c') =
      (((∏ l, ‖c' l‖ ^ (-2 : ℤ)) *
        ∫ g : Mt k r, ‖B.hsVec ((v : Fn k r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro c'
    have hh : ∀ A : Wq →L[ℂ] Wp, B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := fun A => by
      rw [B.hsInner, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [wtI, pairAt]
    simp_rw [hh]
    rw [integral_complex_ofReal, Complex.ofReal_mul]
  simp_rw [key]
  apply integral_norm_ofReal_eq_norm_integral_of_nonneg
  intro c'
  apply mul_nonneg
  · exact Finset.prod_nonneg fun l _ => by positivity
  · exact integral_nonneg fun g => by positivity

theorem jsl_glue_self (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  unfold glue
  rw [dite_eq_right (by simp [Fin.val_succ])]
  simp

end JSL

theorem jSL2Loc_of : JSWordNF → JSRadLoc → SpectralL2Locality := by
  intro hNF hRad Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ js t0 ht0
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have : SFinite μ := sfinite_of_isHaarOn _ μ hμ
  obtain ⟨hΨlc, s, ε, G, hε, hN, hG, hΨv⟩ := hΨ

  let Wv : Module.End ℂ (RadSp P.k P.r z z' π π') :=
    P5.mulOp (fun x => fsv s (x.1 l)) (P5.contDiff_fsv_coord l s) (fun _ _ _ _ _ _ => rfl)
  have hW : multiplicationOperator Wv (fun c _ => fsv s (c l)) := P5.mulOp_isMulOp _ _ _
  let Wn : Module.End ℂ (RadSp P.k P.r z z' π π') :=
    P5.mulOp (fun x => fsv (-s) (x.1 l)) (P5.contDiff_fsv_coord l (-s)) (fun _ _ _ _ _ _ => rfl)
  have hWn : multiplicationOperator Wn (fun c _ => fsv (-s) (c l)) := P5.mulOp_isMulOp _ _ _
  have hΦlc : Wn Ψ ∈ lcSub P.k P.r z z' π π' := mul_lc hWn Ψ hΨlc
  have hΦv : ∀ y ∈ DomR P.k P.r z z', ((Wn Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG P.k P.r (Fin.last P.r) (B.JF D G) y.1 y.2 := by
    intro y hy
    rw [hWn Ψ y.1 y.2, hΨv y hy, smul_smul, fsv_neg_mul_fsv, one_smul]
  have hΨeq : Wv (Wn Ψ) = Ψ := by
    apply Subtype.ext
    funext c' g
    show ((Wv (Wn Ψ) : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c' g
    rw [hW (Wn Ψ) c' g, hWn Ψ c' g, smul_smul, fsv_mul_fsv_neg, one_smul]

  obtain ⟨K, m, ab, hm, hab, hE⟩ := hNF P.k P.r z z' Wp Wq π π' X l s Wv hW js
  have hR : ∀ i, ∃ ε' : ℝ, 0 < ε' ∧ ∃ M : ℝ, ∀ t ∈ Metric.ball t0 ε',
      LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧
        ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M := fun i =>
    hRad Wp Wq P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl ε hε G hN hG (Wn Ψ) hΦlc hΦv c hc (ab i)
      (hab i) t0 ht0
  choose ε' hε' M hM using hR
  have hac : ∀ i, ContinuousAt (fun t => m i t * fsv s t) t0 := fun i =>
    ((hm i).continuousAt (isOpen_compl_singleton.mem_nhds ht0)).mul
      (P5.contDiff_fsv s).continuous.continuousAt
  have hev : ∀ᶠ t in 𝓝 t0, ∀ i, (LevelSquareIntegrable μ l.succ (wOp X l (ab i) (Wn Ψ)) (Function.update c l t) ∧
      ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ ≤ M i) ∧
      ‖m i t * fsv s t‖ ≤ ‖m i t0 * fsv s t0‖ + 1 := by
    rw [Filter.eventually_all]
    intro i
    refine (Filter.eventually_of_mem (Metric.ball_mem_nhds t0 (hε' i)) fun t ht => hM i t ht).and ?_
    exact ((hac i).norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun t ht => ht.le
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨δ, hδ, (K : ℝ) * ∑ i, (‖m i t0 * fsv s t0‖ + 1) ^ 2 * M i, fun t ht => ?_⟩
  have hP := hδP t ht
  have hvlc : ∀ i, wOp X l (ab i) (Wn Ψ) ∈ lcSub P.k P.r z z' π π' := fun i => jsl_wOp_lc X l (ab i) _ hΦlc

  have hx : ∀ (c' : Cf P.r l.succ) (g : Mx P.k P.r),
      (wOp X l js Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g =
        ∑ i, (m i t * fsv s t) •
          (wOp X l (ab i) (Wn Ψ) : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g := by
    intro c' g
    by_cases hxo : glue l.succ (Function.update c l t) c' ∈ OmX P.r
    · have e := hE (Wn Ψ) _ hxo g
      rw [hΨeq, jsl_glue_self] at e
      exact e
    · have h0 : ∀ w : RadSp P.k P.r z z' π π',
          (w : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue l.succ (Function.update c l t) c') g = 0 :=
        fun w => radSp_zero_off w (x := (glue l.succ (Function.update c l t) c', g)) (fun h => hxo h.1)
      rw [h0]
      simp only [h0, smul_zero, Finset.sum_const_zero]
  have hpt : ∀ c' : Cf P.r l.succ,
      ‖wtI l.succ c' * pairAt μ (wOp X l js Ψ) (wOp X l js Ψ) (glue l.succ (Function.update c l t) c')‖ ≤
        (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ))
          (wOp X l (ab i) (Wn Ψ)) (glue l.succ (Function.update c l t) c')‖ := by
    intro c'
    have := jsl_pairAt_comb_le μ hμ (fun i => m i t * fsv s t) (wOp X l js Ψ) (fun i => wOp X l (ab i) (Wn Ψ))
      hvlc _ (hx c')
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left this (norm_nonneg _)).trans (le_of_eq ?_)
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [norm_mul]
    ring
  have hb : Integrable (fun c' : Cf P.r l.succ => (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 *
      ‖wtI l.succ c' * pairAt μ (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ))
        (glue l.succ (Function.update c l t) c')‖) :=
    (integrable_finsetSum _ fun i _ => ((hP i).1.1.norm.const_mul _)).const_mul _
  refine ⟨?_, ?_⟩
  · unfold LevelSquareIntegrable
    exact hb.mono' ((wtI_measurable l.succ).aestronglyMeasurable.mul
      (pairAt_measI μ l.succ _ _ _).aestronglyMeasurable) (ae_of_all _ hpt)
  · have hfs : ‖fs μ l (wOp X l js Ψ) (wOp X l js Ψ) c t‖ ≤
        (K : ℝ) * ∑ i, ‖m i t * fsv s t‖ ^ 2 * ‖fs μ l (wOp X l (ab i) (Wn Ψ)) (wOp X l (ab i) (Wn Ψ)) c t‖ := by
      unfold fs
      refine (norm_integral_le_integral_norm _).trans ?_
      refine (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hb (ae_of_all _ hpt)).trans
        (le_of_eq ?_)
      rw [integral_const_mul, integral_finsetSum _ fun i _ => (hP i).1.1.norm.const_mul _]
      simp only [integral_const_mul, jsl_int_norm_self]
    refine hfs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hP i).2 2) (hP i).1.2 (norm_nonneg _) (by positivity)

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbEquiv2
open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbEquiv

section clm

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

theorem integral_clm_leftInv (L M : E →L[ℂ] E) (hML : ∀ v, M (L v) = v) (f : α → E) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) := by
  by_cases hf : Integrable f μ
  · exact L.integral_comp_comm hf
  · have hLf : ¬ Integrable (fun x => L (f x)) μ := by
      intro h
      apply hf
      have := M.integrable_comp h
      simpa [hML] using this
    rw [integral_undef hf, integral_undef hLf, map_zero]

end clm

section ops

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def post (A : Wp →L[ℂ] Wp) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wp Wp A

def pre (B' : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B'

theorem post_apply (A : Wp →L[ℂ] Wp) (f : Wq →L[ℂ] Wp) : post A f = A.comp f := rfl

theorem pre_apply (B' : Wq →L[ℂ] Wq) (f : Wq →L[ℂ] Wp) : pre B' f = f.comp B' := rfl

end ops

section homeo

variable {k r : ℕ}

def conjHomeo (a : B.Mat k r) (ha : IsUnit a.det) : Mt k r ≃ₜ Mt k r where
  toFun x := a * Matrix.of x * a⁻¹
  invFun x := a⁻¹ * Matrix.of x * a
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * a⁻¹) * a = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha,
      Matrix.one_mul]; rfl
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * a) * a⁻¹ = x
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha,
      Matrix.one_mul]; rfl
  continuous_toFun := by
    show Continuous fun x : Mt k r => a * Matrix.of x * a⁻¹
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const
  continuous_invFun := by
    show Continuous fun x : Mt k r => a⁻¹ * Matrix.of x * a
    exact (Continuous.matrix_mul continuous_const continuous_id).matrix_mul continuous_const

end homeo

section kr

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem unit_of_uw {z : Fin (2 * r + k + 1) → ℂ} {w : B.Mat k r} (hw : w ∈ UWset k r z) : IsUnit w.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hw.1

theorem kr_right_uw (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x w : B.Mat k r)
    (hw : w ∈ UWset k r Bs.z') : PBG.Kr Bs F (x * w) = (PBG.Kr Bs F x).comp (Bs.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k r Bs.z' := LieBracketMultiplication.uw_inv hw
  have := PBG.sigmaFinite_of_haar Bs.haarN
  have := PBG.sigmaFinite_of_haar Bs.haarW'
  set e1 := (PBG.lmulHomeo w hU).toMeasurableEquiv
  set e2 := (conjHomeo w hU).toMeasurableEquiv
  set Φ : Mt k r × Mt k r ≃ᵐ Mt k r × Mt k r := MeasurableEquiv.prodCongr e1 e2
  have hmp1 : MeasurePreserving e1 Bs.μW' Bs.μW' := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM w := by funext x; rfl
    rw [ee]; exact Bs.haarW'.left w hw
  have hmp2 : MeasurePreserving e2 Bs.μN Bs.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM w := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r Bs.z' Bs.μN Bs.z'_mem Bs.T'_pos Bs.haarN w hw
  have hmp : MeasurePreserving Φ (Bs.μW'.prod Bs.μN) (Bs.μW'.prod Bs.μN) := hmp1.prod hmp2
  set f : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  set g : Mt k r × Mt k r → (Wq →L[ℂ] Wp) := fun p => star (psi k r Bs.z' cStd (Matrix.of p.2)) •
      (F (x * w * Matrix.of p.2 * Matrix.of p.1)).comp (Bs.π' (Matrix.of p.1)⁻¹)
  have hK1 : PBG.Kr Bs F x = ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) := (hmp.integral_comp' f).symm
  have hae : ∀ᵐ p ∂(Bs.μW'.prod Bs.μN), (Matrix.of p.1 : B.Mat k r) ∈ UWset k r Bs.z' :=
    Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae Bs.haarW')
  have hK2 : ∫ p, f (Φ p) ∂(Bs.μW'.prod Bs.μN) = ∫ p, pre (Bs.π' w⁻¹) (g p) ∂(Bs.μW'.prod Bs.μN) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    have hpsi : psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹) = psi k r Bs.z' cStd (Matrix.of p.2) := by
      have := Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bs.z' cStd w⁻¹ hwi (Matrix.of p.2)
      rwa [Matrix.nonsing_inv_nonsing_inv _ hU] at this
    have hmat : x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1) = x * w * Matrix.of p.2 * Matrix.of p.1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc w⁻¹ w, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]
    have hpi : Bs.π' (w * Matrix.of p.1)⁻¹ = (Bs.π' (Matrix.of p.1)⁻¹).comp (Bs.π' w⁻¹) := by
      rw [Matrix.mul_inv_rev]
      exact Bs.π'_rep.2 _ (LieBracketMultiplication.uw_inv hp) _ hwi
    show star (psi k r Bs.z' cStd (w * Matrix.of p.2 * w⁻¹)) •
        (F (x * (w * Matrix.of p.2 * w⁻¹) * (w * Matrix.of p.1))).comp (Bs.π' (w * Matrix.of p.1)⁻¹) = _
    rw [hpsi, hmat, hpi, pre_apply, ContinuousLinearMap.smul_comp]
    rfl
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (Bs.π' w) (pre (Bs.π' w⁻¹) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw,
      Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
    rfl
  have hK3 : PBG.Kr Bs F x = (PBG.Kr Bs F (x * w)).comp (Bs.π' w⁻¹) := by
    rw [hK1, hK2, integral_clm_leftInv _ _ hML]
    rfl
  rw [hK3, ContinuousLinearMap.comp_assoc, ← Bs.π'_rep.2 _ hwi _ hw, Matrix.nonsing_inv_mul _ hU, Bs.π'_rep.1]
  rfl

end kr

section pb

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [CompleteSpace Wp]

theorem pbF_right_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (g w : B.Mat k n) (hw : w ∈ UWset k n B0.z') :
    PBQ.pbF Bj B0 e H (g * w) = (PBQ.pbF Bj B0 e H g).comp (B0.π' w) := by
  have hU := unit_of_uw hw
  have hwi : w⁻¹ ∈ UWset k n B0.z' := LieBracketMultiplication.uw_inv hw
  have hML : ∀ v : Wq →L[ℂ] Wp, pre (B0.π' w⁻¹) (pre (B0.π' w) v) = v := by
    intro v
    rw [pre_apply, pre_apply, ContinuousLinearMap.comp_assoc, ← B0.π'_rep.2 _ hw _ hwi,
      Matrix.mul_nonsing_inv _ hU, B0.π'_rep.1]
    rfl
  unfold PBQ.pbF
  rw [← pre_apply, ← integral_clm_leftInv _ _ hML]
  congr 1
  funext x
  unfold PBQ.pbI
  rw [← Matrix.mul_assoc, kr_right_uw B0 H _ w hw, pre_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_assoc]

theorem pbF_left_uw (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n)
    (H : B.Mat k n → (Wq →L[ℂ] Wp)) (h : B.Mat k ρ) (hh : h ∈ UWset k ρ Bj.z) (g : B.Mat k n) :
    PBQ.pbF Bj B0 e H (D.castM e (U.embG k p ρ h) * g) = (Bj.π h).comp (PBQ.pbF Bj B0 e H g) := by
  have hU := unit_of_uw hh
  have hi : h⁻¹ ∈ UWset k ρ Bj.z := LieBracketMultiplication.uw_inv hh
  have hiU := unit_of_uw hi
  have := PBG.sigmaFinite_of_haar Bj.haarN
  have := PBG.sigmaFinite_of_haar Bj.haarW
  haveI : SigmaFinite (U.muRC k p ρ) := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ
  set e1 := (PBG.lmulHomeo h⁻¹ hiU).toMeasurableEquiv
  set e2 := (conjHomeo h⁻¹ hiU).toMeasurableEquiv
  set Φ : PBQ.XP k p ρ ≃ᵐ PBQ.XP k p ρ := MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr e1 e2)
    (MeasurableEquiv.refl _)
  have hmp1 : MeasurePreserving e1 Bj.μW Bj.μW := by
    refine ⟨e1.measurable, ?_⟩
    have ee : ⇑e1 = lmulM h⁻¹ := by funext x; rfl
    rw [ee]; exact Bj.haarW.left h⁻¹ hi
  have hmp2 : MeasurePreserving e2 Bj.μN Bj.μN := by
    refine ⟨e2.measurable, ?_⟩
    have ee : ⇑e2 = conjM h⁻¹ := by funext x; rfl
    rw [ee]; exact Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k ρ Bj.z Bj.μN Bj.z_mem Bj.T_pos Bj.haarN h⁻¹ hi
  have hmp : MeasurePreserving Φ (PBQ.muXP (p := p) Bj) (PBQ.muXP (p := p) Bj) :=
    (hmp1.prod hmp2).prod (MeasurePreserving.id _)
  have hML : ∀ v : Wq →L[ℂ] Wp, post (Bj.π h⁻¹) (post (Bj.π h) v) = v := by
    intro v
    rw [post_apply, post_apply, ← ContinuousLinearMap.comp_assoc, ← Bj.π_rep.2 _ hi _ hh,
      Matrix.nonsing_inv_mul _ hU, Bj.π_rep.1]
    rfl
  have hF : PBQ.pbF Bj B0 e H g = ∫ x, PBQ.pbI Bj B0 e H g (Φ x) ∂(PBQ.muXP Bj) :=
    (hmp.integral_comp' (PBQ.pbI Bj B0 e H g)).symm
  rw [hF, ← post_apply, ← integral_clm_leftInv _ _ hML]
  unfold PBQ.pbF
  refine integral_congr_ae ?_
  filter_upwards [PBQ.ae_goodP Bj] with x hx
  have hx1 : (Matrix.of x.1.1 : B.Mat k ρ) ∈ UWset k ρ Bj.z := hx.1
  have hx2 : (Matrix.of x.1.2 : B.Mat k ρ) ∈ Nset k ρ := hx.2
  have hΦ : PBQ.GoodP Bj (Φ x) :=
    ⟨LieBracketMultiplication.uw_mul hi hx1, (Formalism.QuantumDeterminants.uWNormal k ρ Bj.z Bj.z_mem h⁻¹ hi _ hx2).1⟩
  have hsP : D.castM e (PBQ.sP Bj x) * (D.castM e (U.embG k p ρ h) * g) = D.castM e (PBQ.sP Bj (Φ x)) * g := by
    rw [← Matrix.mul_assoc, ← PBQ.castM_mul]
    congr 2
    unfold PBQ.sP
    rw [if_pos hx, if_pos hΦ]
    show U.Rn k p ρ (-x.2) * U.embG k p ρ ((Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹) * U.embG k p ρ h =
      U.Rn k p ρ (-x.2) * U.embG k p ρ ((h⁻¹ * Matrix.of x.1.1)⁻¹ * (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹)⁻¹)
    rw [Matrix.mul_assoc, ← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul]
    congr 2
    rw [Matrix.nonsing_inv_nonsing_inv h hU]
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv h hU, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have hcP : PBQ.cP Bj (Φ x) = PBQ.cP Bj x := by
    unfold PBQ.cP
    show psi k ρ Bj.z cStd (h⁻¹ * Matrix.of x.1.2 * h⁻¹⁻¹) * _ = _
    rw [Matrix.nonsing_inv_nonsing_inv h hU, Formalism.FourierDecayAlt.P.PBM.psi_conj_UW Bj.z cStd h hh]
    rfl
  have hπ : Bj.π (Matrix.of x.1.1) = (Bj.π h).comp (Bj.π (h⁻¹ * Matrix.of x.1.1)) := by
    rw [← Bj.π_rep.2 _ hh _ (LieBracketMultiplication.uw_mul hi hx1), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  unfold PBQ.pbI
  rw [hsP, ← hcP, hπ, post_apply, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_assoc]
  rfl

end pb

end Formalism.FourierDecayAlt.P.CutEXPbEquiv

namespace Formalism.FourierDecayAlt.P

open CutEXPbEquiv

theorem pullback_equivalence : CutEX.PbEquiv := by
  intro Wp Wq _ _ _ _ _ _ P p G _ Z _ μ _ h hh h' hh'
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hw : D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h') ∈
      UWset P.k P.r p.T.base.z' := by
    have h1 := Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW (k := P.k) P.r (P.r - P.r) _ h' hh'
    rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG] at h1
    have h2 := Formalism.FourierDecayAlt.P.Dx2.Tower.castM_UW (by omega : P.r + (P.r - P.r) = P.r) _ _ h1
    rw [p.T.z'_lev P.r le_rfl] at h2
    exact h2
  have hpi : p.T.base.π' (D.castM (by omega : P.r + (P.r - P.r) = P.r) (U.embG P.k P.r (P.r - P.r) h')) =
      (p.T.bs P.r).π' h' := by
    rw [p.T.π'_lev P.r le_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
    rfl
  unfold CutEX.pbTop PBQ.pbT CutEX.xT
  rw [LeftFubiniLemmas.embedding_map_embedded_group, PBQ.castM_mul, PBQ.castM_mul, pbF_right_uw _ _ _ _ _ _ hw, pbF_left_uw _ _ _ _ _ hh, hpi,
    ContinuousLinearMap.comp_assoc]

end Formalism.FourierDecayAlt.P
end
end
