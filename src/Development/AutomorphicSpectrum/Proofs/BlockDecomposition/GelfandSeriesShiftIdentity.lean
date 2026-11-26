module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultisetEq
open Finset Matrix

noncomputable section

namespace GlobalTheory.Dec.GelfSepProof


open PowerSeries Matrix in
theorem _root_.GlobalTheory.Dec.GelfSepProof.gen {n : ℕ} (l : Fin n → ℂ) :
    ((1 : PowerSeries ℂ) -
        PowerSeries.X * PowerSeries.mk fun (k : ℕ) ↦ ∑ a : Fin n, ∑ b : Fin n, (_root_.Formalism.REAL.Amat l ^ k) a b) *
      ∏ a : Fin n, ((1 : PowerSeries ℂ) - (PowerSeries.C : ℂ → PowerSeries ℂ) (l a) * PowerSeries.X) =
    ∏ a : Fin n,
      ((1 : PowerSeries ℂ) -
        ((PowerSeries.C : ℂ → PowerSeries ℂ) (l a) + (1 : PowerSeries ℂ)) * PowerSeries.X) := by
  have hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0 := by
    intro a b
    unfold _root_.Formalism.REAL.Amat
    rfl
  set A := _root_.Formalism.REAL.Amat l with hAdef
  let Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := A.map (PowerSeries.C : ℂ → PowerSeries ℂ)
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b
  have hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    ext a b k
    rcases k with _ | k
    · simp [B, Matrix.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul,
          map_sum]
        split_ifs <;> simp
  let c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := replicateCol (Fin 1) 1
  let R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ) := replicateRow (Fin 1) 1
  let J : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of fun _ _ => 1
  let U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := -((X : PowerSeries ℂ) • (B * c))
  have hcR : c * R = J := by
    ext a b
    simp [c, R, J, Matrix.mul_apply]
  have hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) =
      1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J := by
    have hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c) := by
      show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _
      rw [Matrix.mul_neg, Matrix.mul_smul, hBc]
    rw [mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]
    abel
  have hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X) := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, hA, mul_comm]
    · intro a b hab
      have hba : b < a := hab
      simp [Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']
  have hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det =
      ∏ a : Fin n, (1 - (C (l a) + 1) * X) := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, J, hA]
      ring
    · intro a b hab
      have hab' : a < b := hab
      simp [Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]
  have hdet3 : (1 + U * R).det =
      1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b := by
    rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]
    simp only [← Finset.mul_sum]
    congr 1
    ext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp [PowerSeries.coeff_mk, map_sum]
  rw [← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]



end GlobalTheory.Dec.GelfSepProof

namespace GlobalTheory.Dec

end GlobalTheory.Dec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentity
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem gser_mul_prod : ∀ (n : ℕ) (c : Fin n → ℂ),
    (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) =
      ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  intro n c
  have h := GlobalTheory.Dec.GelfSepProof.gen (fun a => c a + ((n : ℂ) - 1) / 2)
  have e : gser c = PowerSeries.mk (fun k => ∑ a, ∑ b,
      (Formalism.REAL.Amat (fun a => c a + ((n : ℂ) - 1) / 2) ^ k) a b) := rfl
  rw [e]
  simpa only [map_add (f := _), map_one] using h

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentityStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_series_shift_identity : ∀ (n : ℕ) (c : Fin n → ℂ), (1 - PowerSeries.X * gser c) * ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2) * PowerSeries.X) = ∏ a, (1 - PowerSeries.C (c a + ((n : ℂ) - 1) / 2 + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod | exact GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod | (intros; apply GlobalTheory.CompanionTheory.WaveMult.gser_mul_prod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommute
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SmCalc

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {u : ℝ → E → W} {O : Set E}

theorem hasFDerivAt_unc (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((hu.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
    (by simp)).hasFDerivAt

theorem hasDerivAt_line (s : ℝ) (y : E) :
    HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem deriv_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    deriv (fun r => u r y) s = fderiv ℝ (Function.uncurry u) (s, y) ((1 : ℝ), (0 : E)) := by
  have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s
    (hasFDerivAt_unc hO hu s hy) (hasDerivAt_line s y)
  exact h2.deriv

theorem fderiv_slice_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O)
    (v : E) : fderiv ℝ (u s) y v = fderiv ℝ (Function.uncurry u) (s, y) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right s y
  have h2 := HasFDerivAt.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) y
    (hasFDerivAt_unc hO hu s hy) h1
  have h3 : HasFDerivAt (u s) ((fderiv ℝ (Function.uncurry u) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y := h2
  simp [h3.fderiv]

theorem fd_smooth (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ O) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)

theorem smooth_deriv (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => deriv (fun r => u r y) s) (Set.univ ×ˢ O) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((1 : ℝ), (0 : E))) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply contDiffOn_const
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact deriv_eq hO hu s hy

theorem smooth_field (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => fderiv ℝ (u s) y (V y)) (Set.univ ×ˢ O) := by
  have h0 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), V p.2)) :=
    contDiff_const.prodMk (hV.comp contDiff_snd)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((0 : ℝ), V p.2)) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply h0.contDiffOn
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact fderiv_slice_eq hO hu s hy _

theorem smooth_slice (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) :
    ContDiffOn ℝ ∞ (u s) O := by
  have h1 : ContDiff ℝ ∞ (fun z : E => (s, z)) := contDiff_const.prodMk contDiff_id
  exact ContDiffOn.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) hu
    h1.contDiffOn (fun z hz => ⟨Set.mem_univ _, hz⟩)

theorem smooth_line (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {y : E} (hy : y ∈ O) : ContDiff ℝ ∞ fun s => u s y := by
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => (r, y)) := contDiff_id.prodMk contDiff_const
  have h2 := ContDiffOn.comp (s := Set.univ) (g := Function.uncurry u)
    (f := fun r : ℝ => (r, y)) hu h1.contDiffOn (fun _ _ => ⟨Set.mem_univ _, hy⟩)
  exact contDiffOn_univ.1 h2

theorem deriv_fderiv_comm (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (v : E) (s : ℝ) {y : E}
    (hy : y ∈ O) :
    deriv (fun r => fderiv ℝ (u r) y v) s =
      fderiv ℝ (fun z => deriv (fun r => u r z) s) y v := by
  have hm : (s, y) ∈ (Set.univ : Set ℝ) ×ˢ O := ⟨Set.mem_univ _, hy⟩
  have hn := (isOpen_univ.prod hO).mem_nhds hm
  have hF : ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) := hu.contDiffAt hn
  have hG : HasFDerivAt (fderiv ℝ (Function.uncurry u))
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)) (s, y) :=
    (((fd_smooth hO hu).contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ (Function.uncurry u) (s, y) :=
    hF.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hL : HasDerivAt (fun r => fderiv ℝ (u r) y v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), v)) s := by
    have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s hG (hasDerivAt_line s y)
    have h3 := ((ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)).hasFDerivAt).comp_hasDerivAt s h2
    have he : (fun r => fderiv ℝ (u r) y v) = (⇑(ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)) ∘
        (fderiv ℝ (Function.uncurry u)) ∘ fun r : ℝ => (r, y)) := by
      funext r
      simpa using fderiv_slice_eq hO hu r hy v
    rw [he]
    simpa using h3
  have hR : HasFDerivAt (fun z => deriv (fun r => u r z) s)
      ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        ((fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ E))) y := by
    have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      hasFDerivAt_prodMk_right s y
    have h2 := HasFDerivAt.comp (f := fun z : E => (s, z)) y hG h1
    have h3 := ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt).comp y h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz
    simpa using deriv_eq hO hu s hz
  rw [hL.deriv, hR.fderiv]
  simpa using hsym.eq ((1 : ℝ), (0 : E)) ((0 : ℝ), v)

end Generic

theorem contDiff_mulRight {n : ℕ} (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff

end SmCalc

theorem sm_calculus : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧
      (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧
      ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y :=
  fun _ hu => ⟨SmCalc.smooth_deriv isOpen_GLs hu,
    fun X => SmCalc.smooth_field isOpen_GLs hu (SmCalc.contDiff_mulRight X),
    SmCalc.smooth_slice hu, fun _ hy => SmCalc.smooth_line hu hy,
    fun _ s _ hy => SmCalc.deriv_fderiv_comm isOpen_GLs hu _ s hy⟩

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTimeRightDerivativesCommuteStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_time_right_derivatives_commute : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧ (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧ ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_calculus | exact GlobalTheory.CompanionTheory.WaveSpd.sm_calculus | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_calculus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWords
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWords
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobGL.Expand

variable {n : ℕ}

def co (q : Idx n) (M : Mat n) : ℝ := if q.1 then (M q.2.1 q.2.2).re else (M q.2.1 q.2.2).im

theorem sum_single_ite (a b : Fin n) (g : Fin n → Fin n → ℂ) :
    ∑ x, ∑ i, (if x = a ∧ i = b then g x i else 0) = g a b := by
  rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp),
    Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem sum_co_smul (M : Mat n) : ∑ q : Idx n, co q M • bs q = M := by
  ext a b
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, co, bs, Matrix.sum_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.single_apply, if_true, Bool.false_eq_true, if_false, smul_ite,
    smul_zero]
  rw [sum_single_ite a b (fun x i => (M x i).re • (1 : ℂ)),
    sum_single_ite a b (fun x i => (M x i).im • Complex.I)]
  simp [Complex.ext_iff]

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y i j) :=
  contDiff_apply_apply ℝ i j

theorem contDiff_det (F : Mat n → Mat n) (h : ∀ i j, ContDiff ℝ ∞ (fun y => F y i j)) :
    ContDiff ℝ ∞ (fun y => (F y).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem contDiff_adjugate (i k : Fin n) : ContDiff ℝ ∞ (fun y : Mat n => y.adjugate i k) := by
  simp only [Matrix.adjugate_apply]
  refine contDiff_det (fun y => y.updateRow k (Pi.single i 1)) fun a b => ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne.preimage (contDiff_det (n := n) id contDiff_entry).continuous

theorem contDiffOn_inv_entry (i k : Fin n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹ i k) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun y : Mat n => (y.det)⁻¹ * y.adjugate i k) (GLs n) :=
    ((contDiff_det (n := n) id contDiff_entry).contDiffOn.inv fun y hy => hy).mul
      (contDiff_adjugate i k).contDiffOn
  refine h.congr fun y _ => ?_
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]

theorem co_smooth (p q : Idx n) :
    ContDiffOn ℝ ∞ (fun y : Mat n => co q (y⁻¹ * bs p)) (GLs n) := by
  have he : ∀ a b, ContDiffOn ℝ ∞ (fun y : Mat n => (y⁻¹ * bs p) a b) (GLs n) := by
    intro a b
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun k _ => (contDiffOn_inv_entry a k).mul contDiffOn_const
  rcases q with ⟨_ | _, a, b⟩
  · simpa [co, Function.comp_def] using Complex.imCLM.contDiff.comp_contDiffOn (he a b)
  · simpa [co, Function.comp_def] using Complex.reCLM.contDiff.comp_contDiffOn (he a b)

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) := by
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (contDiff_entry a k).mul contDiff_const

theorem Rw_smooth {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact (ih.fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply
      (contDiff_mul_right (bs p)).contDiffOn

theorem fderiv_mul_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    (y M : Mat n) : fderiv ℝ H y (y * M) = ∑ q, co q M • Rd (bs q) H y := by
  conv_lhs => rw [← sum_co_smul M]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mul_smul, map_smul]
  rfl

theorem fderiv_expand {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Mat n → V)
    {y : Mat n} (hy : y ∈ GLs n) (X : Mat n) :
    fderiv ℝ H y X = ∑ q, co q (y⁻¹ * X) • Rd (bs q) H y := by
  have hu : IsUnit y.det := isUnit_iff_ne_zero.2 hy
  rw [← fderiv_mul_expand, Matrix.mul_nonsing_inv_cancel_left y X hu]

theorem exists_integralCombination_of_mem_completedLattice (L : List (Idx n)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → Mat n → ℝ) (w : ι → List (Idx n)),
      (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
        ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  induction L with
  | nil =>
    exact ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => contDiffOn_const,
      fun V _ _ f _ y _ => by simp [Dw_nil, Rw]⟩
  | cons p L ih =>
    obtain ⟨ι, _, c, w, hc, h⟩ := ih
    refine ⟨ι ⊕ (ι × Idx n), inferInstance,
      Sum.elim (fun i y => fderiv ℝ (c i) y (bs p)) (fun e y => c e.1 y * co e.2 (y⁻¹ * bs p)),
      Sum.elim w (fun e => e.2 :: w e.1), ?_, ?_⟩
    · rintro (i | ⟨i, q⟩)
      · exact ((hc i).fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply contDiffOn_const
      · exact (hc i).mul (co_smooth p q)
    · intro V _ _ f hf y hy
      have hev : Dw L f =ᶠ[nhds y] fun z => ∑ i, c i z • Rw (w i) f z := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz using h V f hf z hz
      have hdc : ∀ i, DifferentiableAt ℝ (c i) y := fun i =>
        ((hc i).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      have hdr : ∀ i, DifferentiableAt ℝ (Rw (w i) f) y := fun i =>
        ((Rw_smooth hf (w i)).contDiffAt (isOpen_GLs.mem_nhds hy)).differentiableAt (by simp)
      show fderiv ℝ (Dw L f) y (bs p) = _
      have hd : HasFDerivAt (fun z => ∑ i, c i z • Rw (w i) f z)
          (∑ i, (c i y • fderiv ℝ (Rw (w i) f) y +
            (fderiv ℝ (c i) y).smulRight (Rw (w i) f y))) y :=
        HasFDerivAt.fun_sum fun i _ => (hdc i).hasFDerivAt.fun_smul (hdr i).hasFDerivAt
      rw [hev.fderiv_eq, hd.fderiv]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_comm]
      congr 1
      rw [fderiv_expand _ hy, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_smul]
      rfl

theorem Dw_eq_comb : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  intro n L
  obtain ⟨ι, _, c, w, hc, h⟩ := exists_integralCombination_of_mem_completedLattice L
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => c (e.symm i), fun i => w (e.symm i), fun i => hc _, ?_⟩
  intro V _ _ f hf y hy
  rw [h V f hf y hy]
  exact (Equiv.sum_comp e.symm fun i => c i y • Rw (w i) f y).symm

end GlobalTheory.CompanionTheory.SobGL.Expand
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeAsRightWordsStatement
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_as_right_words : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | exact GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | (intros; apply GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FderivZeroApply
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.OmDec

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_sub_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g)
    (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f - h) g v = fderiv ℝ f g v - fderiv ℝ h g v := by
  rw [fderiv_sub hf hh]; rfl

theorem fderiv_zero_apply' (g v : E) : fderiv ℝ (0 : E → F) g v = 0 := by
  have h : fderiv ℝ (0 : E → F) g = 0 := by
    simpa using (fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : F))
  rw [h]; rfl

end General

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_left (A B : Mat n) (h : Mat n → V) : Rd (A - B) h = Rd A h - Rd B h := by
  funext g; simp [Rd, mul_sub]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  exact fderiv_zero_apply' _ _

theorem Rd_add_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a + b) g = Rd X a g + Rd X b g :=
  RCalc.fderiv_add_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_sub_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a - b) g = Rd X a g - Rd X b g :=
  fderiv_sub_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_smul_right (c : ℂ) (X : Mat n) {a : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (c • a) g = c • Rd X a g :=
  RCalc.fderiv_csmul_apply (RCalc.differentiableAt_of_smooth ha hg) c _

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  show ∑ d, Eu s c d (Epow s 0 d a f) = _
  rw [Finset.sum_eq_single a]
  · simp [Epow]
  · intro d _ hd
    simp [Epow, hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) :
    gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  show ∑ c, Eu s a c (Epow s 1 c a f) = _
  simp only [Epow_one]

theorem Eu_Eu_apply (s : Bool) (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) (ε : ℂ)
    (hε : ε = if s then -Complex.I else Complex.I) :
    Eu s a b (Eu s c d f) g = (1 / 4 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        + ε • Rd (Matrix.single a b 1) (Rd (Matrix.single c d Complex.I) f) g
        + ε • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d 1) f) g
        + (ε * ε) • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  have hX := RCalc.Rd_contDiffOn (Matrix.single c d (1 : ℂ)) hf
  have hY := RCalc.Rd_contDiffOn (Matrix.single c d Complex.I) hf
  have hS : ContDiffOn ℝ ∞ (ε • Rd (Matrix.single c d Complex.I) f) (GLs n) := hY.const_smul ε
  have key : ∀ Z : Mat n, Rd Z (Eu s c d f) g =
      (1 / 2 : ℂ) • (Rd Z (Rd (Matrix.single c d 1) f) g
        + ε • Rd Z (Rd (Matrix.single c d Complex.I) f) g) := by
    intro Z
    have e : Eu s c d f = (1 / 2 : ℂ) • (Rd (Matrix.single c d 1) f
        + ε • Rd (Matrix.single c d Complex.I) f) := by
      rw [hε]; rfl
    have hA : ContDiffOn ℝ ∞ (Rd (Matrix.single c d 1) f + ε • Rd (Matrix.single c d Complex.I) f)
        (GLs n) := hX.add hS
    rw [e, Rd_smul_right _ _ hA hg, Rd_add_right _ hX hS hg, Rd_smul_right _ _ hY hg]
  have e2 : Eu s a b (Eu s c d f) g = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) (Eu s c d f) g
      + ε • Rd (Matrix.single a b Complex.I) (Eu s c d f) g) := by
    rw [hε]; rfl
  rw [e2, key, key]
  module

theorem Eu_pair_apply (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Eu true a b (Eu true c d f) g + Eu false a b (Eu false c d f) g = (1 / 2 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  rw [Eu_Eu_apply true a b c d hf hg (-Complex.I) (by simp),
    Eu_Eu_apply false a b c d hf hg Complex.I (by simp)]
  have h1 : (-Complex.I) * (-Complex.I) = -1 := by simp
  have h2 : Complex.I * Complex.I = -1 := by simp
  rw [h1, h2]
  module

theorem Om_apply {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om f g = ∑ a, ∑ b, (Rd (Matrix.single a b 1) (Rd (Matrix.single b a 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single b a Complex.I) f) g) := by
  have h : Om f g = (2 : ℂ) • ∑ a, ∑ b,
      (Eu true a b (Eu true b a f) g + Eu false a b (Eu false b a f) g) := by
    simp only [Om, gel_two, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib]
  rw [h]
  simp only [Eu_pair_apply _ _ _ _ hf hg, Finset.smul_sum, smul_smul]
  norm_num

theorem Rd_sq_add (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A + B) (Rd (A + B) f) g =
      Rd A (Rd A f) g + Rd A (Rd B f) g + Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [RCalc.Rd_add_left A B f, RCalc.Rd_add_left A B (Rd A f + Rd B f)]
  simp only [Pi.add_apply]
  rw [Rd_add_right _ dA dB hg, Rd_add_right _ dA dB hg]
  abel

theorem Rd_sq_sub (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A - B) (Rd (A - B) f) g =
      Rd A (Rd A f) g - Rd A (Rd B f) g - Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [Rd_sub_left A B f, Rd_sub_left A B (Rd A f - Rd B f)]
  simp only [Pi.sub_apply]
  rw [Rd_sub_right _ dA dB hg, Rd_sub_right _ dA dB hg]
  abel

theorem sum_Ix (F : Ix n → V) :
    ∑ p, F p = ∑ a, ∑ b, (F (true, a, b) + F (false, a, b)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]

theorem sum_reindex (x y : Fin n → Fin n → V) :
    ∑ a, ∑ b, (x a b - y a b) = (1 / 4 : ℂ) • ∑ a, ∑ b,
      ((2 : ℂ) • (x a b + x b a) - (2 : ℂ) • (y a b + y b a)) := by
  have hx : ∑ a, ∑ b, x b a = ∑ a, ∑ b, x a b := Finset.sum_comm
  have hy : ∑ a, ∑ b, y b a = ∑ a, ∑ b, y a b := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hx, hy]
  module

theorem Om_eq_squares {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) :
    ContDiffOn ℝ ∞ f (GLs n) → ∀ g ∈ GLs n,
      Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g
        - (1 / 4 : ℂ) • ∑ p : Ix n, Rd (sk p) (Rd (sk p) f) g := by
  intro hf g hg
  rw [Om_apply hf hg, sum_reindex, sum_Ix, sum_Ix, ← smul_sub]
  congr 1
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e1 : hm (n := n) (true, a, b) = Matrix.single a b 1 + Matrix.single b a 1 := by simp [hm]
  have e2 : hm (n := n) (false, a, b) =
      Matrix.single a b Complex.I - Matrix.single b a Complex.I := by simp [hm]
  have e3 : sk (n := n) (true, a, b) = Matrix.single a b 1 - Matrix.single b a 1 := by simp [sk]
  have e4 : sk (n := n) (false, a, b) =
      Matrix.single a b Complex.I + Matrix.single b a Complex.I := by simp [sk]
  rw [e1, e2, e3, e4, Rd_sq_add _ _ hf hg, Rd_sq_sub _ _ hf hg, Rd_sq_add _ _ hf hg,
    Rd_sq_sub _ _ hf hg]
  module

end GlobalTheory.CompanionTheory.WaveSpd.OmDec
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrETransposeEqPhiSeq
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.GlTranspose

variable {n : ℕ} {A : Type} [Ring A]

theorem epw_zero (e : Fin n → Fin n → A) (a b : Fin n) :
    Epw e 0 a b = if a = b then 1 else 0 := by
  rw [Epw]

theorem epw_succ (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, e a c * Epw e m c b := by
  rw [Epw]

theorem epw_succ_right (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, Epw e m a c * e c b := by
  induction m generalizing a b with
  | zero =>
    simp [epw_succ, epw_zero]
  | succ m ih =>
    calc Epw e (m + 1 + 1) a b = ∑ c, e a c * ∑ d, Epw e m c d * e d b := by
          rw [epw_succ]
          exact sum_congr rfl fun c _ => by rw [ih]
      _ = ∑ d, (∑ c, e a c * Epw e m c d) * e d b := by
          simp only [mul_sum, sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ c, Epw e (m + 1) a c * e c b := sum_congr rfl fun d _ => by rw [epw_succ]

theorem bco_zero_zero (N : A) (τ : ℕ → A) : bco N τ 0 0 = 1 := by rw [bco]

theorem bco_zero_succ (N : A) (τ : ℕ → A) (j : ℕ) : bco N τ 0 (j + 1) = 0 := by rw [bco]

theorem bco_succ_zero (N : A) (τ : ℕ → A) (m : ℕ) :
    bco N τ (m + 1) 0 = N * bco N τ m 0 - τ m := by rw [bco]

theorem bco_succ_succ (N : A) (τ : ℕ → A) (m j : ℕ) :
    bco N τ (m + 1) (j + 1) = bco N τ m j + N * bco N τ m (j + 1) := by rw [bco]

theorem bco_eq_zero (N : A) (τ : ℕ → A) (m j : ℕ) (h : m < j) : bco N τ m j = 0 := by
  induction m generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact bco_zero_succ N τ j
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [bco_succ_succ, ih j (by omega), ih (j + 1) (by omega)]
    simp

theorem bco_self (N : A) (τ : ℕ → A) (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => exact bco_zero_zero N τ
  | succ m ih =>
    rw [bco_succ_succ, ih, bco_eq_zero N τ m (m + 1) (by omega)]
    simp

theorem phiSeq_eq (N : A) (τ : ℕ → A) (m : ℕ) :
    phiSeq N τ m = τ m - ∑ j ∈ range m, bco N τ m j * phiSeq N τ j := by
  rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m]

section Gl

variable (e : Fin n → Fin n → A)
  (he : ∀ a b c d, e a b * e c d - e c d * e a b =
    (if b = c then e a d else 0) - (if a = d then e c b else 0))
include he

theorem comm_epw (m : ℕ) (a b c d : Fin n) :
    e a b * Epw e m c d - Epw e m c d * e a b =
      (if b = c then Epw e m a d else 0) - (if a = d then Epw e m c b else 0) := by
  induction m generalizing c d with
  | zero =>
    simp only [epw_zero]
    by_cases h1 : c = d
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h2, h3]
    · by_cases h2 : b = c
      · subst h2
        by_cases h3 : a = d
        · subst h3; simp [h1]
        · simp [h1, h3]
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h1, h2, h3]
  | succ m ih =>
    have step : ∀ f, e a b * (e c f * Epw e m f d) - (e c f * Epw e m f d) * e a b =
        ((if b = c then e a f else 0) - (if a = f then e c b else 0)) * Epw e m f d +
          e c f * ((if b = f then Epw e m a d else 0) - (if a = d then Epw e m f b else 0)) := by
      intro f
      rw [← he a b c f, ← ih f d]
      noncomm_ring
    rw [epw_succ e m c d, mul_sum, sum_mul, ← sum_sub_distrib, sum_congr rfl (fun f _ => step f)]
    simp only [sub_mul, mul_sub, sum_add_distrib, sum_sub_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : a = d <;>
      simp only [h1, h2, if_true, if_false, ← epw_succ, sum_const_zero] <;> abel

theorem transpose_step (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) b a =
      ∑ c, Epw e m c a * e b c + (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
  have h : Epw e (m + 1) b a - ∑ c, Epw e m c a * e b c =
      (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
    rw [epw_succ, ← sum_sub_distrib,
      sum_congr rfl (fun c _ => comm_epw e he m b c c a), sum_sub_distrib]
    by_cases h1 : a = b
    · subst h1; simp [trE]
    · have h2 : ¬ b = a := fun h => h1 h.symm
      simp [h1, h2]
  rw [add_sub_assoc, ← h]
  abel

theorem transpose_poly (m : ℕ) (a b : Fin n) :
    Epw e m b a =
      ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * Epw (fun a b => e b a) j a b := by
  induction m generalizing a b with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, bco_zero_zero, one_mul, epw_zero]
    simp only [eq_comm]
  | succ m ih =>
    set f : Fin n → Fin n → A := fun a b => e b a with hf
    set N : A := (n : A) with hN
    set τ : ℕ → A := trE e with hτ
    have key : ∑ c, Epw e m c a * e b c =
        ∑ j ∈ range (m + 1), bco N τ m j * Epw f (j + 1) a b := by
      simp only [epw_succ_right f, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [ih a c, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc]
    have hn : N * Epw e m b a =
        ∑ j ∈ range (m + 1), N * bco N τ m (j + 1) * Epw f (j + 1) a b +
          N * bco N τ m 0 * Epw f 0 a b := by
      rw [← sum_range_succ' (fun j => N * bco N τ m j * Epw f j a b) (m + 1),
        sum_range_succ _ (m + 1), bco_eq_zero N τ m (m + 1) (by omega), ih a b, mul_sum]
      simp [mul_assoc]
    rw [transpose_step e he, key, hn, sum_range_succ' _ (m + 1), bco_succ_zero]
    simp only [bco_succ_succ, add_mul, sum_add_distrib, sub_mul, epw_zero f]
    by_cases h1 : a = b
    · simp [h1]
      try abel
    · simp [h1]
      try abel

theorem trE_eq_sum (m : ℕ) :
    trE e m = ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * trE (fun a b => e b a) j := by
  have h : trE e m = ∑ a, Epw e m a a := rfl
  rw [h, sum_congr rfl (fun a _ => transpose_poly e he m a a), sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [trE, mul_sum]

end Gl

theorem trE_transpose_eq_phiSeq (n : ℕ) {A : Type} [Ring A] [Algebra ℂ A]
    (e : Fin n → Fin n → A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b =
      (if b = c then e a d else 0) - (if a = d then e c b else 0)) (m : ℕ) :
    trE (fun a b => e b a) m = phiSeq (n : A) (trE e) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h := trE_eq_sum e he m
    rw [sum_range_succ, bco_self, one_mul] at h
    have hs : ∑ j ∈ range m, bco (n : A) (trE e) m j * phiSeq (n : A) (trE e) j =
        ∑ j ∈ range m, bco (n : A) (trE e) m j * trE (fun a b => e b a) j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    rw [phiSeq_eq, hs, h, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.WaveMult.GlTranspose
end
