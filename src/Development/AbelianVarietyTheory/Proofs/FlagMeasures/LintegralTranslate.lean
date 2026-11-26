module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMapSurjectiveOfPrimitiveRows
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContinuousOnOfSmoothOnH
section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.SmoothDecompositionForms
open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1)

abbrev Mx (k r : ℕ) := Matrix (Ix k r) (Ix k r) ℂ

def Kmax (k r : ℕ) : Set (Mx k r) := UH (Hpk k r) ∩ (Matrix.unitaryGroup (Ix k r) ℂ : Set _)

structure HRep (k r : ℕ) : Type 1 where

  H : Type
  [instNorm : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℂ H]
  [instComplete : CompleteSpace H]

  σ : Mx k r → (H →L[ℂ] H)
  isURep : IsURepOn (UH (Hpk k r)) σ

attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete

variable {k r : ℕ}

def HRep.smooth (R : HRep k r) : Set R.H := smoothVecs (k := k) (r := r) R.σ

def LieWord (k r : ℕ) (w : List (Mx k r)) : Prop := ∀ X ∈ w, InLieHpk k r X

def HRep.semi (R : HRep k r) (Ws : List (List (Mx k r))) (v : R.H) : ℝ :=
  (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

structure IsSmoothMap (R₁ R₂ : HRep k r) (A : R₁.H → R₂.H) : Prop where
  maps : ∀ v ∈ R₁.smooth, A v ∈ R₂.smooth
  map_add : ∀ v ∈ R₁.smooth, ∀ w ∈ R₁.smooth, A (v + w) = A v + A w
  map_smul : ∀ (a : ℂ), ∀ v ∈ R₁.smooth, A (a • v) = a • A v
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ v ∈ R₁.smooth, ‖dsigW (k := k) (r := r) R₂.σ w (A v)‖ ≤ C * R₁.semi Ws v

section Tensor

variable {ι : Type} [Fintype ι]

def tensSmooth (ι : Type) (R : HRep k r) : Set (ι → R.H) := {x | ∀ c, x c ∈ R.smooth}

def tensAct (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) (g : Mx k r) (x : ι → R.H) : ι → R.H :=
  fun c => ∑ d, ρ g c d • R.σ g (x d)

def pureT {E : Type} [AddCommGroup E] [Module ℂ E] (a : ι → ℂ) (v : E) : ι → E := fun c => a c • v

def tensForm (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : ι → H) : ℂ :=
  ∑ c, ∑ d, A c d * ⟪y c, x d⟫_ℂ

def flat (A : Matrix ι ι ℂ) (y : ι → ℂ) : ι → ℂ := star y ᵥ* A

def contr (A : Matrix ι ι ℂ) (ω : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (x : ι → E) : E :=
  ∑ d, flat A ω d • x d

def IsSmoothMapInto (R₁ R : HRep k r) (A : R₁.H → ι → R.H) : Prop :=
  ∀ c, IsSmoothMap R₁ R fun v => A v c

structure IsSmoothMapFrom (R R₂ : HRep k r) (A : (ι → R.H) → R₂.H) : Prop where
  maps : ∀ x ∈ tensSmooth ι R, A x ∈ R₂.smooth
  map_add : ∀ x ∈ tensSmooth ι R, ∀ y ∈ tensSmooth ι R, A (x + y) = A x + A y
  map_smul : ∀ (a : ℂ), ∀ x ∈ tensSmooth ι R, A (a • x) = a • A x
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ x ∈ tensSmooth ι R, ‖dsigW (k := k) (r := r) R₂.σ w (A x)‖ ≤ C * ∑ c, R.semi Ws (x c)

structure IsSmoothDecomp (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J] (Rs : J → HRep k r)
    (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) : Prop where
  io_cont : ∀ j, IsSmoothMapInto (Rs j) R (io j)
  p_cont : ∀ j, IsSmoothMapFrom R (Rs j) (p j)
  io_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ v ∈ (Rs j).smooth, io j ((Rs j).σ g v) = tensAct ρ R g (io j v)
  p_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ x ∈ tensSmooth ι R, p j (tensAct ρ R g x) = (Rs j).σ g (p j x)
  p_io : ∀ j, ∀ v ∈ (Rs j).smooth, p j (io j v) = v
  p_io_ne : ∀ i j, i ≠ j → ∀ v ∈ (Rs j).smooth, p i (io j v) = 0
  sum_io_p : ∀ x ∈ tensSmooth ι R, ∑ j, io j (p j x) = x

structure IsSignedDecomp (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J]
    (Rs : J → HRep k r) (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) (ep : J → ℝ) : Prop
    extends IsSmoothDecomp ρ R Rs io p where
  sign : ∀ j, ep j = 1 ∨ ep j = -1
  form_eq : ∀ j, ∀ x ∈ (Rs j).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io j x) (io j y) = (ep j : ℂ) * ⟪y, x⟫_ℂ
  orth : ∀ i j, i ≠ j → ∀ x ∈ (Rs i).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io i x) (io j y) = 0

variable [DecidableEq ι]

structure IsFormRep (k r : ℕ) (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (l : ℕ) : Prop where
  map_one : ρ 1 = 1
  map_mul : ∀ g ∈ UH (Hpk k r), ∀ g' ∈ UH (Hpk k r), ρ (g * g') = ρ g * ρ g'
  smooth : ∀ c d, SmoothOnH (Hpk k r) fun g => ρ g c d
  herm : Aᴴ = A
  sq : A * A = 1
  inv : ∀ g ∈ UH (Hpk k r), (ρ g)ᴴ * A * ρ g = A
  unitK : ∀ g ∈ Kmax k r, ρ g ∈ Matrix.unitaryGroup ι ℂ
  growth : ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ∀ c d, ‖ρ g c d‖ ≤ C * Real.sqrt (hs g) ^ l

end Tensor

section Checks

variable {ι : Type} [Fintype ι]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

end
end

open Matrix Finset PI.UpqRep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.TensCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms (HRep IsSmoothMap IsSmoothMapInto IsSmoothMapFrom IsSmoothDecomp IsSignedDecomp IsFormRep
  tensSmooth tensAct tensForm pureT contr LieWord Mx Ix)

variable {k r : ℕ}

theorem isURepOn_of_isDS {R : BranchingSupport.Rep k r} {ε : Ix k r → Bool} {μ : Ix k r → ℝ} (h : R.IsDS ε μ) :
    IsURepOn (BranchingSupport.GG k r) R.σ := by
  obtain ⟨-, P, hP, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  refine ⟨⟨by simpa [hPP] using h1, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · have := hm _ (hmaps ha) _ (hmaps hb)
    have e2 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    simpa only [e2, e] using this
  · simpa only [e] using hn _ (hmaps hg) v
  · have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp h3.continuousOn hmaps
    simpa only [Function.comp_def, e] using this

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Smooth

section Tensor

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : HRep k r} {Rs : κ → HRep k r}
  {io : ∀ I, (Rs I).H → ι → R.H} {pr : ∀ I, ι → R.H → (Rs I).H} {p : ∀ I, (ι → R.H) → (Rs I).H} {ep : κ → ℝ}


end Tensor

end GlobalTheory.TensCompare

end
end

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.AmpMoments

theorem lenA_mul {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (t x : MatKR k r) (s : Fin (r + 1) → ℂ)
    (hs : ∀ a, s a ≠ 0) (ht : ∀ a, t⁻¹ *ᵥ fvec k r z a = s a • fvec k r z a) (a : Fin (r + 1)) :
    lenA k r z (t * x) a = ‖s a‖ * lenA k r z x a := by
  have e : ∀ b, (WithLp.toLp 2 ((t * x)⁻¹ *ᵥ fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) =
      s b • WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b) := fun b => by
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, WithLp.toLp_smul]
  unfold lenA
  simp only [e]
  set v : Fin (r + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b)
  have hsp : Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a}) = Submodule.span ℂ (v '' {b | b < a}) := by
    apply le_antisymm <;> refine Submodule.span_le.2 ?_ <;> rintro _ ⟨b, hb, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · have := Submodule.smul_mem (Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a})) (s b)⁻¹
        (Submodule.subset_span ⟨b, hb, rfl⟩)
      simp only [smul_smul, inv_mul_cancel₀ (hs b), one_smul] at this
      exact this
  rw [hsp, ← infDist_smul₀ (s a)]
  congr 1
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hs a)]
  exact ((Submodule.smul_mem_iff _ (inv_ne_zero (hs a)))).symm

theorem lintegral_translate {k r : ℕ} (ν : Measure (Mt k r)) (t : MatKR k r) (ht : IsUnit t.det)
    (F : Mt k r → ℝ≥0∞) :
    ∫⁻ y, F y ∂ν = ∫⁻ x, F (fun i j => (t * Matrix.of x) i j) ∂(ν.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) := by
  have hc : ∀ g : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x) i j : Mt k r) := fun g =>
    (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => (Matrix.mul_nonsing_inv_cancel_left t (Matrix.of x) ht :)
      right_inv := fun x => (Matrix.nonsing_inv_mul_cancel_left t (Matrix.of x) ht :)
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have := lintegral_map_equiv (μ := ν) (fun x => F (e.symm x)) e.toMeasurableEquiv
  refine Eq.trans ?_ this.symm
  exact lintegral_congr fun y => congrArg F (e.symm_apply_apply y).symm

theorem sq_nnnorm {V : Type} [NormedAddCommGroup V] (v : V) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]; rfl

theorem haar_of_conj {k r : ℕ} {μ : Measure (Mt k r)} {t : MatKR k r} (ht : IsUnit t.det)
    (hN : ∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r)
    (h : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j)) :
    PI.BesselPeriodGGP.IsHaarOn (Nset k r) μ := by
  have hc : ∀ g g' : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x * g') i j : Mt k r) :=
    fun g g' => ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const :
      Continuous fun x : MatKR k r => g * x * g')
  have hl : ∀ g : MatKR k r, Measurable (lmulM g : Mt k r → Mt k r) := fun g =>
    (show Continuous (lmulM g : Mt k r → Mt k r) from
      (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)).measurable
  have i1 : ∀ x : MatKR k r, t * (t⁻¹ * x * t) * t⁻¹ = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t x ht, Matrix.mul_nonsing_inv_cancel_right t x ht]
  have i2 : ∀ x : MatKR k r, t⁻¹ * (t * x * t⁻¹) * t = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left t x ht, Matrix.nonsing_inv_mul_cancel_right t x ht]
  let e0 : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j
      invFun := fun x => fun i j => (t * Matrix.of x * t⁻¹) i j
      left_inv := fun x => (i1 (Matrix.of x) :)
      right_inv := fun x => (i2 (Matrix.of x) :)
      continuous_toFun := hc _ _
      continuous_invFun := hc _ _ }
  let e := e0.toMeasurableEquiv
  obtain ⟨h1, h2, h3, h4⟩ : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map e) := h
  refine ⟨?_, fun h0 => h2 (by rw [h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
  · rw [← e.map_symm_map (μ := μ)]
    exact e.symm.sigmaFinite_map
  · rw [e.map_apply] at h3
    rw [← h3]
    congr 1
    ext x
    have := hN (t⁻¹ * Matrix.of x * t)
    rw [i1] at this
    exact not_congr this.symm
  · have hs' : t⁻¹ * s * t ∈ Nset k r := (hN _).2 (by rwa [i1])
    apply e.map_measurableEquiv_injective
    show (μ.map (lmulM s)).map e = μ.map e
    rw [← h4 _ hs', Measure.map_map e.measurable (hl _), Measure.map_map (hl _) e.measurable]
    congr 1
    funext x
    show t⁻¹ * (s * Matrix.of x) * t = t⁻¹ * s * t * (t⁻¹ * Matrix.of x * t)
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t _ ht]

theorem size_bound {b v g T x Cg Cu CT : ℝ} {r q : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hT : T ≤ b ^ (CT * (2 * r + 2 : ℝ))) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x ^ (2 * q) * Hsq r T (b ^ max 2 Cu) ^ q ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ) * q) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  have h2 : max 1 T ≤ b ^ (|CT| * (2 * r + 2 : ℝ)) :=
    max_le (Real.one_le_rpow hb1 (by positivity))
      (hT.trans (Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))))
  have h3 : x ^ 2 * Hsq r T (b ^ max 2 Cu) ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
    unfold Hsq
    calc x ^ 2 * (max 1 T * (b ^ max 2 Cu) ^ (20 * (r + 1)))
        ≤ (b ^ ((2 * Cg + 2) * r)) ^ 2 * (b ^ (|CT| * (2 * r + 2 : ℝ)) * (b ^ max 2 Cu) ^ (20 * (r + 1))) := by
          gcongr
      _ = b ^ ((2 * Cg + 2) * r * (2 : ℕ) + (|CT| * (2 * r + 2 : ℝ) + max 2 Cu * (20 * (r + 1) : ℕ))) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le _ 2,
            Real.rpow_mul_natCast hb0.le (max 2 Cu)]
      _ ≤ _ := by
          refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
          push_cast
          have := abs_nonneg CT
          nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]
  rw [pow_mul, ← mul_pow, Real.rpow_mul_natCast hb0.le]
  exact pow_le_pow_left₀ (by unfold Hsq; positivity) h3 q

theorem radius_bound {k r m N q : ℕ} {Cn Cq : ℝ} (hm : m = 2 * r + 2) (hk : m ^ 4 ≤ k) (hC : |Cn| + |Cq| ≤ m)
    (hN : (N : ℝ) ≤ Cn * k * (m : ℝ) ^ 3) (hq : (q : ℝ) ≤ Cq * (r : ℝ) ^ 3) :
    N + (r + 1) * q ≤ k * m ^ 5 ∧ (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 := by
  have a1 := abs_nonneg Cn
  have a2 := abs_nonneg Cq
  have hN' : N ≤ m * k * m ^ 3 := by
    have : (N : ℝ) ≤ m * k * (m : ℝ) ^ 3 := hN.trans (by gcongr; linarith [le_abs_self Cn])
    exact_mod_cast this
  have hq' : q ≤ m * r ^ 3 := by
    have : (q : ℝ) ≤ m * (r : ℝ) ^ 3 := hq.trans (by gcongr; linarith [le_abs_self Cq])
    exact_mod_cast this
  have h1 : (r + 1) * q ≤ m * k :=
    calc (r + 1) * q ≤ m * (m * m ^ 3) :=
          Nat.mul_le_mul (by omega) (hq'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)))
      _ = m * m ^ 4 := by ring
      _ ≤ m * k := Nat.mul_le_mul_left _ hk
  have h2 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) m
  constructor
  · calc N + (r + 1) * q ≤ m * k * m ^ 3 + m ^ 4 * k := Nat.add_le_add hN' (h1.trans (Nat.mul_le_mul_right _ h2))
      _ = k * m ^ 4 * 2 := by ring
      _ ≤ k * m ^ 4 * m := Nat.mul_le_mul_left _ (by omega)
      _ = k * m ^ 5 := by ring
  · have : m * k ≤ k * k := Nat.mul_le_mul_right _ (h2.trans hk)
    nlinarith

theorem isBesselMapSm_of {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (h : IsBesselMapSm (k := k) (r := r) z ψ σ π B) : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih =>
      show PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v) = dsig σ X (dsigW σ w v)
      rw [ih]; rfl
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  exact ⟨h1, h2, h3, C, Ws, h4, fun v hv => by simp only [e]; exact h5 v hv⟩

end GlobalTheory.AmpMoments
