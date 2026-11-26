module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKInvOfTriv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory

namespace GlobalTheory.WhitBump

abbrev Idx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

abbrev Vp (E : Type) [Field E] (n : ℕ) : Type := Idx n → Cinf E

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def nu (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else if i = j then 1 else 0

def sdM {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, x i j

theorem superDiag_eq_sdM {R : Type} [CommRing R] (g : GL (Fin n) R) :
    GlobalTheory.Whittaker.superDiag g = sdM (g : Matrix (Fin n) (Fin n) R) := rfl

theorem nu_lower (t : Vp E n) {i j : Fin n} (h : j < i) : nu t i j = 0 := by
  simp [nu, not_lt_of_gt h, ne_of_gt h]

theorem nu_diag (t : Vp E n) (i : Fin n) : nu t i i = 1 := by
  simp [nu]

theorem det_nu (t : Vp E n) : (nu t).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [nu_diag]
  · intro i j h; exact nu_lower t h

def nuGL (t : Vp E n) : GL (Fin n) (Cinf E) :=
  Matrix.nonsingInvUnit (nu t) (by rw [det_nu]; exact isUnit_one)

@[simp] theorem nuGL_val (t : Vp E n) : (nuGL t : Matrix (Fin n) (Fin n) (Cinf E)) = nu t := rfl

theorem nuGL_mem (t : Vp E n) : nuGL t ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun _ _ h => nu_lower t h, nu_diag t⟩

variable [_root_.NumberField.IsTotallyComplex E]

def psiInf (z : Cinf E) : ℂ := (GroundTheory.Global.adelicChar E (sInf E z) : ℂ)

def psiFin (a : Af E) : ℂ := (GroundTheory.Global.adelicChar E (sFin E a) : ℂ)

def bumpInf (f : Lie E n → ℝ) (x : Lie E n) : ℂ :=
  ∫ t : Vp E n, (f (toL (nu t * Matrix.of x)) : ℂ) * psiInf (-sdM (nu t))


open Classical in
def bumpFin (g : GL (Fin n) (Af E)) : ℂ :=
  if h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n then
    psiFin (GlobalTheory.Whittaker.superDiag h.choose) else 0

end GlobalTheory.WhitBump
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorProperties
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump.FinBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem psiFin_add (a b : Af E) : psiFin (a + b) = psiFin a * psiFin b := by
  simp only [psiFin, map_add (f := _), AddChar.map_add_eq_mul, Circle.coe_mul]

theorem bumpFin_eq (hK : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1)
    {g u : GL (Fin n) (Af E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hg : u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = psiFin (GlobalTheory.Whittaker.superDiag u) := by
  have h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n :=
    ⟨u, hu, hg⟩
  unfold bumpFin
  rw [dite_eq_left h]
  obtain ⟨hu', hg'⟩ := h.choose_spec
  set u' := h.choose
  have hw : u⁻¹ * u' ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) := mul_mem (inv_mem hu) hu'
  have hwK : u⁻¹ * u' ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
    have : u⁻¹ * u' = (u⁻¹ * g) * (u'⁻¹ * g)⁻¹ := by group
    rw [this]; exact mul_mem hg (inv_mem hg')
  have hsplit : u' = u * (u⁻¹ * u') := by group
  rw [hsplit, GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hw, psiFin_add, hK _ hw hwK, mul_one]

end GlobalTheory.WhitBump.FinBump

namespace GlobalTheory.WhitBump.FinBump

theorem bumpFin_zero_of_not {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {g : GL (Fin n) (Af E)}
    (h : ¬ ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = 0 := by
  unfold bumpFin; rw [dite_eq_right h]

theorem bumpFin_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) →
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  intro E _ _ _ n hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bumpFin_eq hK (one_mem _) (by simpa using one_mem _), hK 1 (one_mem _) (one_mem _)]
  · intro u hu g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : (u * v)⁻¹ * (u * g) = v⁻¹ * g := by group
      rw [bumpFin_eq hK (mul_mem hu hv) (by rw [e]; exact hvg), bumpFin_eq hK hv hvg,
        GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hv, psiFin_add]
    · rw [bumpFin_zero_of_not h, mul_zero]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, ?_⟩
      have e : (u⁻¹ * v)⁻¹ * g = v⁻¹ * (u * g) := by group
      rw [e]; exact hvg
  · intro k hk g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : v⁻¹ * (g * k) = (v⁻¹ * g) * k := by group
      rw [bumpFin_eq hK hv (by rw [e]; exact mul_mem hvg hk), bumpFin_eq hK hv hvg]
    · rw [bumpFin_zero_of_not h]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨v, hv, ?_⟩
      have e : v⁻¹ * g = (v⁻¹ * (g * k)) * k⁻¹ := by group
      rw [e]; exact mul_mem hvg (inv_mem hk)
  · intro g hg
    by_contra h
    exact hg (bumpFin_zero_of_not h)

end GlobalTheory.WhitBump.FinBump
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorPropertiesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerBumpFiniteFactor_properties : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1) → bumpFin (E := E) (n := n) 1 = 1 ∧ (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧ (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧ ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  first | exact @GlobalTheory.WhitBump.FinBump.bumpFin_props | exact GlobalTheory.WhitBump.FinBump.bumpFin_props | (intros; apply GlobalTheory.WhitBump.FinBump.bumpFin_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatrices
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem isCompact_GL_of_invSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)),
    IsCompact T → T ⊆ invSet E n →
      IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  intro E _ _ n T hT hsub
  haveI : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have hu : Continuous fun p : T =>
      (IsUnit.unit (hsub p.2 : IsUnit (Matrix.of p.1)) : GL (Fin n) (Cinf E)) := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have hinv : ContDiffOn ℝ ∞ (GlobalTheory.ConstTermSmooth.invM (E := E) (a := n)) (invSet E n) := by
      have h1 : ContDiffOn ℝ ∞ (fun y : Lie E n => Ring.inverse (Matrix.of y).det) (invSet E n) := fun y hy => by
        obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hy
        have := contDiffAt_ringInverse ℝ (n := ∞) u
        rw [hu] at this
        exact (this.comp y contDiff_det.contDiffAt).contDiffWithinAt
      refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
      have h2 : ContDiff ℝ ∞ fun y : Lie E n => (Matrix.of y).adjugate i j := by
        simp only [Matrix.adjugate_apply]
        have h3 : ContDiff ℝ ∞ fun y : Lie E n => (Function.update y j (Pi.single i 1) : Lie E n) := by
          refine contDiff_pi.2 fun k => ?_
          by_cases h : k = j
          · subst h; simpa using contDiff_const
          · simpa [Function.update_of_ne h] using contDiff_apply ℝ _ k
        exact contDiff_det.comp h3
      exact h1.mul h2.contDiffOn
    have := hinv.continuousOn.comp_continuous
      (f := fun p : T => (p : Lie E n)) continuous_subtype_val fun p => hsub p.2
    refine Continuous.congr this fun p => ?_
    simp only [Matrix.coe_units_inv]
    rfl
  convert isCompact_range hu using 1
  ext y
  constructor
  · intro hy
    exact ⟨⟨toL (y : Matrix (Fin n) (Fin n) (Cinf E)), hy⟩, Units.ext rfl⟩
  · rintro ⟨p, rfl⟩
    exact p.2

end GlobalTheory.WhitBump
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatricesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)), IsCompact T → T ⊆ invSet E n → IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  first | exact @GlobalTheory.WhitBump.isCompact_GL_of_invSet | exact GlobalTheory.WhitBump.isCompact_GL_of_invSet | (intros; apply GlobalTheory.WhitBump.isCompact_GL_of_invSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertib
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertib
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump Metric Set
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem contDiff_nu_apply (i k : Fin n) : ContDiff ℝ ∞ fun t : Vp E n => nu t i k := by
  by_cases h : i < k
  · have e : (fun t : Vp E n => nu t i k) = fun t => t ⟨(i, k), h⟩ := funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_apply ℝ _ _
  · have e : (fun t : Vp E n => nu t i k) = fun _ => (if i = k then 1 else 0 : Cinf E) :=
      funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_const

theorem contDiff_nu_mul : ContDiff ℝ ∞ fun q : Lie E n × Vp E n => toL (nu (-q.2) * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ fun q : Lie E n × Vp E n => ∑ k, nu (-q.2) i k * q.1 k j
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_nu_apply i k).comp contDiff_snd.neg).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

variable [_root_.NumberField.IsTotallyComplex E]

theorem continuous_psiInf_sdM : Continuous fun t : Vp E n => psiInf (-sdM (nu t)) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  have hd : Continuous fun t : Vp E n => sdM (nu t) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (contDiff_nu_apply i j).continuous
  exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (hs.comp hd.neg))

theorem bumpInf_contDiffOn_invSet : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ),
    ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  open scoped Pointwise in
  intro E _ _ _ n f hf hcs hts
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_invSet x₀ hx₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hB : closedBall x₀ r ⊆ invSet E n := (closedBall_subset_ball (by linarith)).trans hball

  let Φ : Lie E n × Lie E n → Vp E n := fun q p => (Matrix.of q.1 * Matrix.of (ConstTermSmooth.invM q.2)) p.1.1 p.1.2
  have hΦ : ContinuousOn Φ (tsupport f ×ˢ closedBall x₀ r) := by
    have hinv : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2) (tsupport f ×ˢ closedBall x₀ r) :=
      ConstTermSmooth.contDiffOn_invM.continuousOn.comp continuous_snd.continuousOn fun q hq => hB hq.2
    refine continuousOn_pi.2 fun p => ?_
    show ContinuousOn (fun q : Lie E n × Lie E n => ∑ k, q.1 p.1.1 k * ConstTermSmooth.invM q.2 k p.1.2) _
    refine continuousOn_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun q : Lie E n × Lie E n => q.1 p.1.1 k :=
      (continuous_apply k).comp ((continuous_apply p.1.1).comp continuous_fst)
    have h2 : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2 k p.1.2) (tsupport f ×ˢ closedBall x₀ r) :=
      (((continuous_apply p.1.2).comp (continuous_apply k) : Continuous fun m : Lie E n => m k p.1.2)).comp_continuousOn hinv
    exact h1.continuousOn.mul h2
  set K := Φ '' (tsupport f ×ˢ closedBall x₀ r) with hK
  have hKc : IsCompact K := (hcs.isCompact.prod (isCompact_closedBall _ _)).image_of_continuousOn hΦ

  let g : Lie E n → Vp E n → ℂ := fun x y => (f (toL (nu (-y) * Matrix.of x)) : ℂ)
  have hgs : ∀ p, ∀ y, p ∈ ball x₀ r → y ∉ -K → g p y = 0 := by
    intro p y hp hy
    by_contra hne
    have h : f (toL (nu (-y) * Matrix.of p)) ≠ 0 := fun h => hne (by simp [g, h])
    refine hy (Set.mem_neg.2 ⟨(toL (nu (-y) * Matrix.of p), p), ⟨subset_tsupport _ h, ball_subset_closedBall hp⟩, ?_⟩)
    have hu : IsUnit (Matrix.of p).det := (Matrix.isUnit_iff_isUnit_det _).1 (hB (ball_subset_closedBall hp))
    funext q
    have e : Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p) = nu (-y) :=
      Matrix.mul_nonsing_inv_cancel_right _ _ hu
    show (Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p)) q.1.1 q.1.2 = _
    rw [e]
    simp [nu, q.2]
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿g) (ball x₀ r ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp (hf.comp contDiff_nu_mul)).contDiffOn
  have hF : LocallyIntegrable (fun t : Vp E n => psiInf (-sdM (nu t))) volume :=
    continuous_psiInf_sdM.locallyIntegrable
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Lie E n => (0 : Vp E n)) (ball x₀ r) := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.mul ℝ ℂ) hv isOpen_ball hKc.neg hgs hF hg
  have fin : ContDiffOn ℝ ∞ (bumpInf f) (ball x₀ r) := by
    refine main.congr fun x _ => ?_
    simp only [bumpInf, convolution_def, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
  exact fin.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr0))

end GlobalTheory.WhitBump
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertibStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  first | exact @GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | exact GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | (intros; apply GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegral
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem psiFin_superDiag_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) →
    u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  intro E _ _ _ n u _ hk
  have hent := ((GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E n).1 hk).1
  have hs : GlobalTheory.Whittaker.superDiag u ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
    unfold GlobalTheory.Whittaker.superDiag
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => hent i j
  have hd : sFin E (GlobalTheory.Whittaker.superDiag u) ∈ GroundTheory.Global.invDifferentAdeles E :=
    GroundTheory.Global.mem_invDifferentAdeles.mpr
      (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hs)
  unfold psiFin
  rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hd]
  have h0 : (sFin E (GlobalTheory.Whittaker.superDiag u)).1 = 0 := rfl
  rw [h0, map_zero, neg_zero, AddChar.map_zero_eq_one]
  simp

end GlobalTheory.WhitBump
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharFiniteSuperDiagonalSumIntegralStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GL (Fin n) (Af E)), u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) → u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1 := by
  first | exact @GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | exact GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral | (intros; apply GlobalTheory.WhitBump.psiFin_superDiag_eq_one_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreserving
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreserving
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump.Shear

theorem det_eq_one_of_isNilpotent_sub_one {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : V →ₗ[ℝ] V) (hf : IsNilpotent (f - 1)) : LinearMap.det f = 1 := by
  let b := Module.finBasis ℝ V
  rw [← LinearMap.det_toMatrix b]
  set B := LinearMap.toMatrix b b f with hB
  have hBB : LinearMap.toMatrixAlgEquiv b f = B := by
    ext i j; simp [hB, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have h3 : IsNilpotent (B - 1) := by
    have : B - 1 = LinearMap.toMatrixAlgEquiv b (f - 1) := by
      rw [map_sub, map_one, hBB]
    rw [this]; exact hf.map _
  have h4 : IsNilpotent (1 - B) := by rw [← neg_sub]; exact h3.neg
  have h5 := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h4).map (Polynomial.evalRingHom (1 : ℝ))
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_sub, Matrix.eval_charpoly, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, map_one, sub_sub_cancel] at h5
  exact sub_eq_zero.1 h5.eq_zero

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def above (M : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n := fun p => M p.1.1 p.1.2

def sU (t : Vp E n) : Matrix (Fin n) (Fin n) (Cinf E) :=
  Matrix.of fun i j => if h : i < j then t ⟨(i, j), h⟩ else 0

theorem nu_eq (t : Vp E n) : nu t = 1 + sU t := by
  ext i j
  simp only [nu, sU, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases h : i < j
  · simp [h, ne_of_lt h]
  · by_cases h' : i = j
    · subst h'; simp
    · simp [h, h']

theorem nu_above {M : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → M i j = 0) (hd : ∀ i, M i i = 1) :
    nu (above M) = M := by
  ext i j
  simp only [nu, above, Matrix.of_apply]
  rcases lt_trichotomy i j with h | h | h
  · simp [h]
  · subst h; simp [hd]
  · simp [not_lt_of_gt h, ne_of_gt h, hl i j h]

def lin (u : Matrix (Fin n) (Fin n) (Cinf E)) : Vp E n →ₗ[ℝ] Vp E n where
  toFun t := above (sU t * u)
  map_add' a b := by
    have : sU (a + b) = sU a + sU b := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.add_apply]; split_ifs <;> simp
    rw [this, Matrix.add_mul]; rfl
  map_smul' r a := by
    have : sU (r • a) = r • sU a := by
      ext i j; simp only [sU, Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp
    rw [this, Matrix.smul_mul]; rfl

theorem lin_apply (u : Matrix (Fin n) (Fin n) (Cinf E)) (t : Vp E n) : lin u t = above (sU t * u) := rfl

theorem sub_one_vanish {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0) (hd : ∀ i, u i i = 1)
    (c : ℕ) (t : Vp E n) (ht : ∀ p : Idx n, p.1.2.val < c → t p = 0) :
    ∀ p : Idx n, p.1.2.val < c + 1 → ((lin u - 1) t) p = 0 := by
  intro p hp
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only at hp hij
  rw [LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply, lin_apply, sub_eq_zero]
  simp only [above, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [sU, hij, hd]
  · intro k _ hkj
    rcases lt_or_gt_of_ne hkj with hk | hk
    · have : sU t i k = 0 := by
        simp only [sU, Matrix.of_apply]
        split_ifs with h
        · exact ht _ (by simp only; have := Fin.lt_def.1 hk; omega)
        · rfl
      rw [this, zero_mul]
    · rw [hl k j hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem isNilpotent_lin_sub_one {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : IsNilpotent (lin u - 1) := by
  have key : ∀ m : ℕ, ∀ t : Vp E n, ∀ p : Idx n, p.1.2.val < m → (((lin u - 1) ^ m) t) p = 0 := by
    intro m
    induction m with
    | zero => intro t p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ m ih =>
      intro t p hp
      rw [pow_succ', Module.End.mul_apply]
      exact sub_one_vanish hl hd m _ (ih t) p hp
  exact ⟨n, LinearMap.ext fun t => funext fun p => key n t p p.1.2.isLt⟩

theorem det_lin {u : Matrix (Fin n) (Fin n) (Cinf E)} (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) : LinearMap.det (lin u) = 1 :=
  det_eq_one_of_isNilpotent_sub_one _ (isNilpotent_lin_sub_one hl hd)

end GlobalTheory.WhitBump.Shear


open GlobalTheory.WhitBump.Shear in
theorem GlobalTheory.WhitBump.exists_shear_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ)
    (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) →
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  intro E _ _ n u hu
  obtain ⟨hl, hd⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Vp E n)) := Measure.pi.isAddHaarMeasure _
  set L := lin (u : Matrix (Fin n) (Fin n) (Cinf E)) with hLdef
  have hdet : LinearMap.det L = 1 := det_lin hl hd
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact one_ne_zero
  let e := (LinearMap.equivOfDetNeZero L hdet0).toContinuousLinearEquiv
  let h := e.toHomeomorph.trans (Homeomorph.addLeft (above (u : Matrix (Fin n) (Fin n) (Cinf E))))
  refine ⟨h.toMeasurableEquiv, ?_, ?_⟩
  · have hL : MeasurePreserving L volume volume :=
      ⟨L.continuous_of_finiteDimensional.measurable, by
        rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, hdet]; simp⟩
    have := (measurePreserving_add_left volume (above (u : Matrix (Fin n) (Fin n) (Cinf E)))).comp hL
    exact this
  · intro t
    have hmem : nuGL t * u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) := mul_mem (nuGL_mem t) hu
    obtain ⟨hl', hd'⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hmem
    simp only [Units.val_mul, nuGL_val] at hl' hd'
    have : h.toMeasurableEquiv t = above (nu t * (u : Matrix (Fin n) (Fin n) (Cinf E))) := by
      show above _ + L t = _
      rw [hLdef, lin_apply, nu_eq, Matrix.add_mul, Matrix.one_mul]
      rfl
    rw [this, nu_above hl' hd']
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreservingStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_translation_measure_preserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) → ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧ ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  first | exact @GlobalTheory.WhitBump.exists_shear_measurePreserving | exact GlobalTheory.WhitBump.exists_shear_measurePreserving | (intros; apply GlobalTheory.WhitBump.exists_shear_measurePreserving <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFinite
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem adele_eq_sInf_add_sFin {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (x : Ad E) :
    x = sInf E (pInf E x) + sFin E (pFin E x) := by
  refine Prod.ext ?_ ?_
  · change x.1 = infEq E ((infEq E).symm x.1) + 0
    simp
  · change x.2 = 0 + x.2
    simp

theorem psiN_split : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  intro E _ _ _ n u
  have h : GlobalTheory.Whittaker.superDiag u = sInf E (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) + sFin E (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.Whittaker.superDiag, sdM, map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact adele_eq_sInf_add_sFin _
  unfold GlobalTheory.JSW.psiN psiInf psiFin
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.WhitBump
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFiniteStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  first | exact @GlobalTheory.WhitBump.psiN_split | exact GlobalTheory.WhitBump.psiN_split | (intros; apply GlobalTheory.WhitBump.psiN_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerBumpArchimedeanFactorOneNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerBumpArchimedeanFactorOneNeZero
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WhitBump

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem continuous_psiInf : Continuous (psiInf (E := E)) := by
  have hs : Continuous (fun z : Cinf E => sInf E z) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact continuous_subtype_val.comp ((GroundTheory.Global.continuous_adelicChar (K := E)).comp hs)

theorem psiInf_zero : psiInf (0 : Cinf E) = 1 := by
  simp [psiInf, map_zero]

variable {E} {n : ℕ}

theorem continuous_sdM_of : Continuous fun x : Lie E n => sdM (Matrix.of x) := by
  unfold sdM
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (continuous_apply j).comp (continuous_apply i)

theorem sdM_one : sdM (1 : Matrix (Fin n) (Fin n) (Cinf E)) = 0 := by
  unfold sdM
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j hj => ?_
  have hj' := (Finset.mem_filter.1 hj).2
  exact Matrix.one_apply_ne fun e => by subst e; omega

theorem continuous_toL_nu : Continuous fun t : Vp E n => toL (nu t) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun t : Vp E n => nu t i j
  by_cases hij : i < j
  · simp only [nu, Matrix.of_apply, dif_pos hij]
    exact continuous_apply _
  · simp only [nu, Matrix.of_apply, dif_neg hij]
    exact continuous_const

theorem nu_zero : nu (0 : Vp E n) = 1 := by
  ext i j
  by_cases hij : i < j
  · simp [nu, hij, Matrix.one_apply, hij.ne]
  · simp [nu, hij, Matrix.one_apply]

theorem exists_bumpInf_oneL_ne_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) :
    ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
      bumpInf f (oneL E n) ≠ 0 := by
  classical
  set h : Lie E n → ℝ := fun x => (psiInf (-sdM (Matrix.of x))).re with hh
  have hc : Continuous h :=
    Complex.continuous_re.comp ((continuous_psiInf E).comp continuous_sdM_of.neg)
  have hof : Matrix.of (oneL E n) = 1 := Matrix.of.apply_symm_apply _
  have h1 : h (oneL E n) = 1 := by
    simp only [hh, hof, sdM_one, neg_zero, psiInf_zero, Complex.one_re]
  have hU : {x | 0 < h x} ∩ invSet E n ∈ nhds (oneL E n) :=
    Filter.inter_mem ((isOpen_lt continuous_const hc).mem_nhds (by simp [h1]))
      (isOpen_invSet.mem_nhds (by change IsUnit (Matrix.of (oneL E n)); rw [hof]; exact isUnit_one))
  obtain ⟨f, hfs, hfc, hfd, hfr, hf1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  refine ⟨f, hfd, hfc, hfs.trans Set.inter_subset_right, ?_⟩
  set φ : Vp E n → Lie E n := fun t => toL (nu t) with hφ
  have hφc : Continuous φ := continuous_toL_nu
  set ψ : Lie E n → Vp E n := fun x p => x p.1.1 p.1.2 with hψ
  have hψc : Continuous ψ := continuous_pi fun p => (continuous_apply p.1.2).comp (continuous_apply p.1.1)
  have hψφ : ∀ t, ψ (φ t) = t := fun t => by
    funext p
    change nu t p.1.1 p.1.2 = t p
    simp [nu, p.2]
  have hfφ : HasCompactSupport (fun t => f (φ t)) := by
    refine HasCompactSupport.intro ((hfc.isCompact).image hψc) fun t ht => ?_
    by_contra hne
    exact ht ⟨φ t, subset_tsupport _ hne, hψφ t⟩
  have hsd : ∀ t, sdM (nu t) = sdM (Matrix.of (φ t)) := fun t => by
    rw [hφ]; simp only [toL, Equiv.apply_symm_apply]
  have hb : bumpInf f (oneL E n) = ∫ t : Vp E n, (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) := by
    rw [bumpInf, hof]
    simp only [Matrix.mul_one, hsd]
    rfl
  set G : Vp E n → ℂ := fun t => (f (φ t) : ℂ) * psiInf (-sdM (Matrix.of (φ t))) with hG
  have hGc : Continuous G :=
    (Complex.continuous_ofReal.comp (hfd.continuous.comp hφc)).mul
      ((continuous_psiInf E).comp (continuous_sdM_of.neg.comp hφc))
  have hGs : HasCompactSupport G := (hfφ.comp_left Complex.ofReal_zero).mul_right
  have hint : Integrable G := hGc.integrable_of_hasCompactSupport hGs
  have hre : (∫ t, G t).re = ∫ t, f (φ t) * h (φ t) := by
    have := (Complex.reCLM.integral_comp_comm hint).symm
    simp only [Complex.reCLM_apply] at this
    rw [this]
    congr 1
    funext t
    simp [hG, hh, Complex.re_ofReal_mul]
  haveI : (volume : Measure (InfinitePlace E → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  haveI : (volume : Measure (Vp E n)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  have hpos : 0 < ∫ t, f (φ t) * h (φ t) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Vp E n))
      ((hfd.continuous.comp hφc).mul (hc.comp hφc)) hfφ.mul_right (fun t => ?_) ?_
    · have h0 : 0 ≤ f (φ t) := (hfr ⟨φ t, rfl⟩).1
      by_cases hz : f (φ t) = 0
      · simp [hz]
      · exact mul_nonneg h0 (hfs (subset_tsupport _ hz)).1.le
    · have : φ 0 = oneL E n := by rw [hφ]; simp only [nu_zero]
      simp [this, hf1, h1]
  intro h0
  rw [hb] at h0
  rw [h0, Complex.zero_re] at hre
  linarith

end GlobalTheory.WhitBump
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerBumpArchimedeanFactorOneNeZeroStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ), ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧ bumpInf f (oneL E n) ≠ 0 := by
  first | exact @GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero | exact GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero | (intros; apply GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem shear (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n)) :
    ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧
      ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := GlobalTheory.T.unipotent_translation_measure_preserving E n u hu

theorem isCompact_setOf_toL (T : Set (Lie E n)) (hT : IsCompact T) (hs : T ⊆ invSet E n) :
    IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices E n T hT hs

variable [_root_.NumberField.IsTotallyComplex E]

theorem contDiffOn_bumpInf (f : Lie E n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ invSet E n) : ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible E n f hf hc hs

theorem exists_bumpInf_ne : ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧
    bumpInf f (oneL E n) ≠ 0 := GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero E n

theorem psiFin_integral (u : GL (Fin n) (Af E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hk : u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) : psiFin (GlobalTheory.Whittaker.superDiag u) = 1 :=
  GlobalTheory.T.standardAdelicCharFinite_superDiagonalSum_integral_eq_one E n u hu hk

theorem bumpFin_spec
    (htriv : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) :
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := GlobalTheory.T.whittakerBumpFiniteFactor_properties E n htriv

theorem psiN_eq (u : GA E n) :
    GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) *
      psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := GlobalTheory.T.adelicGenericUnipotentCharacter_eq_arch_mul_finite E n u

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem continuous_finGL_bump : Continuous (finGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sFin E : Af E → Ad E) :=
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

variable [_root_.NumberField.IsTotallyComplex E]

theorem psiInf_add (a b : Cinf E) : psiInf (a + b) = psiInf a * psiInf b := by
  simp [psiInf, map_add (f := _), AddChar.map_add_eq_mul]

theorem bumpInf_mul (f : Lie E n → ℝ) (u : GL (Fin n) (Cinf E)) (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (x : Lie E n) :
    bumpInf f (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
      psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) * bumpInf f x := by
  obtain ⟨τ, hτ, hτu⟩ := shear u hu
  have hsd : ∀ t, sdM (nu (τ t)) = sdM (nu t) + sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) := fun t => by
    rw [hτu, ← nuGL_val, ← superDiag_eq_sdM, ← superDiag_eq_sdM, ← Units.val_mul, ← superDiag_eq_sdM]
    exact GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip (nuGL_mem t) hu
  have key : ∀ t, (f (toL (nu t * Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)))) : ℂ) *
      psiInf (-sdM (nu t)) = psiInf (sdM (u : Matrix (Fin n) (Fin n) (Cinf E))) *
        ((f (toL (nu (τ t) * Matrix.of x)) : ℂ) * psiInf (-sdM (nu (τ t)))) := fun t => by
    have e1 : Matrix.of (toL ((u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x)) =
        (u : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of x := rfl
    have e2 : -sdM (nu t) = sdM (u : Matrix (Fin n) (Fin n) (Cinf E)) + -sdM (nu (τ t)) := by
      rw [hsd]; abel
    rw [e1, ← Matrix.mul_assoc, ← hτu, e2, psiInf_add]
    ring
  unfold bumpInf
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact hτ.integral_comp' (g := fun s => (f (toL (nu s * Matrix.of x)) : ℂ) * psiInf (-sdM (nu s)))

end GlobalTheory.WhitBump

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem map_apply_bump {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin n) R) (i j : Fin n) :
    (GeneralLinearGroup.map p g : Matrix (Fin n) (Fin n) S) i j = p ((g : Matrix (Fin n) (Fin n) R) i j) := rfl

theorem pInf_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

omit [_root_.NumberField.IsTotallyComplex E] in
theorem pFin_mem_unipB {u : GA E n} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := n)) :
    GeneralLinearGroup.map (pFin E) u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) :=
  (GlobalTheory.SmGL.mem_unipB (Af E)).2 ⟨fun i j h => by rw [map_apply_bump, hu.1 i j h, map_zero],
    fun i => by rw [map_apply_bump, hu.2 i, map_one]⟩

theorem mem_NA_of {y : GL (Fin n) (Cinf E)} {k : GL (Fin n) (Af E)} (hy : y ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n))
    (hk : k ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n)) : infGL E n y * finGL E n k ∈ GlobalTheory.JSW.NA (E := E) (a := n) := by
  have hI : GeneralLinearGroup.map (pInf E) (infGL E n y * finGL E n k) = y := by simp
  have hF : GeneralLinearGroup.map (pFin E) (infGL E n y * finGL E n k) = k := by simp
  obtain ⟨hy1, hy2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hy
  obtain ⟨hk1, hk2⟩ := (GlobalTheory.SmGL.mem_unipB (Af E)).1 hk
  refine ⟨fun i j h => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
  · rw [← map_apply_bump, hI, hy1 i j h, map_zero]
  · rw [← map_apply_bump, hF, hk1 i j h, map_zero]
  · rw [← map_apply_bump, hI, hy2 i, map_one]
  · rw [← map_apply_bump, hF, hk2 i, map_one]

end GlobalTheory.WhitBump


open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in
theorem GlobalTheory.WhitBump.exists_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  intro E _ _ _ m S
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p _ hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dite_eq_left hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolicStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_whittaker_equivariant_bump_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), ∃ b : GA E (m + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1)) := by
  first | exact @GlobalTheory.WhitBump.exists_bump | exact GlobalTheory.WhitBump.exists_bump | (intros; apply GlobalTheory.WhitBump.exists_bump <;> assumption)
end
