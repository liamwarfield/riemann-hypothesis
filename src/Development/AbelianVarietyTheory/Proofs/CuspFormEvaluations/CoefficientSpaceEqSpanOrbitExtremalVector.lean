module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatRoots
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslationSectionsUniversalObject
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesOfFormalChart
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSpan

open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.GradedWeylDivisibility
open scoped Classical Pointwise Matrix

theorem coeff_mem_of_eval_mem {K A : Type} [Field K] [CharZero K] [CommRing A] [Algebra K A] (M : Submodule K A)
    (p : Polynomial A) (h : ∀ c : ℕ, p.eval (c : A) ∈ M) (k : ℕ) : p.coeff k ∈ M := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set q : Polynomial K := ∑ i ∈ Finset.range (p.natDegree + 1), Polynomial.monomial i (φ (p.coeff i)) with hq
  have hq0 : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (s := Set.range (fun c : ℕ => (c : K))) ?_
      (Set.infinite_range_of_injective Nat.cast_injective)
    rintro _ ⟨c, rfl⟩
    have h1 := hφ _ (h c)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hq, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : p.coeff i * (c : A) ^ i = ((c : K) ^ i) • p.coeff i := by
      rw [Algebra.smul_def, map_pow, map_natCast, mul_comm]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have := congrArg (fun r => r.coeff k) hq0
    simp only [hq, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range,
      Polynomial.coeff_zero] at this
    rwa [if_pos (by omega)] at this
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem eval_rowGen {K : Type} [Field K] {r n : ℕ} (a b : Fin r) (c : K) (f : MvPolynomial (Fin r × Fin n) K) :
    (rowGen K a b f).eval (C c) = rowAct K (1 + Matrix.single b a c) f := by
  induction f using MvPolynomial.induction_on with
  | C x => simp [rowGen, rowAct]
  | add f g hf hg => simp only [map_add (f := _), Polynomial.eval_add, hf, hg]
  | mul_X f v hf =>
    simp only [map_mul, Polynomial.eval_mul, hf]
    congr 1
    simp only [rowGen, rowAct, aeval_X, Matrix.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib,
      Polynomial.eval_add, Polynomial.eval_C]
    congr 1
    · rw [Finset.sum_eq_single v.1]
      · simp
      · intro x _ hx
        simp [Matrix.one_apply, Ne.symm hx]
      · simp
    · rw [Finset.sum_eq_single a]
      · by_cases hv : v.1 = b
        · simp only [hv, if_true, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
            Matrix.single_apply_same]
        · simp [hv, Matrix.single, Ne.symm hv]
      · intro x _ hx
        simp [Matrix.single, Ne.symm hx]
      · simp

theorem isUnit_elem {K : Type} [Field K] [CharZero K] {r : ℕ} (a b : Fin r) (c : ℕ) :
    IsUnit (1 + Matrix.single b a (c : K)) := by
  by_cases h : a = b
  · subst h
    have hc : (1 + c : K) ≠ 0 := by exact_mod_cast (by omega : 1 + c ≠ 0)
    refine IsUnit.of_mul_eq_one (1 + Matrix.single a a (-(c : K) / (1 + c))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_same, add_assoc,
      ← Matrix.single_add, ← Matrix.single_add]
    have : -(c : K) / (1 + c) + (c + c * (-(c : K) / (1 + c))) = 0 := by field_simp; ring
    rw [this]; simp
  · refine IsUnit.of_mul_eq_one (1 + Matrix.single b a (-(c : K))) ?_
    rw [add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.single_mul_single_of_ne _ _ _ _ h, add_zero,
      add_assoc, ← Matrix.single_add]
    simp

def trGL {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) : GL (Fin r) K := inside₂ K r g⁻¹

theorem trGL_coe {K : Type} [Field K] {r : ℕ} (g : GL (Fin r) K) :
    (trGL g : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K)ᵀ := by
  simp [trGL, inside₂]

theorem rowDiv_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  unfold rowDiv
  refine coeff_mem_of_eval_mem M _ (fun c => ?_) k
  have h1 := eval_rowGen a b (c : K) f
  rw [map_natCast] at h1
  rw [h1]
  obtain ⟨u, hu⟩ := isUnit_elem (K := K) a b c
  rw [← hu]
  exact hst u f hf

theorem applyWord_mem_of_stable {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K))
    (hst : ∀ u : GL (Fin r) K, ∀ f ∈ M, rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈ M)
    (f : MvPolynomial (Fin r × Fin m) K) (hf : f ∈ M) (w : List (Fin r × Fin r × ℕ)) : applyWord K w f ∈ M := by
  unfold applyWord
  induction w with
  | nil => rw [List.foldr_nil]; exact hf
  | cons x w ih => rw [List.foldr_cons]; exact rowDiv_mem_of_stable M hst _ _ _ _ ih

theorem rowAct_one {K : Type} [Field K] {r m : ℕ} :
    rowAct K (n := m) (1 : Matrix (Fin r) (Fin r) K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, aeval_X, Matrix.one_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem orbit_stable {K : Type} [Field K] {r m : ℕ} (v : MvPolynomial (Fin r × Fin m) K) (u : GL (Fin r) K)
    (f : MvPolynomial (Fin r × Fin m) K)
    (hf : f ∈ Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v)) :
    rowAct K (u : Matrix (Fin r) (Fin r) K) f ∈
      Submodule.span K (Set.range fun g : GL (Fin r) K => rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ v) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    refine Submodule.subset_span ⟨trGL u * g, ?_⟩
    have := DFunLike.congr_fun
      (rowActMul K r m (u : Matrix (Fin r) (Fin r) K) (g : Matrix (Fin r) (Fin r) K)ᵀ) v
    rw [AlgHom.comp_apply] at this
    beta_reduce
    rw [this, Units.val_mul, trGL_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem dualWeyl_le_span_orbit (K : Type) [Field K] [CharZero K] {r m : ℕ} (hm : m ≤ r) (ν : Fin m → ℕ)
    (hν : Antitone ν) :
    dualWeyl K r m ν ≤ Submodule.span K (Set.range fun g : GL (Fin r) K =>
      rowAct K (g : Matrix (Fin r) (Fin r) K)ᵀ (hw K hm ν)) := by
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K hm ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  generalize hw K hm ν = v
  refine applyWord_mem_of_stable _ (orbit_stable v) v (Submodule.subset_span ⟨1, ?_⟩) w
  beta_reduce
  rw [Units.val_one, Matrix.transpose_one, rowAct_one, AlgHom.id_apply]

theorem prod_mem_span_prod {K A ι : Type} [Field K] [CommRing A] [Algebra K A] (s : Finset ι) (S : ι → Set A)
    (x : ι → A) (hx : ∀ i, x i ∈ Submodule.span K (S i)) : ∏ i ∈ s, x i ∈ Submodule.span K (∏ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty => exact Submodule.subset_span (by simp)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← Submodule.span_mul_span]
    exact Submodule.mul_mem_mul (hx a) ih

theorem trAct_ten {K : Type} [Field K] {Ix : Type} [Fintype Ix] {n : ℕ} (g : Ix → GL (Fin n) K)
    (f : Ix → MvPolynomial (Fin n × Fin n) K) :
    trAct g (ten f) = ten fun t => rowAct K (g t : Matrix (Fin n) (Fin n) K)ᵀ (f t) := by
  unfold trAct ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun t _ =>
    (blockActTensor K K Ix n n (fun τ => (g τ : Matrix (Fin n) (Fin n) K)ᵀ)).1 t (f t)

theorem VV_eq_span_orbit (K : Type) [Field K] [CharZero K] (Ix : Type) [Fintype Ix] (n : ℕ)
    (lam : Ix → DomWeight n) :
    VV K lam = Submodule.span K
      (Set.range fun g : Ix → GL (Fin n) K => actP lam g (ten fun t => extremal K n (lam t))) := by
  apply le_antisymm
  · rw [VV, tensorLat, Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    have h1 := prod_mem_span_prod (K := K) Finset.univ
      (fun t => blockEmb K t '' (Set.range fun g : GL (Fin n) K =>
        rowAct K (g : Matrix (Fin n) (Fin n) K)ᵀ (extremal K n (lam t))))
      (fun t => blockEmb K t (F t)) (fun t => by
        have := dualWeyl_le_span_orbit K le_rfl (lam t).natW (Formalism.L2.Col.natW_anti (lam t)) (hF t)
        exact Submodule.apply_mem_span_image_of_mem_span (blockEmb K t).toLinearMap this)
    refine Submodule.span_le.mpr ?_ h1
    intro y hy
    rw [Set.mem_fintype_prod] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    choose w hw hw' using hz
    choose g hg using hw
    have hd : detTwK lam g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun t _ => Units.ne_zero _
    have h2 : ∏ t, z t = (detTwK lam g)⁻¹ • actP lam g (ten fun t => extremal K n (lam t)) := by
      simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_smul, inv_mul_cancel₀ hd, one_smul,
        trAct_ten]
      unfold ten
      exact Finset.prod_congr rfl fun t _ => by rw [← hw', ← hg]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine polyAction_mem_VV lam g (Submodule.subset_span ⟨_, fun t => ?_, rfl⟩)
    exact Formalism.GradedWeylDivisibility.weylLeDual K n n le_rfl _ (Formalism.L2.Col.natW_anti (lam t)) (Submodule.subset_span ⟨[], rfl⟩)

end GlobalTheory.OrbitSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompInj

open ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.Frames
open Formalism.L2.Pj hiding GoodEmb relab perFr
open scoped Matrix ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem dom_nonempty {r : ℕ} (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP0 hP using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP0 τ, fun i => ?_⟩⟩
  apply GlobalTheory.PeriodOnto.lminor_sign
  have h1 : GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (mat (fun τ => P τ) τ) = 1 := by
    change GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (P τ) = 1
    rw [hP, GlobalTheory.PeriodOnto.sgnMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> simp
  rw [h1]
  exact Matrix.PosDef.one

theorem im_eq_of_span {g : ℕ} {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ) (h : ∀ x y, (hermForm A (P x) (P y)).im = (hermForm B (P x) (P y)).im)
    (z z' : Fin g → ℂ) : (hermForm A z z').im = (hermForm B z z').im := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  have hz' : z' ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  unfold hermForm at *
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact h x y
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      simp only [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h1, h2]
    | smul c _ _ h1 =>
      simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h1]
  | zero => simp
  | add _ _ _ _ h1 h2 => simp only [add_dotProduct, Complex.add_im, h1, h2]
  | smul c _ _ h1 => simp only [smul_dotProduct, Complex.smul_im, h1]

theorem not_im_neg (H : Host E) (D : Datum H) {r : ℕ} (hr : 1 ≤ r) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La → (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (ty : Fin g → (E →+* ℂ)) (q : ℕ) (hξ : cc ξ = -ξ) (hG : ∀ a b, cc (Gm a b) = Gm b a)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (x : Frame Ψ r) (hx : x ∈ GG Ψ Gm q) (P : D.La →+ (Fin g → ℂ))
    (hP : ∀ v k, P v k = GlobalTheory.FramePeriod.locPer (idx k).1.1 Gm q (mat x (idx k).1) (Data.emb (idx k).1.1 (φ v))
      (idx k).2) (hper : IsPeriod D ty P) (hneg : ∀ τ ∈ Ψ, (τ ξ).im < 0) : False := by
  classical
  obtain ⟨-, -, -, hspan, Hm, -, hpos, hIm⟩ := hper
  choose Hl hH hp hI using fun τ : Ψ =>
    (GlobalTheory.FramePeriod.exists_loc τ.1 Gm hG q (mat x τ) (hx τ).1 (hx τ).2).2
  have hblk : ∀ v (τ : Ψ), (fun a => P v (idx.symm (τ, a))) =
      GlobalTheory.FramePeriod.locPer τ.1 Gm q (mat x τ) (Data.emb τ.1 (φ v)) := by
    intro v τ
    funext a
    rw [hP, idx.apply_symm_apply]
  have key := im_eq_of_span P hspan Hm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) (by
    intro v w
    rw [GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, hIm]
    have h1 : ((D.EF v w : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * herm Gm (φ v) (φ w)) : ℚ) : ℝ) := by
      rw [← hEF]; simp
    rw [h1, GlobalTheory.FramePeriod.trace_re Ψ hcm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hblk, hblk, Complex.im_ofReal_mul, hI, map_mul, ← hermC_emb]
    have h2 : (τ.1 ξ).re = 0 := by
      have h3 := congrArg Complex.re (emb_cc τ.1 ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
      linarith
    rw [Complex.mul_re, h2]
    ring)
  have hI' : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ),
      (hermForm A (Complex.I • z) z).im = (hermForm A z z).re := by
    intro A z
    simp [hermForm]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
    by_cases h : ComplexEmbedding.conjugate σ ∈ Ψ
    · exact ⟨_, h⟩
    · exact ⟨σ, (hcm σ).2 h⟩
  have hz : (fun _ => 1 : Fin g → ℂ) ≠ 0 := fun h => by
    simpa using congrFun h (idx.symm (⟨τ, hτ⟩, ⟨0, hr⟩))
  have h1 := key (Complex.I • fun _ => 1) (fun _ => 1)
  rw [hI', hI', GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum] at h1
  have h2 := hpos _ hz
  rw [h1] at h2
  refine absurd h2 (not_lt.2 (Finset.sum_nonpos fun t _ => ?_))
  rw [Complex.re_ofReal_mul]
  have h3 := hp t (fun _ => 1) (fun h => by simpa using congrFun h ⟨0, hr⟩)
  have h4 := hneg t.1 t.2
  nlinarith

variable {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_idx {c : Coeff l} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {r g : ℕ} (hr : r = Dw.p + Dw.q)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j, relab c σ (e j).1 =
      if ((idx j).2 : ℕ) < Dw.q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < Dw.q then hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dite_eq_left hn]
      rfl

theorem exists_frame {c : Coeff l} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {r g : ℕ} (h1 : 1 ≤ r)
    (hr : r = Dw.p + Dw.q) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) (D : Datum H) (hp : D.p = Dw.p) (hq : D.q = Dw.q)
    (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (hEF : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (x₀ : Frame X.Ψ r) (hx₀ : x₀ ∈ X.dom) (P₀ : D.La →+ (Fin g → ℂ))
    (hP₀ : ∀ a j, P₀ a j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2)
    (hper₀ : IsPeriod D (fun j => relab c σ (e j).1) P₀) (P : D.La →+ (Fin g → ℂ))
    (hper : IsPeriod D (fun j => relab c σ (e j).1) P) :
    ∃ x ∈ X.dom, ∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2 := by
  obtain ⟨idx, hi, hper'⟩ := exists_idx hσ hr e X hp0 hty
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    rcases X.κ0_xi with h | h
    · intro τ hτ
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
    · exfalso
      refine not_im_neg H D h1 (-X.ξ0) X.Gm (fun a => (φ a : Fin r → E)) X.Ψ X.cmType idx _ Dw.q hξ X.Gm_herm hEF
        x₀ (hp0 ▸ hx₀) P₀ (fun v k => by rw [hP₀, hper']; rfl) hper₀ fun τ hτ => ?_
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_neg, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  have hψ : Set.range ψ = (X.Λ : Set (Fin r → E)) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hy
      exact ⟨φ.symm ⟨y, hy⟩, by simp [ψ]⟩
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm ψ X.Ψ hty g idx _
    (by rw [hq]; exact hi) hξ hpos
    ⟨fun a b hab => φ.injective (Subtype.ext hab), by rw [hψ]; exact X.Λ_span, X.Gm_herm, X.Gm_det, hEF⟩
    (by rw [hp, hq]; exact hr) P hper
  refine ⟨x, by rw [hq, ← hp0] at hx; exact hx, fun a j => ?_⟩
  rw [hper', hPx, hq]
  rfl

theorem frBor_of_eq {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : ∀ τ i, y'.u τ i = y.u τ i) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨g, a, h⟩ := Model.exists_frChg y y' hx
  have ha := Model.FrChg.isUnit h
  refine ⟨fun k => Option.elim k ha.unit (fun _ => 1), (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_,
    fun τ i j hij => Matrix.one_apply_ne hij.ne, hx, fun τ i => ?_, h.2.2⟩⟩
  · exact Matrix.one_apply_eq i
  · rw [hu]
    exact (GlobalTheory.Reg.BorelGroupoid.chg_refl y).2.1 τ i

end GlobalTheory.CompInj

namespace GlobalTheory

open CompInj

theorem card_comp_le_periodSpaces : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  intro _ E _ _ _ H D l Xo c σ r U h1 hσ hU
  obtain ⟨hr, hX, -, hfib, -, g, e, F, ik, φ, hEF, hP⟩ := hU
  refine ⟨g, _, F, (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e, ?_⟩
  suffices hinj : Function.Injective ik by simpa using Fintype.card_le_of_injective ik hinj
  intro k k' hk
  obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2 ψ hEF'
    x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpacesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_familyUnif_isTypeFn_card_comp_le : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  first | exact @GlobalTheory.card_comp_le_periodSpaces | exact GlobalTheory.card_comp_le_periodSpaces | (intros; apply GlobalTheory.card_comp_le_periodSpaces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSections
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_faithfullyFlat_isVtOver :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b) := by
  intro hL E _ _ _ H Dw l Xo c S _ _ y n x
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hpow : ∀ {R : Type} [CommRing R] (x0 : Sp R ⟶ Xo.X) (a : Dw.La), levPt Xo x0 a ^ l.M = 1 := by
    intro R _ x0 a
    rw [levPt, ← MonObj.comp_pow, (moduli_univ_eta_killed hL E H Dw l Xo a).2.2, MonObj.comp_one]
  have hkill : ∀ {R : Type} [CommRing R] (x0 : Sp R ⟶ Xo.X) (a : Dw.La),
      KilledBy Xo l.Mb (levPt Xo x0 a) := by
    intro R _ x0 a b hb
    rw [levPt, Category.assoc, (moduli_univ_eta_killed hL E H Dw l Xo a).1 b hb, MonObj.comp_one]
  obtain ⟨B, _, φ, w, hφ, hw⟩ := GlobalTheory.T.exists_faithfullyFlat_nthRoots_of_torsion hL E H Dw l Xo S y.x l.M l.M hM hM (Fin n)
    (fun b => levPt Xo y.x (x b)) (fun b => hpow _ _)
  letI : Algebra c.F B := (φ.comp (algebraMap c.F S)).toAlgebra
  let ψ : S →ₐ[c.F] B := { φ with commutes' := fun _ => rfl }
  obtain ⟨y', hy'⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S B ψ y
  have hx : spMap φ ≫ y.x = y'.x := hy'.1.symm
  have hroot : ∀ (x0 : Sp B ⟶ Xo.X), spMap φ ≫ y.x = x0 → ∀ b, ∃ v : ptO Xo x0 ⟶ Xo.univ.t.G,
      v ^ l.M = levPt Xo x0 (x b) := by
    rintro _ rfl b
    refine ⟨w b, ?_⟩
    let g : ptO Xo (spMap φ ≫ y.x) ⟶ ptO Xo y.x := Over.homMk (spMap φ) rfl
    have hg : levPt Xo (spMap φ ≫ y.x) (x b) = g ≫ levPt Xo y.x (x b) := by
      rw [levPt, levPt, ← Category.assoc, comp_toUnit]
    rw [hg]
    exact Over.OverMorphism.ext (hw b)
  have hF : ∀ b, ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s
      (levPt Xo y'.x (x b)) F := by
    intro b
    obtain ⟨v, hv⟩ := hroot _ hx b
    obtain ⟨t', ht', hk⟩ := (exists_root_killedBy_pow E H Dw l Xo _ _ v l.M hM (hkill _ _) hv).2 rfl
    refine (GlobalTheory.T.exists_translation_sections_universal_object hL E H Dw l Xo l.M l.odd (ptO Xo y'.x) y'.s).1 _ _ t' ht' ?_ hk
    rw [pow_two, pow_mul, ht', hpow]
  choose F hF using hF
  exact ⟨B, inferInstance, inferInstance, ψ, y', F, hφ, hy', hF⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatCoverLevelSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_cover_level_sections : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La), ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S') (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y'.x))), φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y'.s (levPt Xo y'.x (x b)) (F b) := by
  first | exact @GlobalTheory.exists_faithfullyFlat_isVtOver | exact GlobalTheory.exists_faithfullyFlat_isVtOver | (intros; apply GlobalTheory.exists_faithfullyFlat_isVtOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsNab
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBiextensionChartWithGermsFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBiextensionChartWithGermsFramedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRing

theorem bijective_appTop_powObj (hGF : GlobalFnsSt) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (hG : IsAbelianScheme G) (n : ℕ) :
    Function.Bijective (ReciprocityTheory.ChartRestriction.G.Out.powObj G n).hom.appTop.hom := by
  cases n with
  | zero =>
    show Function.Bijective (𝟙 S : S ⟶ S).appTop.hom
    simp only [Scheme.Hom.id_appTop, CommRingCat.hom_id]
    exact Function.bijective_id
  | succ n => exact hGF _ _ (AbelianSchemeGerms.isAbelianScheme_powObj G hG n)


set_option maxHeartbeats 1600000 in
theorem exists_chartAt_with_germs : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  intro hL E _ _ _ H Dw l Xo c _ hstar S _ _ _ y
  obtain ⟨d, G, A, uvec, x, -, -, hchG⟩ :=
    GlobalTheory.ChartData.exists_isChartG_of_basis E H Xo.X Xo.univ.t S y.x (Lt1 Dw) (fun ℓ => y.u ℓ.1 ℓ.2)
      (fun ℓ => y.tan ℓ.1 ℓ.2) (fun w hw => GlobalTheory.FrameTangent.frame_tangent_basis E H Dw l Xo c S y w hw)
  have hch := (isChart_iff y d G.F A.act uvec x).2 hchG
  obtain ⟨e, wP, ph1, ph2, sy, ad, hfr, hpr, htr, hfa, had, hrig⟩ :=
    GlobalTheory.exists_frames_of_chart E H Xo.X Xo.univ.t S y.x d G A (Lt1 Dw) _ uvec x hchG
  have hPow := bijective_appTop_powObj hL.globalFns Xo.univ.t.G (GlobalTheory.moduli_univ_polAV E H Dw l Xo).2.2.2.1
  obtain ⟨hax, hr⟩ := GlobalTheory.FrameBiextId.fbId E H Xo.X Xo.univ.t hPow hstar S y.x d G A (Lt1 Dw) _ uvec x e
    ph1 ph2 sy ad hchG hfr hfa had
  obtain ⟨h, hh⟩ := GlobalTheory.canonGauge_exists S d (𝓞 E) S (mkFB G A ph1 ph2 sy ad hax hr)
  refine ⟨⟨d, mkFB G A ph1 ph2 sy ad hax hr, uvec, x, e, wP, h, hch,
    (isFrame_iff y d x _ _ _ _ _ _ e).2 hfr, (isPrim_iff wP).2 hpr, hh, hrig⟩, htr, ?_⟩
  intro k F
  obtain ⟨f, hf⟩ := germSt_holds E H Xo.X Xo.univ.t S y.x d G.F A.act (Lt1 Dw) _ uvec x ph1 ph2 sy ad e wP
    hchG hfr hpr htr k F
  exact ⟨f, (isGerm_iff y d x _ e wP k F f).2 hf⟩

end GlobalTheory.ChartRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBiextensionChartWithGermsFramedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biextension_chart_with_germs_framed_point : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S), ∃ C : ChartAt Xo c y, FrTruncC y C ∧ ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))), ∃ f, IsGerm y C.d C.x C.B.A.act C.e C.wP k F f := by
  first | exact @GlobalTheory.ChartRing.exists_chartAt_with_germs | exact GlobalTheory.ChartRing.exists_chartAt_with_germs | (intros; apply GlobalTheory.ChartRing.exists_chartAt_with_germs <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.CanonConn

theorem exists_isNab : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab := by
  intro hL E _ _ _ H Dw l Xo c
  classical
  letI : StarRing (𝓞 E) := H.starRing
  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hC := GlobalTheory.T.exists_biextension_chart_with_germs_framed_point hL E H Dw l Xo c hs
  choose C _hT hg using hC
  choose g hg using hg
  let val : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (k : ℤ),
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)) → (Lt1 Dw →₀ ℕ) → S :=
    fun S _ _ _ y k => match k with
      | Int.ofNat k => fun F α =>
          (C S y).B.nabVal S (C S y).h H.w0 k (g S y k F) (C S y).uvec (MvPolynomial.monomial α 1)
      | Int.negSucc _ => fun _ _ => 0
  let nab : NabV Xo c := fun {S} _ _ y k F α =>
    if h : Nonempty (Algebra ℚ S) then @val S _ _ h.some y k F α else 0
  refine ⟨inferInstance, nab, hs, ?_⟩
  intro S _ _ iQ y
  refine ⟨C S y, fun k F => ⟨_, hg S y k F⟩, ?_⟩
  intro k F f hf α
  have hne : Nonempty (Algebra ℚ S) := ⟨iQ⟩
  have h1 : nab y k F α = @val S _ _ hne.some y k F α := dif_pos hne
  have h2 : hne.some = iQ := Subsingleton.elim _ _
  refine h1.trans ?_
  rw [h2, isGermFun_holds E H Dw l Xo c S y _ _ _ _ _ k F f _ hf (hg S y k F)]

end GlobalTheory.CanonConn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMove
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMove
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShortValMove

open GlobalTheory.TranslMove GlobalTheory.VVRank

section Sections

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left}
  {T : Over S'} {T₀ : Over S} {L₀ : LB G.left} {L₁ : LB A.left}
  {w : LB.Iso L₁ (L₀.pull φ)} {Ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left}

theorem secRel_of_charts (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (h₂ : Ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ)
    (s₀ : LB.Sec (LPow G L₀ 1 T₀)) (s : LB.Sec (LPow A L₁ 1 T))
    (H : ∀ (i : L₀.ι) (j : L₁.ι) (W : (T ⊗ A).left.Opens),
      W = (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) →
      ∀ (h₀ : W ≤ (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)))
      (h₁ : W ≤ Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i)) (h₂ : W ≤ (LPow A L₁ 1 T).U (fun _ => j)),
      (Ψ.appLE ((LPow G L₀ 1 T₀).U (fun _ => i)) W h₁).hom (s₀.f (fun _ => i)) =
        ((snd T A).left.appLE ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) W h₀).hom
          (Units.val (w.s ((fun _ => i), j))) *
        ((T ⊗ A).left.presheaf.map (homOfLE h₂).op).hom (s.f (fun _ => j))) : SecRel w Ψ s₀ s := by
  refine (secRel_iff hL₀ hL₁ h₂ 1 Nat.cast_one.symm s₀ s).2 fun i j W k₀ k₁ k₂ => fn_ext fun x hx => ?_
  have m₁ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      Ψ ⁻¹ᵁ (LPow G L₀ 1 T₀).U (fun _ => i) := fun p hp => Set.mem_iInter.2 fun _ => by
    have h : ((snd T A).left ≫ φ) p ∈ L₀.U i := mem_pull.1 hp.1
    rw [← h₂] at h
    exact h
  have m₂ : (snd T A).left ⁻¹ᵁ ((LB.div (L₀.pull φ) L₁).U ((fun _ => i), j)) ≤
      (LPow A L₁ 1 T).U (fun _ => j) := fun p hp => Set.mem_iInter.2 fun _ => hp.2
  have e := congrArg (gs (𝟙 _) x _) (H i j _ rfl le_rfl m₁ m₂)
  have hx' : (𝟙 (T ⊗ A).left : _ ⟶ _) x ∈ W := hx
  have hx₀ := k₀ hx'
  rw [gs_mul _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀, TranslMove.gs_appLE _ _ _ _ _ _ hx₀,
    gs_res _ _ _ hx₀] at e
  rw [pow_one, gs_mul _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx', TranslMove.gs_appLE _ _ _ _ _ _ hx',
    gs_res _ _ _ hx']
  exact e

end Sections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem sv_pull {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x')}
    (ha : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i),
      (pm.appLE _ _ h).hom (s.f i) = s'.f i)
    {Z : Scheme.{0}} (r : Z ⟶ Gx x') (z : Z) {J} (hJ : Good Xo.univ.t.PP.L z J) :
    sv Xo.univ.t.G s (r ≫ pm) z J = sv Xo.univ.t.G s' r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd (Over.mk x') Xo.univ.t.G).left) r
  refine (sval_of s (r ≫ pm) z J (fun _ => J (r ≫ (snd (Over.mk x') Xo.univ.t.G).left))
    (fun _ => by rw [Category.assoc, hs])).trans ?_
  refine (TranslMove.gs_appLE r pm z _ _ (FramedBaseChange.chart_le pm hs _) hm _).symm.trans ?_
  exact congrArg (gs r z _) (ha _ _)

theorem exists_ptEquiv {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {x x' : Sp S ⟶ Xo.X} (hx : x' = x ≫ ρ) :
    ∃ e : (ptO Xo x ⟶ Xo.univ.t.G) ≃* (ptO Xo x' ⟶ Xo.univ.t.G), ∀ p, (e p).left = p.left ≫ ν.φ := by
  subst hx
  refine ⟨MulEquiv.ofBijective (pushHom ν.cart (ptO Xo x)) ⟨fun p q h => ?_, fun q => ?_⟩, fun p => rfl⟩
  · exact Over.OverMorphism.ext (ν.cart.1.hom_ext (congrArg (fun t => t.left) h)
      ((Over.w p).trans (Over.w q).symm))
  · exact ⟨Over.homMk (ν.cart.1.lift q.left x (Over.w q)) (ν.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (ν.cart.1.lift_fst _ _ _)⟩

theorem exists_move_baseChange {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {ρ : Xo.X ⟶ Xo.X} {ν : SABMap Xo.univ.t Xo.univ.t ρ} {y y' : FrPt Xo c S} (hm : FrMove ρ ν y y')
    {φ : S →ₐ[c.F] T} {z z' : FrPt Xo c T} (h : FrMap φ y z) (h' : FrMap φ y' z') :
    z'.x = z.x ≫ ρ ∧ (∀ τ i, z'.u τ i = z.u τ i ≫ ν.φ) ∧
    ∃ (pm : Gx z.x ⟶ Gx z'.x) (w : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)),
      pm ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left ∧
      pm ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ ∧
      CubIso ν w ∧ SecRel (T := Over.mk z.x) (T₀ := Over.mk z'.x) w pm z'.s z.s := by
  obtain ⟨hx, hu, pm, w, hf, hs, hw, hc⟩ := hm
  obtain ⟨gx, gu, p, ps, pf, pa⟩ := h
  obtain ⟨gx', gu', p', ps', pf', pa'⟩ := h'
  have hL := Xo.univ.t.PP.isLB
  have ex : z'.x = z.x ≫ ρ := by rw [gx', gx, hx, Category.assoc]
  have sq : (fst (Over.mk z.x) Xo.univ.t.G).left ≫ z'.x =
      ((snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom := by
    rw [Category.assoc, ν.cart.1.w, ex, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ ρ) ((Over.w (fst (Over.mk z.x) Xo.univ.t.G)).trans
      (Over.w (snd (Over.mk z.x) Xo.univ.t.G)).symm)
  let q : Gx z.x ⟶ Gx z'.x := pullback.lift (f := z'.x) (g := Xo.univ.t.G.hom) _ _ sq
  have qf : q ≫ (fst (Over.mk z'.x) Xo.univ.t.G).left = (fst (Over.mk z.x) Xo.univ.t.G).left :=
    pullback.lift_fst _ _ _
  have qs : q ≫ (snd (Over.mk z'.x) Xo.univ.t.G).left = (snd (Over.mk z.x) Xo.univ.t.G).left ≫ ν.φ :=
    pullback.lift_snd _ _ _
  have comm : q ≫ p' = p ≫ pm := FramedBaseChange.pulledGroup_hom_ext _ _
    (by rw [Category.assoc, ps', qs, Category.assoc, hs, ← Category.assoc, ps])
    (by rw [Category.assoc, pf', ← Category.assoc, qf, Category.assoc, hf, pf])
  have R := secRel_of_charts (T := Over.mk y.x) (T₀ := Over.mk y'.x) hL hL hs y'.s y.s hc
  refine ⟨ex, fun τ i => by rw [gu', gu, hu, Category.assoc], q, w, qf, qs, hw, fun Z r t J₀ J hJ₀ hJ => ?_⟩
  have a₁ := sv_pull p' ps' pa' (r ≫ q) t hJ₀
  have a₂ := sv_pull p ps pa r t hJ
  have a₃ := R Z (r ≫ p) t J₀ J hJ₀ hJ
  rw [Category.assoc, comm, ← Category.assoc] at a₁
  rw [Category.assoc r p (snd (Over.mk y.x) Xo.univ.t.G).left, ps] at a₃
  exact a₁.symm.trans (a₃.trans (congrArg _ a₂))

theorem eta_congr {a b : Dw.La}
    (h : (Submodule.Quotient.mk a : LevQ Dw l) = Submodule.Quotient.mk b) : Xo.univ.eta a = Xo.univ.eta b := by
  have h2 := Xo.univ.eta_add (a - b) b
  rwa [sub_add_cancel, Xo.univ.eta_ker _ ((Submodule.Quotient.eq _).1 h), _root_.one_mul] at h2

theorem mk_levRep (q : LevQ Dw l) : (Submodule.Quotient.mk (levRep q) : LevQ Dw l) = q :=
  Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)

theorem shortValAt_move : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c S), IsLevMove ρ ν gM gA → FrMove ρ ν y y' → ∀ σq : LevQ Dw l ≃ LevQ Dw l, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (gM a)) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y' v → ShortValAt Xo c nab (fun q => w (fun b => σq.symm (q b))) Λ β N P y v := by
  intro hLaw hCI E _ _ _ H Dw l Xo c _ nab hnab S _ _ ρ ν gM gA y y' hlev hmv σq hσ n a P hP w Λ β N v hv
  obtain ⟨S', _, _, φ, y₁', z', tp', F', hff, hfr, hZ, hG, htp, hUU, hval⟩ := hv
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.FramedBaseChange.exists_frMap hLaw E H Dw l Xo c S S' φ y
  obtain ⟨hx, hu, pm, ω, hf, hs, hω, hR⟩ := exists_move_baseChange hmv hy₁ hfr
  have hL := Xo.univ.t.PP.isLB
  obtain ⟨e, he⟩ := exists_ptEquiv ν hx
  have he' : ∀ p, p.left = (e.symm p).left ≫ ν.φ := fun p => by rw [← he, e.apply_symm_apply]
  have hact : ∀ p b, e (p ≫ Xo.univ.t.act.act b) = e p ≫ Xo.univ.t.act.act b := fun p b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, ν.act])
  have hact' : ∀ p b, e.symm p ≫ Xo.univ.t.act.act b = e.symm (p ≫ Xo.univ.t.act.act b) := fun p b =>
    e.injective (by rw [hact, e.apply_symm_apply, e.apply_symm_apply])
  have hlv : ∀ q : LevQ Dw l, e (levPt Xo y₁.x (levRep q)) = levPt Xo y₁'.x (levRep (σq.symm q)) := fun q => by
    have h1 : Xo.univ.eta (levRep q) = Xo.univ.eta (gM (levRep (σq.symm q))) :=
      eta_congr (by rw [← hσ, mk_levRep, mk_levRep, σq.apply_symm_apply])
    refine Over.OverMorphism.ext ?_
    rw [he, levPt, levPt, h1, Over.comp_left, Over.comp_left, Category.assoc, hlev.2.1, Over.toUnit_left,
      Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hx.symm)
  choose F hF hFF using fun (q : Fin n → LevQ Dw l) i b =>
    isUUOver_move hLaw E H Dw l Xo c S' ρ ν y₁ y₁' pm ω hx hf hs hω
      ((secRel_iff hL hL hs 1 Nat.cast_one.symm y₁'.s y₁.s).1 hR) N (e.symm (z' i b))
      (e.symm (tp' (fun b => σq.symm (q b)) b)) (z' i b) (tp' (fun b => σq.symm (q b)) b) (he' _) (he' _)
      (F' (fun b => σq.symm (q b)) i b) (hUU _ i b)
  refine ⟨S', inferInstance, inferInstance, φ, y₁, fun i b => e.symm (z' i b),
    fun q b => e.symm (tp' (fun b => σq.symm (q b)) b), F, hff, hy₁, fun i => ⟨fun b => ?_, ?_⟩, ?_,
    fun q b => ⟨?_, ?_⟩, hF, ?_⟩
  · rw [← map_pow, (hZ i).1 b, map_one]
  · intro mu hmu cm hcm k
    have h := congrArg e.symm ((hZ i).2 mu hmu cm hcm k)
    rw [map_list_prod, List.map_ofFn, map_one] at h
    simp only [hact']
    exact h
  · intro k _ ψ g hg i j hij
    refine hG k ψ (Over.homMk (spMap ψ) rfl) rfl (funext fun b => Over.OverMorphism.ext ?_)
    have h := congrArg (fun t => t.left ≫ ν.φ) (congrFun hij b)
    simp only [Over.comp_left, hg, Category.assoc, ← he'] at h
    exact h
  · rw [← map_pow, (htp _ b).1, ← hlv, e.symm_apply_apply]
  · obtain ⟨j, hj⟩ := (htp (fun b => σq.symm (q b)) b).2
    exact ⟨j, fun t ht => by rw [hact', hj t ht, map_one]⟩
  · rw [hval]
    congr 1
    refine (finsum_comp_equiv (Equiv.piCongrRight fun _ : Fin n => σq.symm)).symm.trans
      (finsum_congr fun q => ?_)
    refine congrArg₂ (· * ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
    exact GlobalTheory.T.harmonic_values_invariant_universal_endomorphism hLaw hCI E H Dw l Xo c nab hnab S' ρ ν y₁ y₁' pm ω hx hf hs hω hu n a P hP N
      (F q i) (F' (fun b => σq.symm (q b)) i) (hFF q i)

end GlobalTheory.ShortValMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortThetaValueUnderLevelMoveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortThetaValue_under_levelMove : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c S), IsLevMove ρ ν gM gA → FrMove ρ ν y y' → ∀ σq : LevQ Dw l ≃ LevQ Dw l, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (gM a)) → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F) (N : ℕ) (v : S), ShortValAt Xo c nab w Λ β N P y' v → ShortValAt Xo c nab (fun q => w (fun b => σq.symm (q b))) Λ β N P y v := by
  first | exact @GlobalTheory.ShortValMove.shortValAt_move | exact GlobalTheory.ShortValMove.shortValAt_move | (intros; apply GlobalTheory.ShortValMove.shortValAt_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnesses
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnesses
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_pull (hC : ChartIndepSt2) [StarRing (𝓞 E)] (nab : NabV Xo c) (hnab : IsNab Xo c nab)
    {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) (z : FrPt Xo c T) (hm : FrMap ψ y z) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y.x)))
    (hF : ∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y.s (levPt Xo y.x (x b)) (F b)) :
    ∃ F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo z.x)),
      (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) z.s (levPt Xo z.x (x b)) (F' b)) ∧
      ψ (thExpr Xo c nab y P F) = thExpr Xo c nab z P F' := by
  obtain ⟨hx, -⟩ := id hm
  let h : ptO Xo z.x ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) hx.symm
  have hh : h.left = spMap ψ.toRingHom := rfl
  have hs := GlobalTheory.FramedBaseChange.isPullSec ψ hm h hh
  have hH : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    unfold harmA HaO at hP
    exact hP.1
  choose F' hF' using fun b => Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L
    ((l.M : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b)
  refine ⟨F', fun b => ?_, ?_⟩
  · have hv := (GlobalTheory.VtBaseChange.isVtOver_isUUOver_baseChange E H Dw l Xo l.M (l.Mb ^ 2) (ptO Xo y.x)
      (ptO Xo z.x) h y.s z.s hs (F b) (F' b) (hF' b)).1 _ (hF b)
    have e : h ≫ levPt Xo y.x (x b) = levPt Xo z.x (x b) := by
      unfold levPt
      rw [← Category.assoc]
      congr 1
      exact CartesianMonoidalCategory.toUnit_unique _ _
    rwa [e] at hv
  · have hv := GlobalTheory.T.harmonicValue_baseChange_alt hC E H Dw l Xo c nab hnab S T ψ y z hm h hh a n P hH l.M F F' hF'
    unfold thExpr
    rw [map_mul, AlgHom.commutes, hv]

theorem thExpr_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s (levPt Xo y1.x (x b)) (F1 b)) → FrMap φ2 y y2 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s (levPt Xo y2.x (x b)) (F2 b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ψ1 (thExpr Xo c nab y1 P F1) = ψ2 (thExpr Xo c nab y2 P F2) := by
  intro hL hC E _ _ _ H Dw l Xo c _ nab hnab S _ _ y a n x P hP S1 _ _ φ1 y1 F1 S2 _ _ φ2 y2 F2 hm1 hF1 hm2 hF2 T _ _ ψ1 ψ2 hψ
  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algHom hL E H Dw l Xo c S T (ψ1.comp φ1) y
  have hw1 : FrMap ψ1 y1 w := GlobalTheory.FramedBaseChange.cancel φ1 ψ1 hm1 hw
  have hw2 : FrMap ψ2 y2 w := GlobalTheory.FramedBaseChange.cancel φ2 ψ2 hm2 (hψ ▸ hw)
  obtain ⟨G1, hG1, e1⟩ := exists_pull hC nab hnab ψ1 y1 w hw1 a n x P hP F1 hF1
  obtain ⟨G2, hG2, e2⟩ := exists_pull hC nab hnab ψ2 y2 w hw2 a n x P hP F2 hF2
  rw [e1, e2]
  have hG : G1 = G2 := funext fun b => vtUniq_obj hL.globalFns Xo.univ (hG1 b) (hG2 b)
  rw [hG]

end GlobalTheory.ThetaCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaExpressionEqOfWitnessesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpression_eq_of_witnesses : Laws → ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ (S1 : Type) [CommRing S1] [Algebra c.F S1] (φ1 : S →ₐ[c.F] S1) (y1 : FrPt Xo c S1) (F1 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y1.x))) (S2 : Type) [CommRing S2] [Algebra c.F S2] (φ2 : S →ₐ[c.F] S2) (y2 : FrPt Xo c S2) (F2 : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((l.M : ℤ) ^ 2) (ptO Xo y2.x))), FrMap φ1 y y1 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y1.s (levPt Xo y1.x (x b)) (F1 b)) → FrMap φ2 y y2 → (∀ b, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) y2.s (levPt Xo y2.x (x b)) (F2 b)) → ∀ (T : Type) [CommRing T] [Algebra c.F T] (ψ1 : S1 →ₐ[c.F] T) (ψ2 : S2 →ₐ[c.F] T), ψ1.comp φ1 = ψ2.comp φ2 → ψ1 (thExpr Xo c nab y1 P F1) = ψ2 (thExpr Xo c nab y2 P F2) := by
  first | exact @GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses | exact GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses | (intros; apply GlobalTheory.ThetaCompare.thExpr_eq_of_witnesses <;> assumption)
end
end
