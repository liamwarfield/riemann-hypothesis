module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.GramSchmidtEigenframe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowerBlockMatrices
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientPositivity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.FdFjNearSupOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermLinApply
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoNormRelationTamePrime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.DotAddRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentSubOneMajorantBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxPointFrameOfTransference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.FdFjNearSup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.FdPointAssembly
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.FdUnipMove
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantBoundOrthogonalPart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NoShortVectorLowerBoundHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalShortVectorBoundOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SchwarzLemmaBallHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ShortVectorBound

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FundamentalDomainD5
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ThetaDotSelf
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.HQsmulRight
section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.RhoDotSelf
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix ComplexConjugate

variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)

def rho (w : ι → Fin r → ℂ) : Fin N → ℝ := fun k =>
  if (eqv k).2.2 = 0 then (w (eqv k).1 (eqv k).2.1).re else (w (eqv k).1 (eqv k).2.1).im

theorem rho_add (w w' : ι → Fin r → ℂ) : rho eqv (w + w') = rho eqv w + rho eqv w' := by
  funext k
  simp only [rho, Pi.add_apply]
  split_ifs <;> simp

theorem rho_sub (w w' : ι → Fin r → ℂ) : rho eqv (w - w') = rho eqv w - rho eqv w' := by
  funext k
  simp only [rho, Pi.sub_apply]
  split_ifs <;> simp

theorem rho_smul (c : ℝ) (w : ι → Fin r → ℂ) : rho eqv ((c : ℂ) • w) = c • rho eqv w := by
  funext k
  simp only [rho, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem rho_zero : rho eqv (0 : ι → Fin r → ℂ) = 0 := by
  funext k
  simp [rho]

theorem rho_sum {κ : Type} (s : Finset κ) (w : κ → ι → Fin r → ℂ) :
    rho eqv (∑ j ∈ s, w j) = ∑ j ∈ s, rho eqv (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rho_add, ih]

theorem rho_dot (w w' : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w' = ∑ i, ∑ a, (conj (w i a) * w' i a).re := by
  unfold dotProduct
  rw [← eqv.symm.sum_comp]
  simp only [rho, Equiv.apply_symm_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [Complex.mul_re]

theorem rho_dot_self (w : ι → Fin r → ℂ) : rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ a, ‖w i a‖ ^ 2 := by
  rw [rho_dot]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

def Phi (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → K) : ι → Fin r → ℂ :=
  fun i => Q i *ᵥ embVec (σ i) v

def Theta (p : ℕ) (w : ι → Fin r → ℂ) : ι → Fin r → ℂ := fun i a => sgn p a * w i a

theorem sgn_conj (p : ℕ) (a : Fin r) : conj (sgn p a) = sgn p a := by
  unfold sgn
  split_ifs <;> simp

theorem embVec_add (τ : K →+* ℂ) (x y : Fin r → K) : embVec τ (x + y) = embVec τ x + embVec τ y := by
  ext a
  simp [embVec]

theorem embVec_smul (τ : K →+* ℂ) (c : K) (x : Fin r → K) : embVec τ (c • x) = τ c • embVec τ x := by
  ext a
  simp [embVec]

theorem embVec_qsmul (τ : K →+* ℂ) (q : ℚ) (x : Fin r → K) : embVec τ (q • x) = (q : ℂ) • embVec τ x := by
  ext a
  simp [embVec, Rat.smul_def, map_ratCast]

theorem Phi_add (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (x y : Fin r → K) :
    Phi σ Q (x + y) = Phi σ Q x + Phi σ Q y := by
  ext i a
  simp [Phi, embVec_add, Matrix.mulVec_add]

theorem Phi_qsmul (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (q : ℚ) (x : Fin r → K) :
    Phi σ Q (q • x) = ((q : ℝ) : ℂ) • Phi σ Q x := by
  ext i a
  simp [Phi, embVec_qsmul, Matrix.mulVec_smul, Complex.ofReal_ratCast]

theorem Phi_sum (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {κ : Type} (s : Finset κ)
    (x : κ → Fin r → K) : Phi σ Q (∑ j ∈ s, x j) = ∑ j ∈ s, Phi σ Q (x j) := by
  exact map_sum (AddMonoidHom.mk' (Phi σ Q) (Phi_add σ Q)) x s

section Herm

variable (S : HermForm K r)

theorem h_add_left (x x' y : Fin r → K) : S.h (x + x') y = S.h x y + S.h x' y := by
  simp only [HermForm.h, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem h_add_right (x y y' : Fin r → K) : S.h x (y + y') = S.h x y + S.h x y' := by
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem h_smul_left (c : K) (x y : Fin r → K) : S.h (c • x) y = S.c c * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem h_smul_right (c : K) (x y : Fin r → K) : S.h x (c • y) = c * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem h_qsmul_left (q : ℚ) (x y : Fin r → K) : S.h (q • x) y = (q : K) * S.h x y := by
  have hq : q • x = (q : K) • x := by ext a; simp [Rat.smul_def]
  rw [hq, h_smul_left, map_ratCast]

theorem h_qsmul_right (q : ℚ) (x y : Fin r → K) : S.h x (q • y) = (q : K) * S.h x y := by
  have hq : q • y = (q : K) • y := by ext a; simp [Rat.smul_def]
  rw [hq, h_smul_right]

theorem h_sum_left {κ : Type} (s : Finset κ) (x : κ → Fin r → K) (y : Fin r → K) :
    S.h (∑ j ∈ s, x j) y = ∑ j ∈ s, S.h (x j) y := by
  exact map_sum (AddMonoidHom.mk' (fun x => S.h x y) (fun a b => h_add_left S a b y)) x s

theorem h_sum_right {κ : Type} (s : Finset κ) (x : Fin r → K) (y : κ → Fin r → K) :
    S.h x (∑ j ∈ s, y j) = ∑ j ∈ s, S.h x (y j) := by
  exact map_sum (AddMonoidHom.mk' (fun y => S.h x y) (fun a b => h_add_right S x a b)) y s

end Herm

end Formalism.L2.Pj.FundamentalDomainD5
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinrankCmType
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix
open scoped ComplexConjugate

lemma conj_conj_emb {K : Type} [Field K] (φ : K →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
  star_star φ

def cmEquiv {K : Type} [Field K] {ι : Type} (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    ι ⊕ ι ≃ (K →+* ℂ) :=
  Equiv.ofBijective (Sum.elim σ fun i => ComplexEmbedding.conjugate (σ i)) (by
    constructor
    · rintro (i | i) (j | j) h
      · exact congrArg Sum.inl (hinj h)
      · exfalso
        have h1 : ∃ i', σ i' = σ i := ⟨i, rfl⟩
        exact (hcm (σ i)).1 h1 ⟨j, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [this, conj_conj_emb]⟩
      · exfalso
        have h1 : ∃ i', σ i' = σ j := ⟨j, rfl⟩
        exact (hcm (σ j)).1 h1 ⟨i, by
          have := congrArg ComplexEmbedding.conjugate h
          simp only [Sum.elim_inl, Sum.elim_inr] at this
          rw [← this, conj_conj_emb]⟩
      · have := congrArg ComplexEmbedding.conjugate h
        simp only [Sum.elim_inr, conj_conj_emb] at this
        exact congrArg Sum.inr (hinj this)
    · intro τ
      by_cases h : ∃ i, σ i = τ
      · obtain ⟨i, hi⟩ := h
        exact ⟨Sum.inl i, hi⟩
      · have h2 : ∃ i, σ i = ComplexEmbedding.conjugate τ := by
          by_contra h3
          exact h ((hcm τ).2 h3)
        obtain ⟨i, hi⟩ := h2
        refine ⟨Sum.inr i, ?_⟩
        simp only [Sum.elim_inr, hi, conj_conj_emb])

theorem sum_re_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (z : K) :
    ∑ i, (σ i z).re = (1 / 2 : ℝ) * ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
  have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ K z) = ∑ τ : K →+* ℂ, τ z := by
    rw [trace_eq_sum_embeddings ℂ (x := z)]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ (fun _ => rfl)
  have h2 : ∑ τ : K →+* ℂ, τ z = ∑ i, σ i z + ∑ i, conj (σ i z) := by
    rw [← Equiv.sum_comp (cmEquiv σ hinj hcm), Fintype.sum_sum_type]
    rfl
  have h3 := congrArg Complex.re (h1.trans h2)
  simp only [Complex.add_re, Complex.re_sum, Complex.conj_re] at h3
  have h4 : ((algebraMap ℚ ℂ) (Algebra.trace ℚ K z)).re = ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
    simp
  rw [h4] at h3
  linarith

theorem finrank_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Module.finrank ℚ K = 2 * Fintype.card ι := by
  rw [← NumberField.Embeddings.card K ℂ, ← Fintype.card_congr (cmEquiv σ hinj hcm), Fintype.card_sum]
  ring

end Formalism.L2.Pj.FundamentalDomainD5
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

theorem trace_id (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ)
    (Q : ι → Matrix (Fin r) (Fin r) ℂ) (p : ℕ) (S : HermForm K r)
    (hform : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (y v : Fin r → K) :
    rho eqv (Theta p (Phi σ Q y)) ⬝ᵥ rho eqv (Phi σ Q v) =
      (1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h y v) : ℚ) : ℝ) := by
  rw [rho_dot, ← sum_re_cmType σ hinj hcm (S.h y v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hform i y v, jForm, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Theta, Phi, map_mul, sgn_conj]
  ring_nf

private lemma rho_dot_self_lemma {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv w ⬝ᵥ rho eqv w = ∑ i, ∑ j, Complex.normSq (w i j) := by
  unfold rho
  simp only [dotProduct]
  refine (Equiv.sum_comp eqv (fun x : ι × Fin r × Fin 2 =>
    (if x.2.2 = 0 then (w x.1 x.2.1).re else (w x.1 x.2.1).im) *
      (if x.2.2 = 0 then (w x.1 x.2.1).re else (w x.1 x.2.1).im))).trans ?_
  simp [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]

theorem theta_dot_self (p : ℕ) {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (w : ι → Fin r → ℂ) :
    rho eqv (Theta p w) ⬝ᵥ rho eqv (Theta p w) = rho eqv w ⬝ᵥ rho eqv w := by
  rw [rho_dot_self_lemma, rho_dot_self_lemma]
  unfold Theta sgn
  simp only [map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem phi_dot_self (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) {N : ℕ}
    (eqv : Fin N ≃ ι × Fin r × Fin 2) (v : Fin r → K) :
    rho eqv (Phi σ Q v) ⬝ᵥ rho eqv (Phi σ Q v) = majSq σ Q v := by
  rw [rho_dot_self_lemma]
  unfold Phi majSq normSq
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact Complex.normSq_eq_norm_sq _

theorem trace_one_ne : Algebra.trace ℚ K 1 ≠ 0 := by
  rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap]
  simp only [nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero]
  exact Module.finrank_pos.ne'

theorem nondeg [Nonempty ι] (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (hQ : ∀ i, (Q i).det ≠ 0) (p : ℕ) (S : HermForm K r)
    (hform : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    (x : Fin r → K) (h : ∀ v, Algebra.trace ℚ K (S.h v x) = 0) : x = 0 := by
  classical
  unfold jForm embVec at hform
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsingle : ∀ (j : Fin r) (b : K),
      (fun a => σ i₀ ((Pi.single j b : Fin r → K) a)) = (Pi.single j (σ i₀ b) : Fin r → ℂ) := by
    intro j b
    funext a
    by_cases ha : a = j
    · subst ha
      simp
    · simp [Pi.single_eq_of_ne ha]
  have hcol : ∀ (j : Fin r) (z : ℂ) (k : Fin r), (Q i₀ *ᵥ (Pi.single j z : Fin r → ℂ)) k = Q i₀ k j * z := by
    intro j z k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hg : ∀ j : Fin r, S.h (Pi.single j 1) x = 0 := by
    intro j
    have hlin : ∀ b : K, S.h (Pi.single j b) x = S.1 b * S.h (Pi.single j 1) x := by
      intro b
      apply (σ i₀).injective
      rw [map_mul, hform, hform, hsingle, hsingle, S.3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hcol, hcol, map_one]
      simp only [map_mul, map_one]
      ring
    by_contra hg0
    have ht := h (Pi.single j (S.1 (S.h (Pi.single j 1) x)⁻¹))
    have ht2 := hlin (S.1 (S.h (Pi.single j 1) x)⁻¹)
    rw [ht2, S.2, inv_mul_cancel₀ hg0] at ht
    exact trace_one_ne ht
  have hw : (Q i₀)ᴴ *ᵥ (fun k => sgn p k * (Q i₀ *ᵥ fun a => σ i₀ (x a)) k) = 0 := by
    funext j
    have h0 := congrArg (σ i₀) (hg j)
    rw [hform, hsingle, map_zero] at h0
    show ∑ k, (Q i₀)ᴴ j k * (sgn p k * (Q i₀ *ᵥ fun a => σ i₀ (x a)) k) = 0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcol, map_one, mul_one, Matrix.conjTranspose_apply, starRingEnd_apply]
    ring
  have hdet : ((Q i₀)ᴴ).det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr (hQ i₀)
  have hw0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hw
  have hu0 : (Q i₀ *ᵥ fun a => σ i₀ (x a)) = 0 := by
    funext k
    have hk := congrFun hw0 k
    simp only [Pi.zero_apply] at hk ⊢
    rcases mul_eq_zero.mp hk with hk | hk
    · unfold sgn at hk
      split_ifs at hk <;> norm_num at hk
    · exact hk
  have hx0 := Matrix.eq_zero_of_mulVec_eq_zero (hQ i₀) hu0
  funext a
  have ha := congrFun hx0 a
  simp only [Pi.zero_apply] at ha ⊢
  exact (σ i₀).injective (by rw [ha, map_zero])

end Formalism.L2.Pj.FundamentalDomainD5
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DiscrMulIntegral
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

theorem discr_mul_integral {K : Type} [Field K] [NumberField K] (z : K)
    (hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (z * a) = n) :
    IsIntegral ℤ ((NumberField.discr K : K) * z) := by
  classical
  have hne : (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))

  have hz1 : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
      rw [← FractionalIdeal.coeIdeal_top]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨n, hn⟩ := hz a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply]
    simpa using hn.symm

  set N : ℕ := Ideal.absNorm (differentIdeal ℤ (𝓞 K)) with hN
  have hNmem : (N : K) ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨(N : 𝓞 K), Ideal.absNorm_mem _, by simp⟩
  have hprod : z * (N : K) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h := FractionalIdeal.mul_mem_mul hz1 hNmem
    have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
        (differentIdeal ℤ (𝓞 K) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ := by
      rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
    rwa [hdual, inv_mul_cancel₀ hne] at h
  obtain ⟨x, hx⟩ := (FractionalIdeal.mem_one_iff _).mp hprod
  have hint : IsIntegral ℤ (z * (N : K)) := by
    rw [← hx]; exact RingOfIntegers.isIntegral_coe x
  have hNd : N = (NumberField.discr K).natAbs := NumberField.absNorm_differentIdeal K (𝓞 K)
  rcases Int.natAbs_eq (NumberField.discr K) with h | h
  · rw [h, ← hNd, Int.cast_natCast, mul_comm]; exact hint
  · rw [h, ← hNd, Int.cast_neg, Int.cast_natCast, neg_mul, mul_comm]; exact hint.neg

end Formalism.L2.Pj.FundamentalDomainD5
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DotSelfEqSqNorm
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open Matrix

theorem dot_self_eq_sq_norm {N : ℕ} (v : Fin N → ℝ) :
    v ⬝ᵥ v = ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [dotProduct, sq]

theorem cover_round {N : ℕ} (b : Fin N → Fin N → ℝ) (hb : LinearIndependent ℝ b) (ℓ : ℝ)
    (hℓ : ∀ j, b j ⬝ᵥ b j ≤ ℓ ^ 2) (w : Fin N → ℝ) :
    ∃ n : Fin N → ℤ, (w - ∑ j, (n j : ℝ) • b j) ⬝ᵥ (w - ∑ j, (n j : ℝ) • b j) ≤ ((N : ℝ) * ℓ / 2) ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by simp [dotProduct]⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hcard : Fintype.card (Fin N) = Module.finrank ℝ (Fin N → ℝ) := by simp
  let B := basisOfLinearIndependentOfCardEqFinrank hb hcard
  have hB : ∀ j, B j = b j := fun j => by simp [B]
  set c := B.repr w with hcdef
  refine ⟨fun j => round (c j), ?_⟩
  have hw : w = ∑ j, c j • b j := by
    conv_lhs => rw [← B.sum_repr w]
    simp only [hB, hcdef]

  have hdiff : w - ∑ j, ((round (c j) : ℤ) : ℝ) • b j = ∑ j, (c j - round (c j)) • b j := by
    conv_lhs => rw [hw]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sub_smul]
  have hbj : ∀ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ ≤ |ℓ| := by
    intro j
    have h := hℓ j
    rw [dot_self_eq_sq_norm, ← sq_abs ℓ] at h
    by_contra hc
    push_neg at hc
    nlinarith [abs_nonneg ℓ]
  have hnorm : ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ≤
      (N : ℝ) * |ℓ| / 2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    calc ‖∑ j, (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖
        ≤ ∑ j, ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm ((c j - round (c j)) • b j)‖ :=
          norm_sum_le _ _
      _ = ∑ j, |c j - round (c j)| * ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (b j)‖ := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [LinearEquiv.map_smul, norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ _j : Fin N, (1 / 2) * |ℓ| :=
          Finset.sum_le_sum (fun j _ =>
            mul_le_mul (abs_sub_round _) (hbj j) (norm_nonneg _) (by norm_num))
      _ = (N : ℝ) * |ℓ| / 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  rw [hdiff, dot_self_eq_sq_norm]
  calc ‖(WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm (∑ j, (c j - round (c j)) • b j)‖ ^ 2
      ≤ ((N : ℝ) * |ℓ| / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = ((N : ℝ) * ℓ / 2) ^ 2 := by
      rw [div_pow, mul_pow, sq_abs, ← mul_pow, ← div_pow]

end Formalism.L2.Pj.FundamentalDomainD5
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ExistsBasisIn
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

theorem exists_basis_in {K : Type} [Field K] {r : ℕ} (S : Set (Fin r → K))
    (hS : Submodule.span K S = ⊤) :
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ S) ∧ LinearIndependent K v := by
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent K S
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin r → K)) := by
    rw [Subtype.range_coe, hspan, hS]
  let B := Module.Basis.mk hli htop
  let e := B.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨fun j => (e.symm j : Fin r → K), fun j => hbS (e.symm j).2, ?_⟩
  exact hli.comp e.symm e.symm.injective

end Formalism.L2.Pj.FundamentalDomainD5
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.LatticeZbasis
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix

theorem lattice_zbasis {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hfg : L.FG) (hspan : Submodule.span K (L : Set (Fin r → K)) = ⊤) :
    ∃ e : Fin (Module.finrank ℚ K * r) → (Fin r → K), (∀ j, e j ∈ L) ∧ LinearIndependent ℚ e ∧
      ∀ v ∈ L, ∃ n : Fin (Module.finrank ℚ K * r) → ℤ, v = ∑ j, (n j : ℚ) • e j := by
  classical
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 K) L
  haveI : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  set b := Module.Free.chooseBasis ℤ L
  set f : Module.Free.ChooseBasisIndex ℤ L → (Fin r → K) := fun j => (b j : Fin r → K) with hf
  have hfZ : LinearIndependent ℤ f :=
    b.linearIndependent.map' (L.subtype.restrictScalars ℤ) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hfQ : LinearIndependent ℚ f := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hfZ
  have hrep : ∀ v ∈ L, ∃ c : Module.Free.ChooseBasisIndex ℤ L → ℤ, v = ∑ j, (c j : ℚ) • f j := by
    intro v hv
    refine ⟨fun j => b.repr ⟨v, hv⟩ j, ?_⟩
    have h' := congrArg (fun z : L => (z : Fin r → K)) (b.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h'
    conv_lhs => rw [← h']
    exact Finset.sum_congr rfl fun j _ => (Int.cast_smul_eq_zsmul ℚ _ _).symm
  have hS : ∀ v ∈ L, v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv
    obtain ⟨c, hc⟩ := hrep v hv
    rw [hc]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hKL : ∀ v ∈ L, ∀ k : K, k • v ∈ Submodule.span ℚ (Set.range f) := by
    intro v hv k
    have halg : IsAlgebraic ℤ k :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hyi⟩ := halg.exists_integral_multiple
    have hmem : ((⟨y • k, hyi⟩ : 𝓞 K)) • v ∈ L := L.smul_mem _ hv
    have hyK : (y : K) ≠ 0 := by exact_mod_cast hy0
    have heq : k • v = ((y : ℚ)⁻¹) • ((⟨y • k, hyi⟩ : 𝓞 K) • v) := by
      rw [algebra_compatible_smul K ((y : ℚ)⁻¹), algebra_compatible_smul K (⟨y • k, hyi⟩ : 𝓞 K), smul_smul]
      congr 1
      simp only [map_inv₀, map_intCast, zsmul_eq_mul]
      show k = (y : K)⁻¹ * ((y : K) * k)
      field_simp
    rw [heq]
    exact Submodule.smul_mem _ _ (hS _ hmem)
  have htop : ⊤ ≤ Submodule.span ℚ (Set.range f) := by
    intro x _
    have hx : x ∈ Submodule.span K (L : Set (Fin r → K)) := hspan ▸ Submodule.mem_top
    have key : ∀ z ∈ Submodule.span K (L : Set (Fin r → K)), ∀ k : K, k • z ∈ Submodule.span ℚ (Set.range f) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem v hv => exact hKL v hv
      | zero => intro k; rw [smul_zero]; exact Submodule.zero_mem _
      | add a c _ _ ha hc => intro k; rw [smul_add]; exact Submodule.add_mem _ (ha k) (hc k)
      | smul c a _ ha => intro k; rw [smul_smul]; exact ha (k * c)
    simpa using key x hx 1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℚ K * r := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.mk hfQ htop), Module.finrank_pi_fintype]
    simp [mul_comm]
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, fun j => (b (eqv.symm j)).2, hfQ.comp _ eqv.symm.injective, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := hrep v hv
  refine ⟨c ∘ eqv.symm, ?_⟩
  rw [hc]
  exact (Fintype.sum_equiv eqv.symm _ _ (fun j => rfl)).symm

end Formalism.L2.Pj.FundamentalDomainD5
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

theorem d5_translation : ReciprocityTheory.ChartRestriction.G.FD.CoveringRadiusStatement := by
  intro K _ _ _ ι _ _ r p S σ Q L laStar hinj hcm hp hla hQ hform hL hSD hmin
  intro μ
  classical
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    refine ⟨fun w => ⟨0, L.zero_mem, ?_⟩, fun j => j.elim0, fun j => j.elim0,
      linearIndependent_empty_type, fun j => j.elim0⟩
    simp [normSq]
    positivity
  set f := Fintype.card ι with hf
  have hdeg : Module.finrank ℚ K = 2 * f := finrank_cmType σ hinj hcm
  set N := Module.finrank ℚ K * r with hN
  have hNpos : 0 < N := Nat.mul_pos Module.finrank_pos hr0
  obtain ⟨e, heL, heli, hecoord⟩ := lattice_zbasis L hL.1 hL.2
  have hcardN : Fintype.card (ι × Fin r × Fin 2) = N := by
    simp only [Fintype.card_prod, Fintype.card_fin, hN, hdeg, hf]
    ring
  let eqv : Fin N ≃ ι × Fin r × Fin 2 := (Fintype.equivFinOfCardEq hcardN).symm

  let A : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun k j => rho eqv (Phi σ Q (e j)) k
  have hAR : ∀ c : Fin N → ℝ, A *ᵥ c = ∑ j, c j • rho eqv (Phi σ Q (e j)) := by
    intro c
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hAQ : ∀ c : Fin N → ℚ, A *ᵥ (fun j => ((c j : ℚ) : ℝ)) = rho eqv (Phi σ Q (∑ j, c j • e j)) := by
    intro c
    rw [hAR, Phi_sum, rho_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Phi_qsmul, rho_smul]

  let T : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun k j => Algebra.trace ℚ K (S.h (e k) (e j))
  have hfinrank : Module.finrank ℚ (Fin r → K) = N := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hN,
      mul_comm]
  have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  let eB : Module.Basis (Fin N) ℚ (Fin r → K) :=
    basisOfLinearIndependentOfCardEqFinrank heli (by rw [Fintype.card_fin, hfinrank])
  have heB : ∀ j, eB j = e j := fun j => by simp [eB]
  have htrq : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K ((q : K) * z) = q * Algebra.trace ℚ K z := by
    intro q z
    rw [← Rat.smul_def, map_smul, smul_eq_mul]
  have hTdet : T.det ≠ 0 := by
    intro h0
    obtain ⟨s, hs0, hs⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    set x := ∑ j, s j • e j with hx
    have hx0 : x ≠ 0 := by
      intro hx0
      exact hs0 (funext fun j => Fintype.linearIndependent_iff.1 heli s hx0 j)
    have hTx : ∀ k, Algebra.trace ℚ K (S.h (e k) x) = 0 := by
      intro k
      have h1 := congrFun hs k
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, T] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx, h_sum_right, map_sum]
      simp only [h_qsmul_right, htrq]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hall : ∀ v : Fin r → K, Algebra.trace ℚ K (S.h v x) = 0 := by
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← eB.sum_repr v, h_sum_left, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [heB, h_qsmul_left, htrq, hTx k, mul_zero]
    exact hx0 (nondeg σ Q hQ p S hform x hall)

  have hid : ∀ y v : Fin r → K, rho eqv (Theta p (Phi σ Q y)) ⬝ᵥ rho eqv (Phi σ Q v) =
      (1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h y v) : ℚ) : ℝ) := trace_id σ hinj hcm Q p S hform eqv
  have hAdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hTR : (T.map (Rat.castHom ℝ)).det ≠ 0 := by
      rw [show T.map (Rat.castHom ℝ) = (Rat.castHom ℝ).mapMatrix T from rfl, ← RingHom.map_det]
      exact (map_ne_zero _).2 hTdet
    apply hc0
    refine Matrix.eq_zero_of_mulVec_eq_zero hTR ?_
    funext k
    have h1 : rho eqv (Theta p (Phi σ Q (e k))) ⬝ᵥ (A *ᵥ c) = 0 := by rw [hc, dotProduct_zero]
    rw [hAR, dotProduct_sum] at h1
    simp only [dotProduct_smul, hid, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Pi.zero_apply, Rat.coe_castHom, T]
    have h2 : ∑ j, ((Algebra.trace ℚ K (S.h (e k) (e j)) : ℚ) : ℝ) * c j =
        2 * ∑ j, c j * ((1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h (e k) (e j)) : ℚ) : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, h1, mul_zero]

  set dK : ℝ := |(NumberField.discr K : ℝ)| with hdK
  have hdpos : 0 < dK := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero K)
  set μ' : ℝ := laStar / dK with hμ'
  have hμ'pos : 0 < μ' := div_pos hla hdpos
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hAdet
  have hTTdet : Tᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hTdet
  have hAtdet : Aᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hAdet
  have hdual : ∀ t : Fin N → ℤ, t ≠ 0 →
      μ' ^ 2 ≤ ((A⁻¹)ᵀ *ᵥ fun i => (t i : ℝ)) ⬝ᵥ ((A⁻¹)ᵀ *ᵥ fun i => (t i : ℝ)) := by
    intro t ht
    set u := (A⁻¹)ᵀ *ᵥ fun i => (t i : ℝ) with hu
    have hAtu : Aᵀ *ᵥ u = fun i => (t i : ℝ) := by
      rw [hu, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul A hAu,
        Matrix.transpose_one, Matrix.one_mulVec]
    set tq : Fin N → ℚ := fun i => (t i : ℚ) with htq
    set s : Fin N → ℚ := (Tᵀ)⁻¹ *ᵥ ((2 : ℚ) • tq) with hs
    have hTs : Tᵀ *ᵥ s = (2 : ℚ) • tq := by
      rw [hs, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hTTdet), Matrix.one_mulVec]
    set y := ∑ j, s j • e j with hy
    have hyk : ∀ k, Algebra.trace ℚ K (S.h y (e k)) = 2 * (t k : ℚ) := by
      intro k
      have h1 := congrFun hTs k
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.smul_apply,
        smul_eq_mul, htq, T] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy, h_sum_left, map_sum]
      simp only [h_qsmul_left, htrq]
      rw [← h1]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hAty : Aᵀ *ᵥ rho eqv (Theta p (Phi σ Q y)) = fun i => (t i : ℝ) := by
      funext k
      have h1 := hid y (e k)
      rw [dotProduct] at h1
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, A, Matrix.of_apply]
      rw [show (∑ m, rho eqv (Phi σ Q (e k)) m * rho eqv (Theta p (Phi σ Q y)) m) =
        ∑ m, rho eqv (Theta p (Phi σ Q y)) m * rho eqv (Phi σ Q (e k)) m from
        Finset.sum_congr rfl fun m _ => mul_comm _ _, h1, hyk k]
      push_cast
      ring
    have hu' : rho eqv (Theta p (Phi σ Q y)) = u := by
      have h1 : Aᵀ *ᵥ (rho eqv (Theta p (Phi σ Q y)) - u) = 0 := by
        rw [Matrix.mulVec_sub, hAty, hAtu, sub_self]
      exact sub_eq_zero.1 (Matrix.eq_zero_of_mulVec_eq_zero hAtdet h1)
    have hint : ∀ v ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (S.h y v) = n := by
      intro v hv
      obtain ⟨n, hn⟩ := hecoord v hv
      refine ⟨∑ k, n k * (2 * t k), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hn, h_sum_right, map_sum]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [h_qsmul_right, htrq, hyk k]
    have hdy : ((NumberField.discr K : ℤ) : K) • y ∈ L := by
      refine hSD.2 _ fun v hv => ?_
      have hz : ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (S.h y v * a) = n := by
        intro a
        have hav : (a : K) • v ∈ L := L.smul_mem a hv
        obtain ⟨n, hn⟩ := hint _ hav
        refine ⟨n, ?_⟩
        rw [mul_comm, ← h_smul_right, hn]
      have hI := discr_mul_integral (S.h y v) hz
      refine ⟨⟨S.h (((NumberField.discr K : ℤ) : K) • y) v, ?_⟩, rfl⟩
      rw [h_smul_left, map_intCast]
      exact hI
    have hy0 : y ≠ 0 := by
      intro hy0
      have hs0 : s = 0 := funext fun j => Fintype.linearIndependent_iff.1 heli s hy0 j
      apply ht
      funext i
      have h1 := congrFun hTs i
      rw [hs0, Matrix.mulVec_zero] at h1
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, htq] at h1
      have h2 : (t i : ℚ) = 0 := by linarith
      exact_mod_cast h2
    have hdy0 : ((NumberField.discr K : ℤ) : K) • y ≠ 0 :=
      smul_ne_zero (by exact_mod_cast NumberField.discr_ne_zero K) hy0
    obtain ⟨i, hi⟩ := hmin _ hdy hdy0
    have hscale : normSq (Q i *ᵥ embVec (σ i) (((NumberField.discr K : ℤ) : K) • y)) =
        dK ^ 2 * normSq (Q i *ᵥ embVec (σ i) y) := by
      rw [embVec_smul, Matrix.mulVec_smul, map_intCast]
      simp only [normSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum, Complex.norm_intCast]
      rw [hdK, sq_abs]
    have huu : u ⬝ᵥ u = majSq σ Q y := by rw [← hu', theta_dot_self, phi_dot_self]
    rw [huu, hμ', div_pow, div_le_iff₀ (by positivity)]
    have hle : normSq (Q i *ᵥ embVec (σ i) y) ≤ majSq σ Q y :=
      Finset.single_le_sum (f := fun i => normSq (Q i *ᵥ embVec (σ i) y))
        (fun j _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    calc laStar ^ 2 ≤ dK ^ 2 * normSq (Q i *ᵥ embVec (σ i) y) := hscale ▸ hi
      _ ≤ dK ^ 2 * majSq σ Q y := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
      _ = majSq σ Q y * dK ^ 2 := mul_comm _ _

  have hRdet : IsUnit ((A⁻¹)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact Matrix.isUnit_nonsing_inv_det A hAu
  have hRinv : ((A⁻¹)ᵀ)⁻¹ᵀ = A := by
    have h1 : ((A⁻¹)ᵀ)⁻¹ = Aᵀ := Matrix.inv_eq_right_inv (by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv A hAu, Matrix.transpose_one])
    rw [h1, Matrix.transpose_transpose]
  have hdual' : ∀ t : Fin N → ℤ, t ≠ 0 → μ' ^ 2 ≤
      (fun i => (t i : ℝ)) ⬝ᵥ (((A⁻¹)ᵀᵀ * (A⁻¹)ᵀ) *ᵥ fun i => (t i : ℝ)) := by
    intro t ht
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    exact hdual t ht
  obtain ⟨c, hcli, hcb⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.shortDual_holds N ((A⁻¹)ᵀᵀ * (A⁻¹)ᵀ) (A⁻¹)ᵀ μ' hNpos rfl
    hRdet hμ'pos hdual' (N / μ') (by positivity)
  rw [hRinv] at hcb

  set v : Fin N → Fin r → K := fun j => ∑ k, ((c j k : ℤ) : ℚ) • e k with hv
  have hzsm : ∀ (n : ℤ) (x : Fin r → K), x ∈ L → ((n : ℚ) • x) ∈ L := by
    intro n x hx
    rw [Int.cast_smul_eq_zsmul]
    exact L.toAddSubgroup.zsmul_mem hx n
  have hvL : ∀ j, v j ∈ L := fun j => L.sum_mem fun k _ => hzsm _ _ (heL k)
  have hAv : ∀ j, A *ᵥ (fun k => (c j k : ℝ)) = rho eqv (Phi σ Q (v j)) := by
    intro j
    rw [hv, ← hAQ]
    congr 1
  set ℓ : ℝ := 2 * (N : ℝ) / μ' with hℓ
  have hcb' : ∀ j, (A *ᵥ fun k => (c j k : ℝ)) ⬝ᵥ (A *ᵥ fun k => (c j k : ℝ)) ≤ ℓ ^ 2 := by
    intro j
    have h1 := hcb j
    have h2 : ((N : ℝ) / μ' + N / μ') = ℓ := by rw [hℓ]; ring
    rwa [h2] at h1
  have hvb : ∀ j, majSq σ Q (v j) ≤ ℓ ^ 2 := by
    intro j
    rw [← phi_dot_self σ Q eqv, ← hAv j]
    exact hcb' j

  let Cz : Matrix (Fin N) (Fin N) ℤ := Matrix.of c
  have hCz : Cz.det ≠ 0 := by
    intro h0
    obtain ⟨m, hm0, hm⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    apply hm0
    funext j
    refine Fintype.linearIndependent_iff.1 hcli m ?_ j
    funext k
    have h1 := congrFun hm k
    simpa [Matrix.vecMul, dotProduct, Cz, Finset.sum_apply] using h1
  have hCR : (Cz.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [show Cz.map (Int.castRingHom ℝ) = (Int.castRingHom ℝ).mapMatrix Cz from rfl, ← RingHom.map_det]
    simpa using hCz
  have hCQ : (Cz.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [show Cz.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix Cz from rfl, ← RingHom.map_det]
    simpa using hCz
  have hvli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro q hq
    have h1 : ∑ k, (∑ j, q j * (c j k : ℚ)) • e k = 0 := by
      rw [← hq]
      simp only [hv, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2 := Fintype.linearIndependent_iff.1 heli _ h1
    have h3 : q ᵥ* (Cz.map (Int.castRingHom ℚ)) = 0 := by
      funext k
      simpa [Matrix.vecMul, dotProduct, Cz] using h2 k
    exact fun j => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hCQ h3) j
  have hspanQ : Submodule.span ℚ (Set.range v) = ⊤ :=
    hvli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin, hfinrank])
  have hspanK : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Submodule.span ℚ (Set.range v) := hspanQ ▸ Submodule.mem_top
    exact Submodule.span_le_restrictScalars ℚ K _ hx
  obtain ⟨vb, hvbS, hvbli⟩ := exists_basis_in (Set.range v) hspanK

  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast Fintype.card_pos
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  set X : ℝ := (f : ℝ) * r with hX
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hf1 hr1
  have hNX : (N : ℝ) = 2 * X := by rw [hN, hdeg, hX]; push_cast; ring
  set Dq : ℝ := dK / laStar with hDq
  have hDqpos : 0 < Dq := div_pos hdpos hla
  have hμval : μ = 4 * X ^ 3 * Dq := by
    show ReciprocityTheory.ChartRestriction.G.FD.d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar = _
    simp only [ReciprocityTheory.ChartRestriction.G.FD.d5mu, hX, hDq]
    ring
  have hℓval : ℓ = 4 * X * Dq := by
    rw [hℓ, hNX, hμ', hDq]
    field_simp
    ring
  have hX3 : X ≤ X ^ 3 := by simpa using pow_le_pow_right₀ hX1 (show 1 ≤ 3 by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX1 (by norm_num)
  have hℓμ : ℓ ^ 2 ≤ μ ^ 2 := by
    refine pow_le_pow_left₀ (by rw [hℓval]; positivity) ?_ 2
    rw [hℓval, hμval]
    nlinarith
  have hcovμ : ((N : ℝ) * ℓ / 2) ^ 2 ≤ μ ^ 2 := by
    refine pow_le_pow_left₀ (by rw [hℓval, hNX]; positivity) ?_ 2
    rw [hℓval, hμval, hNX]
    nlinarith
  refine ⟨fun w => ?_, vb, fun j => ?_, hvbli, fun j => ?_⟩
  ·
    have hbli : LinearIndependent ℝ (fun j => A *ᵥ (fun k => (c j k : ℝ))) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have h1 : A *ᵥ (a ᵥ* Cz.map (Int.castRingHom ℝ)) = 0 := by
        calc A *ᵥ (a ᵥ* Cz.map (Int.castRingHom ℝ)) = A *ᵥ (∑ i, a i • fun k => (c i k : ℝ)) := by
              congr 1
              funext k
              simp [Matrix.vecMul, dotProduct, Cz, Finset.sum_apply]
          _ = ∑ i, a i • A *ᵥ fun k => (c i k : ℝ) := by
              rw [Matrix.mulVec_sum]
              simp [Matrix.mulVec_smul]
          _ = 0 := ha
      have h2 := Matrix.eq_zero_of_mulVec_eq_zero hAdet h1
      exact fun j => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hCR h2) j
    have hcr := cover_round (N := N) (fun j => A *ᵥ (fun k => (c j k : ℝ))) hbli ℓ hcb' (rho eqv w)
    obtain ⟨n, hn⟩ := hcr
    have hlL : (∑ j, ((n j : ℤ) : ℚ) • v j) ∈ L := Submodule.sum_mem L fun j _ => hzsm (n j) (v j) (hvL j)
    refine ⟨_, hlL, ?_⟩
    have hsumr : ∑ j, (n j : ℝ) • (A *ᵥ (fun k => (c j k : ℝ))) =
        rho eqv (Phi σ Q (∑ j, ((n j : ℤ) : ℚ) • v j)) := by
      rw [Phi_sum, rho_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Phi_qsmul, rho_smul, hAv j]
      simp [Rat.cast_intCast]
    rw [hsumr] at hn
    have heq : ∑ i, normSq (Q i *ᵥ embVec (σ i) (∑ j, ((n j : ℤ) : ℚ) • v j) - w i) =
        (rho eqv w - rho eqv (Phi σ Q (∑ j, ((n j : ℤ) : ℚ) • v j))) ⬝ᵥ
          (rho eqv w - rho eqv (Phi σ Q (∑ j, ((n j : ℤ) : ℚ) • v j))) := by
      rw [← rho_sub, rho_dot_self]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [normSq, Phi, Pi.sub_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← norm_neg, neg_sub]
    rw [heq]
    exact hn.trans hcovμ
  · obtain ⟨j', hj'⟩ := hvbS j
    rw [← hj']
    exact hvL j'
  · obtain ⟨j', hj'⟩ := hvbS j
    rw [← hj']
    exact (hvb j').trans hℓμ

end Formalism.L2.Pj.FundamentalDomainD5
end
end

set_option autoImplicit false

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem t41H_statement : ReciprocityTheory.ChartRestriction.G.FD.FrameAtHalfMaximum (E := E) :=
  ReciprocityTheory.ChartRestriction.G.FD.maxPointFrame_of_transference d5_translation

end Formalism.L2.Pj.FundamentalDomainD5
