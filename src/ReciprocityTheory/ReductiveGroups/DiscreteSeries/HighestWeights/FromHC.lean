module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PolyCoef

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHCB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHCA
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Sig

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]


open Classical in
def fhSig (τ : KG ε →* unitary (V →L[ℂ] V)) (g : Matrix (Fin n) (Fin n) ℂ) : V →L[ℂ] V :=
  if h : g ∈ Kset ε then ((τ (torepK ε h) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) else 1

lemma fhSig_of_mem (τ : KG ε →* unitary (V →L[ℂ] V)) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    fhSig τ g = ((τ (torepK ε hg) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  unfold fhSig
  rw [dite_eq_left hg]

lemma fhSig_toMK (τ : KG ε →* unitary (V →L[ℂ] V)) (k : KG ε) :
    fhSig τ (toMK k) = ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  rw [fhSig_of_mem τ (g := toMK k) k.2, torepK_toMK]

lemma fh_op_mul (τ : KG ε →* unitary (V →L[ℂ] V)) (k k' : KG ε) :
    ((τ (k * k') : unitary (V →L[ℂ] V)) : V →L[ℂ] V) =
      ((τ k : unitary (V →L[ℂ] V)) : V →L[ℂ] V).comp ((τ k' : unitary (V →L[ℂ] V)) : V →L[ℂ] V) := by
  rw [map_mul]
  rfl

lemma fhSig_isURepOn (τ : KG ε →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) :
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) (fhSig τ) := by
  have hmul : ∀ a ∈ Kset ε, ∀ b ∈ Kset ε, a * b ∈ Kset ε := by
    intro a ha b hb
    refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
    rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
    ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [fhSig_of_mem τ hone]
    have h1 : torepK ε hone = 1 := onep_KG_ext (by rw [toMK_torepK]; rfl)
    rw [h1, map_one]
    rfl
  · intro a ha b hb
    rw [fhSig_of_mem τ ha, fhSig_of_mem τ hb, fhSig_of_mem τ (hmul a ha b hb)]
    have h1 : torepK ε (hmul a ha b hb) = torepK ε ha * torepK ε hb := onep_KG_ext (by
      rw [toMK_torepK]
      exact (congrArg₂ (· * ·) (toMK_torepK ε ha) (toMK_torepK ε hb)).symm)
    rw [h1, fh_op_mul]
  · intro g hg v
    rw [fhSig_of_mem τ hg]
    exact Unitary.norm_map _ v
  · intro v
    rw [continuousOn_iff_continuous_restrict]
    show Continuous fun x : ↥(Kset ε) => fhSig τ (x : Matrix (Fin n) (Fin n) ℂ) v
    have hc : Continuous fun x : ↥(Kset ε) =>
        ((τ (torepK ε x.2) : unitary (V →L[ℂ] V)) : V →L[ℂ] V) v :=
      (continuous_subtype_val.comp (hτ.comp (continuous_torepK ε))).clm_apply continuous_const
    refine hc.congr fun x => ?_
    rw [fhSig_of_mem τ x.2]

end Sig

section InK

variable {n : ℕ} {ε : Fin n → Bool}

end InK

section Coef

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ}

def fhEnt (k : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] (Fin k × Fin k → ℂ) where
  toFun A ij := A ij.1 ij.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma fh_diff_eval (P : MvPolynomial (Fin k × Fin k) ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => MvPolynomial.eval (fhEnt k A) P) A := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact differentiableAt_const _
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (differentiableAt_pi.1
      (LinearMap.toContinuousLinearMap (fhEnt k)).differentiableAt i)

lemma fh_det_eq (A : Matrix (Fin k) (Fin k) ℂ) :
    A.det = MvPolynomial.eval (fhEnt k A) (Matrix.det (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ)) := by
  have h : (fhEnt k A : Fin k × Fin k → ℂ) = fun p => A p.1 p.2 := rfl
  rw [h, RingHom.map_det, Matrix.mvPolynomialX_mapMatrix_eval]

end Coef

section Coef2

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V]

lemma fh_det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Kset (fun _ : Fin k => true)) : g.det ≠ 0 := by
  intro h0
  have hu := Matrix.mem_unitaryGroup_iff.1 hg.1
  have h := congrArg Matrix.det hu
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

theorem fh_coef (τ : KG (fun _ : Fin k => true) →* unitary (V →L[ℂ] V)) (hτ : Continuous τ) (v w : V) :
    ∃ L : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] ℂ, ∀ X, inK (fun _ : Fin k => true) X →
      inner ℂ w (derOp (fun _ : Fin k => true) τ X v) = L X := by
  classical
  obtain ⟨m, P, hP⟩ := polynomial_coefficients k V (fhSig τ) ⊤ (fhSig_isURepOn τ hτ) inferInstance
    (fun _ _ _ _ => Submodule.mem_top) v Submodule.mem_top w
  have hdet1 : DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) 1 := by
    have h : (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) = fun A =>
        MvPolynomial.eval (fhEnt k A) (Matrix.det (Matrix.mvPolynomialX (Fin k) (Fin k) ℂ)) :=
      funext fh_det_eq
    rw [h]
    exact fh_diff_eval _ _
  let F : Matrix (Fin k) (Fin k) ℂ → ℂ := fun A =>
    MvPolynomial.eval (fhEnt k A) P * (A.det ^ m)⁻¹
  have hF : DifferentiableAt ℂ F 1 := by
    have hne : (1 : Matrix (Fin k) (Fin k) ℂ).det ^ m ≠ 0 := by
      rw [Matrix.det_one, one_pow]
      exact one_ne_zero
    have hpow : DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => A.det ^ m) 1 :=
      (differentiableAt_pow m).comp 1 hdet1
    exact (fh_diff_eval P 1).mul (hpow.inv hne)
  refine ⟨(fderiv ℂ F 1).toLinearMap, fun X hX => ?_⟩
  have hγ := (kcurve_spec (fun _ : Fin k => true) hX).2.1
  have hD := derOp_hasDeriv (fun _ : Fin k => true) τ hτ X hX (kcurve (fun _ : Fin k => true) X) hγ
  let Λ : (V →L[ℂ] V) →L[ℂ] ℂ := (innerSL ℂ w).comp (ContinuousLinearMap.apply ℂ V v)
  have h1 := (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hD
  have he := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at he
  have h3 := (hF.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 he (by simp)
  have heq : (⇑(Λ.restrictScalars ℝ) ∘ fun t : ℝ =>
      ((τ (kcurve (fun _ : Fin k => true) X t) : unitary (V →L[ℂ] V)) : V →L[ℂ] V)) =
      F ∘ fun u : ℝ => NormedSpace.exp (u • X) := by
    funext t
    have hx : NormedSpace.exp (t • X) = toMK (kcurve (fun _ : Fin k => true) X t) := by
      rw [hγ t]
      exact congrArg NormedSpace.exp (Complex.coe_smul t X).symm
    simp only [Function.comp_apply]
    rw [hx]
    have hk : toMK (kcurve (fun _ : Fin k => true) X t) ∈ Kset (fun _ : Fin k => true) := (kcurve (fun _ : Fin k => true) X t).2
    have hP' := hP _ hk
    rw [fhSig_toMK] at hP'
    simp only [Λ, F, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply]
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ (fh_det_ne_zero hk))]
    exact hP'
  rw [heq] at h1
  have h4 := h1.unique h3
  exact h4

end Coef2

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section Alg

variable {k : ℕ}

lemma fh_Jm_allPos : Jm (fun _ : Fin k => true) = 1 := by
  ext i j
  simp [Jm, Matrix.diagonal, Matrix.one_apply]

lemma fh_decomp (Z : Matrix (Fin k) (Fin k) ℂ) : ∃ Z₁ Z₂ : Matrix (Fin k) (Fin k) ℂ,
    inK (fun _ : Fin k => true) Z₁ ∧ inK (fun _ : Fin k => true) Z₂ ∧ Z = Z₁ + Complex.I • Z₂ := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  have hh : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hi : star (-(Complex.I / 2)) = Complex.I / 2 := by
    simp [Complex.star_def, Complex.conj_I, neg_div]
  refine ⟨(1 / 2 : ℂ) • (Z - Zᴴ), (-(Complex.I / 2)) • (Z + Zᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, hh]
    module
  · rw [hJ, Matrix.mul_one, Matrix.one_mul]
  · simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, hi]
    module
  · rw [hJ, Matrix.mul_one, Matrix.one_mul]
  · have hI : Complex.I * (-(Complex.I / 2)) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]
      ring
    rw [smul_smul, hI]
    module

lemma fh_diag_conj (d : Fin k → ℂ) (a b : Fin k) :
    Matrix.diagonal d * Matrix.single a b 1 * star (Matrix.diagonal d) =
      (d a * star (d b)) • Matrix.single a b 1 := by
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [smul_eq_mul]
  · simp

lemma fh_not_cdom {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b) :
    ¬ Formalism.MainNotions.S.CDom (fun _ : Fin k => true) (Λ + Pi.single a 1 - Pi.single b 1) Λ := by
  rintro ⟨c, hc, hsum⟩
  let f : (Fin k → ℝ) →ₗ[ℝ] ℝ := ∑ i : Fin k, ((i : ℕ) : ℝ) • LinearMap.proj i
  have hf : ∀ x, f x = ∑ i : Fin k, ((i : ℕ) : ℝ) * x i := fun x => by simp [f]
  have hs : ∀ j : Fin k, f (Pi.single j 1) = ((j : ℕ) : ℝ) := fun j => by
    rw [hf]
    simp [Pi.single_apply]
  have hL : Λ - (Λ + Pi.single a 1 - Pi.single b 1) = Pi.single b 1 - Pi.single a 1 := by abel
  have h1 := congrArg f hsum
  rw [hL, map_sub, hs, hs] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Formalism.REAL.root, map_sub, hs, smul_eq_mul] at h1
  have hneg : ∑ x : Fin k, ∑ y : Fin k, (c x y : ℝ) * (((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)) ≤ 0 := by
    refine Finset.sum_nonpos fun x _ => Finset.sum_nonpos fun y _ => ?_
    by_cases h0 : c x y = 0
    · simp [h0]
    · have hxy : ((x : ℕ) : ℝ) < ((y : ℕ) : ℝ) := Nat.cast_lt.mpr (hc x y h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.mpr hab
  linarith

end Alg

section Tau

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma fh_unitary (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) (g : KG (fun _ : Fin k => true)) :
    π (toMK g) ∈ unitary (H →L[ℂ] H) := by
  have hmem : toMK g ∈ Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) := g.1.2
  have hiso := hU.2.1 _ hmem
  have hmul : ∀ a b : KG (fun _ : Fin k => true), π (toMK (a * b)) = π (toMK a) * π (toMK b) :=
    fun a b => hU.1.2 _ a.1.2 _ b.1.2
  have hone : π (toMK (1 : KG (fun _ : Fin k => true))) = 1 := hU.1.1
  have hTR : π (toMK g) * π (toMK g⁻¹) = 1 := by rw [← hmul, mul_inv_cancel, hone]
  have h1 : star (π (toMK g)) * π (toMK g) = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp hiso
  have hstar : star (π (toMK g)) = π (toMK g⁻¹) := by
    calc star (π (toMK g)) = star (π (toMK g)) * (π (toMK g) * π (toMK g⁻¹)) := by rw [hTR, mul_one]
      _ = π (toMK g⁻¹) := by rw [← mul_assoc, h1, one_mul]
  exact Unitary.mem_iff.mpr ⟨h1, by rw [hstar, hTR]⟩

def fhTau (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) :
    KG (fun _ : Fin k => true) →* unitary (H →L[ℂ] H) where
  toFun g := ⟨π (toMK g), fh_unitary π hU g⟩
  map_one' := Subtype.ext hU.1.1
  map_mul' a b := Subtype.ext (hU.1.2 _ (a : UJ (fun _ : Fin k => true)).2 _ (b : UJ (fun _ : Fin k => true)).2)

lemma fhTau_coe (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) (g : KG (fun _ : Fin k => true)) :
    ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = π (toMK g) := rfl

lemma fhTau_cont [FiniteDimensional ℂ H] (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k)) π) : Continuous (fhTau π hU) := by
  apply continuous_induced_rng.2
  change Continuous fun g : KG (fun _ : Fin k => true) => π (toMK g)
  rw [continuous_clm_apply]
  intro v
  have hc : Continuous fun g : KG (fun _ : Fin k => true) => toMK g :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  exact (hU.2.2 v).comp_continuous hc (fun g => g.1.2)

end Tau

section Der

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (τ : KG (fun _ : Fin k => true) →* unitary (H →L[ℂ] H))
  (dτ : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] (H →L[ℂ] H))
  (hder : ∀ X, inK (fun _ : Fin k => true) X → ∀ γ : ℝ → KG (fun _ : Fin k => true),
    (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0)
  (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H))
  (hσ : ∀ g : KG (fun _ : Fin k => true), σ (toMK g) = ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))

include hder in
lemma fh_conj (g : KG (fun _ : Fin k => true)) {Y : Matrix (Fin k) (Fin k) ℂ}
    (hY : inK (fun _ : Fin k => true) Y) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Y * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Y * star (toMK g)) := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  have hγ : ∀ t : ℝ, toMK (onepCurve (fun _ : Fin k => true) hY t) =
      NormedSpace.exp ((t : ℂ) • Y) := toMK_onepCurve _ hY
  have hKs : toMK g ∈ Formalism.REAL.Kset (fun _ : Fin k => true) := g.2
  have hun : star (toMK g) * toMK g = 1 := Matrix.mem_unitaryGroup_iff'.mp hKs.1
  have hinv : toMK g * toMK g⁻¹ = 1 := by exact Units.mul_inv g.1.1
  have hg : star (toMK g) = toMK g⁻¹ := by
    calc star (toMK g) = star (toMK g) * (toMK g * toMK g⁻¹) := by rw [hinv, Matrix.mul_one]
      _ = toMK g⁻¹ := by rw [← Matrix.mul_assoc, hun, Matrix.one_mul]
  have hc : inK (fun _ : Fin k => true) (toMK g * Y * star (toMK g)) := by
    obtain ⟨h1, -⟩ := hY
    simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul] at h1
    refine ⟨?_, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
    simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.add_mul, ← Matrix.mul_add, h1,
      Matrix.mul_zero, Matrix.zero_mul]
  have hδ : ∀ t : ℝ, toMK (g * onepCurve (fun _ : Fin k => true) hY t * g⁻¹) =
      NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
    intro t
    have e := Matrix.exp_units_conj g.1.1 ((t : ℂ) • Y)
    calc toMK (g * onepCurve (fun _ : Fin k => true) hY t * g⁻¹)
        = toMK g * NormedSpace.exp ((t : ℂ) • Y) * toMK g⁻¹ := by rw [← hγ t]; rfl
      _ = NormedSpace.exp ((t : ℂ) • (toMK g * Y * star (toMK g))) := by
        rw [hg, ← Matrix.smul_mul, ← Matrix.mul_smul]
        exact e.symm
  have hU' : ((τ g⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hd1 := hder _ hc (fun t => g * onepCurve (fun _ : Fin k => true) hY t * g⁻¹) hδ
  have h0 := hder Y hY _ hγ
  have heq : (fun t => ((τ (g * onepCurve (fun _ : Fin k => true) hY t * g⁻¹) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) =
      fun t => ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) *
        ((τ (onepCurve (fun _ : Fin k => true) hY t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) *
        star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    funext t
    rw [map_mul, map_mul, ← hU']
    rfl
  have hd2 := (h0.const_mul ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H)).mul_const
    (star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H))
  rw [← heq] at hd2
  exact hd2.unique hd1

include hder in
lemma fh_conj_all (g : KG (fun _ : Fin k => true)) (Z : Matrix (Fin k) (Fin k) ℂ) :
    ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ Z * star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) =
      dτ (toMK g * Z * star (toMK g)) := by
  obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := fh_decomp Z
  rw [map_add (f := _), map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, fh_conj τ dτ hder g h1,
    fh_conj τ dτ hder g h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add,
    map_smul]

include hder hσ in
lemma fh_dτ_of_wt {μ : Fin k → ℝ} {v : H}
    (hv : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (fun _ : Fin k => true)) σ μ v) (a : Fin k) :
    dτ (Matrix.single a a 1) v = ((μ a : ℝ) : ℂ) • v := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  have hX : inK (fun _ : Fin k => true) (Complex.I • Matrix.single a a 1) := by
    refine ⟨?_, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
    simp only [inG, hJ, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one]
    simp [Complex.star_def, Complex.conj_I]
  have hγ : ∀ t : ℝ, toMK (onepCurve (fun _ : Fin k => true) hX t) =
      NormedSpace.exp ((t : ℂ) • (Complex.I • Matrix.single a a 1)) := toMK_onepCurve _ hX
  have hd1 := hder _ hX _ hγ
  have hd2 : HasDerivAt
      (fun t => ((τ (onepCurve (fun _ : Fin k => true) hX t) :
        unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) (dτ (Complex.I • Matrix.single a a 1) v) 0 :=
    ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd1
  let θ : ℝ → Fin k → ℝ := fun t b => if b = a then t else 0
  have hdiag : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ))) =
      Matrix.diagonal (fun b => Complex.exp (((θ t b : ℝ) : ℂ) * Complex.I)) := by
    intro t
    have e1 : (t : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ)) =
        Matrix.diagonal (fun b => ((θ t b : ℝ) : ℂ) * Complex.I) := by
      ext i j
      rcases eq_or_ne i j with rfl | hij
      · by_cases hia : i = a
        · subst hia
          simp [θ, Matrix.diagonal_apply, Matrix.single_apply, mul_comm]
        · simp [θ, Matrix.diagonal_apply, Matrix.single_apply, hia, Ne.symm hia]
      · simp [θ, Matrix.diagonal_apply, Matrix.single_apply, hij]
        rintro rfl rfl
        exact absurd rfl hij
    rw [e1, Matrix.exp_diagonal, Pi.exp_def, Complex.exp_eq_exp_ℂ]
  have hval : ∀ t : ℝ, ((τ (onepCurve (fun _ : Fin k => true) hX t) :
      unitary (H →L[ℂ] H)) : H →L[ℂ] H) v = Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := by
    intro t
    have hm : Matrix.diagonal (fun b => Complex.exp (((θ t b : ℝ) : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (fun _ : Fin k => true) := by
      rw [← hdiag t, ← hγ t]
      exact (onepCurve (fun _ : Fin k => true) hX t).2
    rw [← hσ, hγ t, hdiag t, hv (θ t) hm]
    congr 3
    simp [θ]
  have hd3 : HasDerivAt (fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v)
      ((Complex.exp (((μ a * 0 : ℝ) : ℂ) * Complex.I) * (((μ a * 1 : ℝ) : ℂ) * Complex.I)) • v) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul (μ a)).ofReal_comp.mul_const Complex.I).cexp).smul_const v
  have hfun : (fun t => ((τ (onepCurve (fun _ : Fin k => true) hX t) :
      unitary (H →L[ℂ] H)) : H →L[ℂ] H) v) =
      fun t : ℝ => Complex.exp (((μ a * t : ℝ) : ℂ) * Complex.I) • v := funext hval
  rw [hfun] at hd2
  have hu := hd2.unique hd3
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hu
  rw [map_smul, ContinuousLinearMap.smul_apply, mul_comm, mul_smul] at hu
  exact smul_right_injective H Complex.I_ne_zero hu

include hder hσ in
lemma fh_hw {Λ : Fin k → ℝ}
    (hK5 : ∀ (μ : Fin k → ℝ) (v : H), v ∈ (⊤ : Submodule ℂ H) → v ≠ 0 →
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (fun _ : Fin k => true)) σ μ v → Formalism.MainNotions.S.CDom (fun _ : Fin k => true) μ Λ)
    {w : H} (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset (fun _ : Fin k => true)) σ Λ w) (a b : Fin k) (hab : a < b) :
    dτ (Matrix.single a b 1) w = 0 := by
  have hJ : Jm (fun _ : Fin k => true) = 1 := fh_Jm_allPos
  by_contra hne
  refine fh_not_cdom hab (hK5 _ (dτ (Matrix.single a b 1) w) Submodule.mem_top hne ?_)
  intro θ hθ
  set d : Fin k → ℂ := fun c => Complex.exp ((θ c : ℂ) * Complex.I) with hd
  have hD1 : star (Matrix.diagonal d) * Matrix.diagonal d = 1 := Matrix.mem_unitaryGroup_iff'.mp hθ.1
  have hD2 : Matrix.diagonal d * star (Matrix.diagonal d) = 1 := Matrix.mem_unitaryGroup_iff.mp hθ.1
  let u0 : (Matrix (Fin k) (Fin k) ℂ)ˣ := ⟨Matrix.diagonal d, star (Matrix.diagonal d), hD2, hD1⟩
  have huJ : u0 ∈ UJ (fun _ : Fin k => true) := by
    show (Matrix.diagonal d)ᴴ * Jm (fun _ : Fin k => true) * Matrix.diagonal d = Jm (fun _ : Fin k => true)
    rw [hJ, Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hD1]
  let g0 : UJ (fun _ : Fin k => true) := ⟨u0, huJ⟩
  let g : KG (fun _ : Fin k => true) := ⟨g0, hθ⟩
  have hg : toMK g = Matrix.diagonal d := rfl
  have hU1 : star ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = 1 :=
    Unitary.star_mul_self_of_mem (τ g).2
  have hcomm : ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) * dτ (Matrix.single a b 1) =
      dτ (toMK g * Matrix.single a b 1 * star (toMK g)) * ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
    rw [← fh_conj_all τ dτ hder g, mul_assoc _ (star _) _, hU1, mul_one]
  have h3 : ((τ g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) w =
      Complex.exp (((∑ c, Λ c * θ c : ℝ) : ℂ) * Complex.I) • w := by
    rw [← hσ, hg]
    exact hw θ hθ
  have h2 := congrArg (fun T : H →L[ℂ] H => T w) hcomm
  simp only [ContinuousLinearMap.mul_apply] at h2
  rw [hg, fh_diag_conj, h3] at h2
  rw [← hg, hσ, h2, map_smul, LinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  congr 1
  have hs : ∑ c, (Λ + Pi.single a 1 - Pi.single b 1 : Fin k → ℝ) c * θ c = (∑ c, Λ c * θ c) + θ a - θ b := by
    simp [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
  have hst : star (d b) = Complex.exp (-((θ b : ℂ) * Complex.I)) := by
    rw [hd, Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  rw [hs, hst, hd]
  simp only
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Der

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem derivExists_allPos : DerivExistsAllPosStatement := by
  intro k V _ _ _ τ hτ
  classical
  have : CompleteSpace V := FiniteDimensional.completeSpace ℂ V
  let ε : Fin k → Bool := fun _ => true
  let σ (g : Matrix (Fin k) (Fin k) ℂ) : V →L[ℂ] V :=
    if hg : g ∈ Kset ε then (τ (torepK ε hg)).val else 1
  have hσ {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Kset ε) :
      σ g = (τ (torepK ε hg)).val := dite_eq_left hg
  have hrep : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) σ := by
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · have h1 : (1 : Matrix (Fin k) (Fin k) ℂ) ∈ Kset ε :=
        ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
      rw [hσ h1, show torepK ε h1 = 1 from onep_KG_ext (toMK_torepK ε h1), map_one]
      rfl
    · intro a ha b hb
      change a ∈ Kset ε at ha
      change b ∈ Kset ε at hb
      have hab : a * b ∈ Kset ε := by
        refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
        rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]
      have hmul : torepK ε hab = torepK ε ha * torepK ε hb := by
        apply onep_KG_ext
        change toMK (torepK ε hab) = toMK (torepK ε ha) * toMK (torepK ε hb)
        rw [toMK_torepK, toMK_torepK, toMK_torepK]
      rw [hσ hab, hσ ha, hσ hb, hmul]
      exact fh_op_mul τ _ _
    · intro g hg v
      rw [hσ hg]
      exact Unitary.norm_map _ v
    · intro v
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous fun g : Kset ε => (τ (torepK ε g.2)).val v :=
        (continuous_subtype_val.comp (hτ.comp (continuous_torepK ε))).clm_apply continuous_const
      exact hc.congr fun g => (congrArg (fun A : V →L[ℂ] V => A v) (hσ g.2)).symm
  let b := stdOrthonormalBasis ℂ V
  have hcoeff (i j : Fin (Module.finrank ℂ V)) :=
    polynomial_coefficients k V σ ⊤ hrep inferInstance
      (fun _ _ _ _ => Submodule.mem_top) (b j) Submodule.mem_top (b i)
  choose m P hP using hcoeff
  let F (A : Matrix (Fin k) (Fin k) ℂ) : V →L[ℂ] V :=
    ∑ i, ∑ j, (MvPolynomial.eval (fhEnt k A) (P i j) * (A.det ^ m i j)⁻¹) •
      ((innerSL ℂ (b j)).smulRight (b i))
  have hF (g : KG ε) : F (toMK g) = (τ g).val := by
    have hg : toMK g ∈ Kset ε := g.2
    have hσg : σ (toMK g) = (τ g).val := by rw [hσ hg, torepK_toMK]
    have hc (i j : Fin (Module.finrank ℂ V)) :
        MvPolynomial.eval (fhEnt k (toMK g)) (P i j) * ((toMK g).det ^ m i j)⁻¹ =
          inner ℂ (b i) ((τ g).val (b j)) := by
      rw [← hσg, mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ (fh_det_ne_zero hg))]
      exact (hP i j _ hg).symm
    ext v
    simp only [F, hc, sum_apply, _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    conv_rhs => rw [← b.sum_repr' v]
    simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [← b.sum_repr' ((τ g).val (b j)), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  let _ : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℝ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  have hdet : DifferentiableAt ℂ (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) 1 := by
    rw [show (fun A : Matrix (Fin k) (Fin k) ℂ => A.det) = _ from funext fh_det_eq]
    exact fh_diff_eval _ _
  have hdiff : DifferentiableAt ℂ F 1 := by
    apply DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    exact ((fh_diff_eval (P i j) _).mul ((hdet.pow _).inv (by simp))).smul_const _
  refine ⟨(fderiv ℂ F 1).toLinearMap, ?_⟩
  intro X _ γ hγ
  have hexp := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
  have hcomp := (hdiff.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hexp (by simp)
  have hcurve : (fun t : ℝ => (τ (γ t)).val) = F ∘ fun t : ℝ => NormedSpace.exp (t • X) := by
    funext t
    rw [Function.comp_apply, ← Complex.coe_smul, ← hγ t, hF]
  rw [hcurve]
  exact hcomp

theorem kType_of_hcTypeU {k : ℕ} {u : Fin k → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (hπ : Formalism.MainNotions.S.IsHCTypeU k u π) :
    ∃ T : KType (fun _ : Fin k => true) (lowK (fun _ : Fin k => true) u), ∃ U : H ≃ₗᵢ[ℂ] T.V,
      ∀ (g : KG (fun _ : Fin k => true)) (v : H), U (π (toMK g) v) = T.op g (U v) := by
  obtain ⟨hnt, hfd, hU, hK⟩ := hπ
  haveI := hfd
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  obtain ⟨dτ, hd⟩ := derivExists_allPos k H (fhTau π hU) (fhTau_cont π hU)
  have hσ : ∀ g, π (toMK g) = ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) :=
    fun g => (fhTau_coe π hU g).symm
  obtain ⟨_, _, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  have hwt := fun a => fh_dτ_of_wt (fhTau π hU) dτ hd π hσ hvw a
  have hhw := fun a b hab => fh_hw (fhTau π hU) dτ hd π hσ hdom hvw a b hab
  let T : KType (fun _ : Fin k => true) (lowK (fun _ : Fin k => true) u) :=
    { V := H
      τ := fhTau π hU
      cont := fhTau_cont π hU
      irred := ?irr
      dτ := dτ
      hasDeriv := hd
      w := ((‖v‖⁻¹ : ℝ) : ℂ) • v
      w_norm := ?nrm
      w_wt := ?wt
      w_hw := ?hw }
  refine ⟨T, LinearIsometryEquiv.refl ℂ H, ?_⟩
  case irr =>
    intro W hW
    apply hirr W le_top
    intro g hg x hx
    have := hW (torepK _ hg) x hx
    rw [← hσ] at this
    first
    | (rwa [toMK_torepK (fun _ : Fin k => true) hg] at this)
    | (convert this using 2; exact (toMK_torepK (fun _ : Fin k => true) hg).symm)
  case nrm =>
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  case wt =>
    intro a
    rw [map_smul, hwt a]
    exact smul_comm _ _ _
  case hw =>
    intro a b hab _
    rw [map_smul, hhw a b hab, smul_zero]
  intro g x
  first
  | (simp only [LinearIsometryEquiv.refl_apply, KType.op, hσ])
  | (show π (toMK g) x = ((fhTau π hU g : unitary (H →L[ℂ] H)) : H →L[ℂ] H) x; rw [hσ])

end ReciprocityTheory.ChartRestriction.DS.HW
