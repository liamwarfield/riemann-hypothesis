module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse

theorem isOpen_posDef_hermitian {X κ : Type} [TopologicalSpace X] [Fintype κ]
    (M : X → Matrix κ κ ℂ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : κ → ℂ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (κ → ℂ) => (dotProduct (star p.2) ((M p.1).mulVec p.2)).re) :=
    Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd))
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : κ → ℂ) 1,
      0 < (dotProduct (star v) ((M x).mulVec v)).re := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0)).1
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul] at h1
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  have hre : 0 < (dotProduct (star v) ((M x).mulVec v)).re :=
    (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)
  have hstar : star (dotProduct (star v) ((M x).mulVec v)) = dotProduct (star v) ((M x).mulVec v) := by
    conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, (hs x).eq, ← Matrix.dotProduct_mulVec]
  have him : (dotProduct (star v) ((M x).mulVec v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
  exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem isOpen_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    IsOpen (ballDom q) := by
  have hset : ballDom q = ⋂ τ, {t | (1 - (ballMat q t τ)ᴴ * ballMat q t τ).PosDef} := by
    ext t
    simp [ballDom]
  rw [hset]
  refine isOpen_iInter_of_finite fun τ => isOpen_posDef_hermitian _ ?_ fun t => ?_
  · have hm : Continuous fun t : Fin n → ℂ => ballMat q t τ :=
      continuous_matrix fun a b => continuous_apply _
    exact continuous_const.sub (hm.matrix_conjTranspose.matrix_mul hm)
  · exact (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)

theorem exists_inverse : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  intro Ψ _ j j' n q Z G hZ hbij _ _
  have hJ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicKernelFibre.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CriticalFlatNotInjective.proof
  obtain ⟨-, Y, hY, hYZ⟩ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.proof hJ n _ Z
    (isOpen_ballDom q) hZ hbij.injOn
  rw [hbij.image_eq] at hY
  refine ⟨Y, hY, fun t ht => ?_⟩
  obtain ⟨s, hs, hst⟩ := hbij.surjOn ht
  have hYt : Y t = s := by
    rw [← hst]
    exact hYZ s hs
  exact ⟨hYt ▸ hs, by rw [hYt, hst], hYZ t ht⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExistsStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_automorphism_inverse_exists : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F) (R : RiemLat E g Λ) (τ : Ψ)

open Classical in
theorem pPart_add (y y' : Fin (j + j') → ℂ) : C.pPart R τ (y + y') = C.pPart R τ y + C.pPart R τ y' := by
  simp only [LatEmb.pPart, smul_add, Pi.single_add, map_add (f := _), smul_sub]
  abel

open Classical in
theorem pPart_real_smul (r : ℝ) (y : Fin (j + j') → ℂ) : C.pPart R τ (r • y) = (r : ℂ) • C.pPart R τ y := by
  have h1 : ∀ y : Fin (j + j') → ℂ, C.perExt R (Pi.single τ (r • y)) = (r : ℂ) • C.perExt R (Pi.single τ y) := by
    intro y
    rw [Pi.single_smul, map_smul]
    ext i; simp
  have h2 : Complex.I • r • y = r • Complex.I • y := smul_comm _ _ _
  simp only [LatEmb.pPart, h2, h1, smul_sub]
  simp only [smul_smul]
  congr 2 <;> ring_nf

open Classical in
theorem pPart_I_smul (y : Fin (j + j') → ℂ) : C.pPart R τ (Complex.I • y) = Complex.I • C.pPart R τ y := by
  have h : Complex.I • Complex.I • y = -y := by simp [smul_smul]
  have h2 : C.perExt R (Pi.single τ (-y)) = - C.perExt R (Pi.single τ y) := by
    rw [Pi.single_neg, map_neg]
  simp only [LatEmb.pPart, h, h2]
  ext k
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  linear_combination (1 / 2 * (C.perExt R (Pi.single τ (Complex.I • y))) k) * Complex.I_mul_I

def pPartL : (Fin (j + j') → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun := C.pPart R τ
  map_add' := pPart_add C R τ
  map_smul' a y := by
    have ha : a • y = a.re • y + a.im • Complex.I • y := by
      ext i; simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      conv_lhs => rw [← Complex.re_add_im a]
      ring
    rw [ha, pPart_add, pPart_real_smul, pPart_real_smul, pPart_I_smul]
    simp only [RingHom.id_apply]
    conv_rhs => rw [← Complex.re_add_im a]
    rw [add_smul, mul_smul]

theorem pPart_elim (A : Matrix (Fin (j + j')) (Sg j j') ℂ) (v : Fin j → ℂ) (x : Fin j' → ℂ) :
    C.pPart R τ (A *ᵥ Sum.elim v x) =
      ∑ i, v i • C.pPart R τ (A *ᵥ Sum.elim (Pi.single i 1) 0) +
      ∑ b, x b • C.pPart R τ (A *ᵥ Sum.elim 0 (Pi.single b 1)) := by
  have hs : Sum.elim v x = ∑ i, v i • (Sum.elim (Pi.single i 1) 0 : Sg j j' → ℂ) +
      ∑ b, x b • (Sum.elim 0 (Pi.single b 1) : Sg j j' → ℂ) := by
    ext (i | b)
    · simp [Finset.sum_apply, Pi.single_apply]
    · simp [Finset.sum_apply, Pi.single_apply]
  change pPartL C R τ _ = ∑ i, v i • pPartL C R τ _ + ∑ b, x b • pPartL C R τ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, Matrix.mulVec_add, map_add (f := _), Matrix.mulVec_sum, Matrix.mulVec_sum, map_sum, map_sum]
  simp [Matrix.mulVec_smul]

end

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInverseProperties
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInverseProperties
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem facts (eqv : n ≃ m) (I : Matrix m m ℂ) (hI : I * I = 1) (G : Matrix n n ℂ) (e : ℂ) (he : e * e = 1)
    (A : Matrix n m ℂ) (hA : Aᴴ * (e • G) * A = I) (c : Matrix m n ℂ) (hc : c = I * Aᴴ * (e • G)) :
    c * A = 1 ∧ A * c = 1 ∧ (cᴴ * c).PosDef ∧ (cᴴ * c) * G⁻¹ * (cᴴ * c) = G ∧
    (∀ a ai : Matrix n n ℂ, a * ai = 1 → aᴴ * G * a = G →
      (a * A)ᴴ * (e • G) * (a * A) = I ∧ I * (a * A)ᴴ * (e • G) = c * ai ∧
      (c * (a * A))ᴴ * I * (c * (a * A)) = I ∧
      ((c * (a * A))ᴴ * (c * (a * A)) = 1 ↔ aᴴ * (cᴴ * c) * a = cᴴ * c)) ∧
    ∀ A' : Matrix n m ℂ, A'ᴴ * (e • G) * A' = I → (A' * c)ᴴ * G * (A' * c) = G := by
  have hee : ∀ X : Matrix n n ℂ, e • e • X = X := fun X => by rw [smul_smul, he, one_smul]
  have h1 : c * A = 1 := by
    calc c * A = I * (Aᴴ * (e • G) * A) := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, hI]
  have h2 : A * c = 1 := (Matrix.mul_eq_one_comm_of_equiv eqv.symm).1 h1
  have h1h : Aᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h2h : cᴴ * Aᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hS : cᴴ * I * c = e • G := by
    calc cᴴ * I * c = cᴴ * (Aᴴ * (e • G) * A) * c := by rw [hA]
      _ = (cᴴ * Aᴴ) * (e • G) * (A * c) := by simp only [Matrix.mul_assoc]
      _ = e • G := by rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
  have hSX : (e • G) * (A * I * Aᴴ) = 1 := by
    calc (e • G) * (A * I * Aᴴ) = cᴴ * I * (c * A) * I * Aᴴ := by
          rw [← hS]; simp only [Matrix.mul_assoc]
      _ = cᴴ * (I * I) * Aᴴ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hI, Matrix.mul_one, h2h]
  have hGX : G * (e • (A * I * Aᴴ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul]; exact hSX
  have hGinv : G⁻¹ = e • (A * I * Aᴴ) := Matrix.inv_eq_right_inv hGX
  have hc_inj : Function.Injective c.mulVec := by
    intro v w hvw
    have := congrArg A.mulVec hvw
    simpa [Matrix.mulVec_mulVec, h2] using this
  refine ⟨h1, h2, Matrix.PosDef.conjTranspose_mul_self c hc_inj, ?_, ?_, ?_⟩
  · calc (cᴴ * c) * G⁻¹ * (cᴴ * c) = e • (cᴴ * (c * A) * I * (Aᴴ * cᴴ) * c) := by
          rw [hGinv, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = e • (cᴴ * I * c) := by rw [h1, h1h, Matrix.mul_one, Matrix.mul_one]
      _ = G := by rw [hS, hee]
  · intro a ai hai ha
    have hia : ai * a = 1 := mul_eq_one_comm.1 hai
    have hSa : aᴴ * (e • G) * a = e • G := by rw [Matrix.mul_smul, Matrix.smul_mul, ha]
    have haS : aᴴ * (e • G) = (e • G) * ai := by
      calc aᴴ * (e • G) = aᴴ * (e • G) * (a * ai) := by rw [hai, Matrix.mul_one]
        _ = (aᴴ * (e • G) * a) * ai := by simp only [Matrix.mul_assoc]
        _ = (e • G) * ai := by rw [hSa]
    have hform : (a * A)ᴴ * (e • G) * (a * A) = I := by
      calc (a * A)ᴴ * (e • G) * (a * A) = Aᴴ * (aᴴ * (e • G) * a) * A := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hSa, hA]
    refine ⟨hform, ?_, ?_, ?_⟩
    · calc I * (a * A)ᴴ * (e • G) = I * Aᴴ * (aᴴ * (e • G)) := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = c * ai := by rw [haS, hc]; simp only [Matrix.mul_assoc]
    · calc (c * (a * A))ᴴ * I * (c * (a * A)) = (a * A)ᴴ * (cᴴ * I * c) * (a * A) := by
            rw [conjTranspose_mul c]; simp only [Matrix.mul_assoc]
        _ = I := by rw [hS, hform]
    · have hu : (c * (a * A))ᴴ * (c * (a * A)) = Aᴴ * (aᴴ * (cᴴ * c) * a) * A := by
        rw [conjTranspose_mul c, conjTranspose_mul a]; simp only [Matrix.mul_assoc]
      rw [hu]
      constructor
      · intro h
        calc aᴴ * (cᴴ * c) * a = (cᴴ * Aᴴ) * (aᴴ * (cᴴ * c) * a) * (A * c) := by
              rw [h2h, h2, Matrix.one_mul, Matrix.mul_one]
          _ = cᴴ * (Aᴴ * (aᴴ * (cᴴ * c) * a) * A) * c := by simp only [Matrix.mul_assoc]
          _ = cᴴ * c := by rw [h, Matrix.mul_one]
      · intro h
        calc Aᴴ * (aᴴ * (cᴴ * c) * a) * A = (Aᴴ * cᴴ) * (c * A) := by
              rw [h]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [h1h, h1, Matrix.one_mul]
  · intro A' hA'
    have hX : e • ((A' * c)ᴴ * G * (A' * c)) = e • G := by
      calc e • ((A' * c)ᴴ * G * (A' * c)) = cᴴ * (A'ᴴ * (e • G) * A') * c := by
            rw [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
        _ = e • G := by rw [hA', hS]
    calc (A' * c)ᴴ * G * (A' * c) = e • e • ((A' * c)ᴴ * G * (A' * c)) := (hee _).symm
      _ = G := by rw [hX, hee]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Adapted

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem sgI_mul_self (j j' : ℕ) : sgI j j' * sgI j j' = 1 := by
  simp [sgI, Matrix.fromBlocks_multiply]

theorem cinv_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C τ A hA
  have he : ((C.eps τ : ℝ) : ℂ) * ((C.eps τ : ℝ) : ℂ) = 1 := by
    have h := C.eps_sq τ
    rw [← Complex.ofReal_mul, ← pow_two, h, Complex.ofReal_one]
  exact Adapted.facts finSumFinEquiv.symm (sgI j j') (sgI_mul_self j j') (C.gr τ) ((C.eps τ : ℝ) : ℂ) he A hA
    (C.cinv A τ) rfl

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInversePropertiesStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_inverse_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMul
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem ballMat_ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) (τ : Ψ) :
    ballMat q (ballPt q W) τ = (W τ)ᵀ := by
  ext a b
  simp [ballMat, ballPt]

theorem sgI_form (a : Fin j → ℂ) (b : Fin j' → ℂ) :
    star (Sum.elim a b : Sg j j' → ℂ) ⬝ᵥ (sgI j j' *ᵥ Sum.elim a b) = star a ⬝ᵥ a - star b ⬝ᵥ b := by
  simp [sgI, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, sub_eq_add_neg,
    neg_mulVec, Finset.sum_neg_distrib]

theorem form_mulVec {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) (z : Sg j j' → ℂ) :
    star (v *ᵥ z) ⬝ᵥ (sgI j j' *ᵥ (v *ᵥ z)) = star z ⬝ᵥ (sgI j j' *ᵥ z) := by
  have hv' : vᴴ * sgI j j' * v = sgI j j' := hv
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hv']

theorem norm_lt_of_ball {W : Matrix (Fin j') (Fin j) ℂ} (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) {y : Fin j' → ℂ}
    (hy : y ≠ 0) : (star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y)).re < (star y ⬝ᵥ y).re := by
  have hc : star y ≠ 0 := by simpa using hy
  have h := hW.dotProduct_mulVec_pos hc
  have hw : Wᵀ *ᵥ star y = star (Wᴴ *ᵥ y) := by
    rw [star_mulVec, conjTranspose_conjTranspose, mulVec_transpose]
  have e : star (star y) ⬝ᵥ ((1 - (Wᵀ)ᴴ * Wᵀ) *ᵥ star y) =
      star y ⬝ᵥ y - star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hw, dotProduct_sub, star_star, dotProduct_comm y (star y)]
    congr 1
    rw [dotProduct_mulVec, vecMul_conjTranspose, hw, star_star, dotProduct_comm]
  rw [e] at h
  have := (Complex.lt_def.1 h).1
  simpa using this

theorem isUnit_det_P {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det := by
  by_contra hne
  have h0 : (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det = 0 := by simpa using hne
  obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : v *ᵥ Sum.elim x (W *ᵥ x) =
      Sum.elim (0 : Fin j → ℂ) ((v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks v]
    rw [fromBlocks_mulVec]
    have h1 : v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x) = 0 := by
      rw [← hPx, add_mulVec, mulVec_mulVec]
    show Sum.elim (v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x))
      (v.toBlocks₂₁ *ᵥ x + v.toBlocks₂₂ *ᵥ (W *ᵥ x)) = _
    rw [h1, add_mulVec, mulVec_mulVec]
  have hen := form_mulVec hv (Sum.elim x (W *ᵥ x))
  rw [hz, sgI_form, sgI_form] at hen
  set y := W *ᵥ x with hy
  set Qx := (v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x
  have hxx : 0 < (star x ⬝ᵥ x).re := by
    have := (Complex.lt_def.1 (dotProduct_star_self_pos_iff.2 hx)).1
    simpa using this
  have hQ : 0 ≤ (star Qx ⬝ᵥ Qx).re := (Complex.le_def.1 (dotProduct_star_self_nonneg Qx)).1
  have hre := congrArg Complex.re hen
  simp only [Complex.sub_re, star_zero, dotProduct_zero, Complex.zero_re] at hre
  have hyy : (star x ⬝ᵥ x).re ≤ (star y ⬝ᵥ y).re := by linarith
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hyy
    simp at hyy
    linarith
  have hlt := norm_lt_of_ball hW hy0
  set w := Wᴴ *ᵥ y with hw
  have hnn : 0 ≤ (star (x - w) ⬝ᵥ (x - w)).re :=
    (Complex.le_def.1 (dotProduct_star_self_nonneg (x - w))).1
  have h1 : star x ⬝ᵥ w = star y ⬝ᵥ y := by
    rw [hw, dotProduct_mulVec, hy, star_mulVec]
  have h2 : star w ⬝ᵥ x = star y ⬝ᵥ y := by
    rw [hw, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hexp : star (x - w) ⬝ᵥ (x - w) = star x ⬝ᵥ x - star x ⬝ᵥ w - star w ⬝ᵥ x + star w ⬝ᵥ w := by
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    ring
  rw [hexp, h1, h2] at hnn
  simp only [Complex.add_re, Complex.sub_re] at hnn
  linarith

theorem moebW_mul (u v : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ)
    (hP : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det) :
    moebW (u * v) W = moebW u (moebW v W) := by
  set P := v.toBlocks₁₁ + v.toBlocks₁₂ * W with hPd
  set Q := v.toBlocks₂₁ + v.toBlocks₂₂ * W with hQd
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hv : moebW v W = Q * P⁻¹ := rfl
  have huv : u * v = fromBlocks
      (u.toBlocks₁₁ * v.toBlocks₁₁ + u.toBlocks₁₂ * v.toBlocks₂₁)
      (u.toBlocks₁₁ * v.toBlocks₁₂ + u.toBlocks₁₂ * v.toBlocks₂₂)
      (u.toBlocks₂₁ * v.toBlocks₁₁ + u.toBlocks₂₂ * v.toBlocks₂₁)
      (u.toBlocks₂₁ * v.toBlocks₁₂ + u.toBlocks₂₂ * v.toBlocks₂₂) := by
    rw [← fromBlocks_multiply, fromBlocks_toBlocks, fromBlocks_toBlocks]
  have e1 : (u * v).toBlocks₁₁ + (u * v).toBlocks₁₂ * W =
      (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P = u.toBlocks₁₁ * P + u.toBlocks₁₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₁₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 : (u * v).toBlocks₂₁ + (u * v).toBlocks₂₂ * W =
      (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P = u.toBlocks₂₁ * P + u.toBlocks₂₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₂₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hv]
  unfold moebW
  rw [e1, e2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul]

theorem moebBall_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  intro Ψ _ j j' n q u v hu hv t ht
  unfold moebBall
  congr 1
  funext τ
  rw [ballMat_ballPt, transpose_transpose]
  refine moebW_mul _ _ _ (isUnit_det_P (hv τ) ?_)
  simpa using ht τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMulStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameOfEquivalent
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameOfEquivalent
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

namespace LatEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem perExt_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (y : Ψ → Fin (j + j') → ℂ) : C.perExt R' y = k (C.perExt R y) := by
  have h : C.perExt R' = (k.toLinearMap.restrictScalars ℝ) ∘ₗ C.perExt R := by
    refine C.bas.ext fun i => ?_
    simp [perExt, Module.Basis.constr_basis, hk]
  rw [h]
  rfl

theorem pPart_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pPart R' τ y = k (C.pPart R τ y) := by
  simp only [pPart, C.perExt_of_coord k hk, map_smul, map_sub]

theorem pBar_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pBar R' τ y = k (C.pBar R τ y) := by
  simp only [pBar, C.perExt_of_coord k hk, map_smul, map_add (f := _)]

end LatEmb

theorem isAdapted_of_eqvBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted R A → R.EqvBy R' 1 → C.IsAdapted R' A := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R R' A hA hE
  obtain ⟨k, hk⟩ := hE
  have hk' : ∀ x, R'.P x = k (R.P x) := fun x => hk x
  refine ⟨hA.unit, fun τ v => ?_, fun τ v => ?_⟩
  · rw [C.pPart_of_coord k hk', hA.ker, map_zero]
  · rw [C.pBar_of_coord k hk', hA.kerBar, map_zero]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameOfEquivalentStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_frame_of_equivalent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted R A → R.EqvBy R' 1 → C.IsAdapted R' A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.isAdapted_of_eqvBy <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitive
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitive
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

section Blocks

open scoped MatrixOrder

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem exists_congr_one {A : Matrix a a ℂ} (hA : A.PosDef) : ∃ X : Matrix a a ℂ, Xᴴ * A * X = 1 ∧ IsUnit X.det := by
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hs : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  obtain ⟨C, hCA⟩ : ∃ C : Matrix a a ℂ, A = Cᴴ * C :=
    ⟨CFC.sqrt A, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self A h0]⟩
  have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 hA.isUnit
  have hC : IsUnit C.det := by
    rw [hCA, Matrix.det_mul] at hd
    exact isUnit_of_mul_isUnit_right hd
  have h1 : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hC
  refine ⟨C⁻¹, ?_, ?_⟩
  · calc (C⁻¹)ᴴ * A * C⁻¹ = (C * C⁻¹)ᴴ * (C * C⁻¹) := by
          rw [hCA, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp
  · exact (Matrix.isUnit_nonsing_inv_det_iff).2 hC

theorem posDef_one_sub_swap {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) : (1 - Wᴴ * W).PosDef := by
  set B := 1 - W * Wᴴ with hB
  have hBu : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det _).1 h.isUnit
  have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hBu
  have hP : (1 + Wᴴ * B⁻¹ * W).PosDef :=
    Matrix.PosDef.one.add_posSemidef (h.inv.posSemidef.conjTranspose_mul_mul_same W)
  have hinv : (1 + Wᴴ * B⁻¹ * W) * (1 - Wᴴ * W) = 1 := by
    have e2 : W * Wᴴ = 1 - B := by rw [hB]; abel
    have e : Wᴴ * B⁻¹ * W * (Wᴴ * W) = Wᴴ * B⁻¹ * (W * Wᴴ) * W := by simp only [Matrix.mul_assoc]
    have e3 : Wᴴ * B⁻¹ * (1 - B) * W = Wᴴ * B⁻¹ * W - Wᴴ * W := by
      have hBi' : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hBu
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc (Wᴴ) (B⁻¹) B, hBi', Matrix.mul_one]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, e, e2, e3]
    abel
  have : (1 - Wᴴ * W) = (1 + Wᴴ * B⁻¹ * W)⁻¹ := (Matrix.inv_eq_right_inv hinv).symm
  rw [this]
  exact hP.inv

theorem exists_boost {W : Matrix b a ℂ} (h : (1 - W * Wᴴ).PosDef) :
    ∃ u : Matrix (a ⊕ b) (a ⊕ b) ℂ,
      uᴴ * fromBlocks 1 0 0 (-1) * u = fromBlocks 1 0 0 (-1) ∧ u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ = W := by
  obtain ⟨X, hX, hXu⟩ := exists_congr_one (posDef_one_sub_swap h)
  obtain ⟨Y, hY, -⟩ := exists_congr_one h
  refine ⟨fromBlocks X (Wᴴ * Y) (W * X) Y, ?_, ?_⟩
  · have e11 : Xᴴ * X - Xᴴ * Wᴴ * (W * X) = 1 := by
      rw [← hX, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    have e22 : Yᴴ * W * (Wᴴ * Y) - Yᴴ * Y = -1 := by
      rw [← hY, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
      abel
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.mul_neg, add_zero, zero_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.neg_mul]
    congr 1
    · simp only [Matrix.mul_assoc, add_neg_cancel]
    · simp only [Matrix.mul_assoc, add_neg_cancel]
  · have : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hXu
    simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁]
    rw [Matrix.mul_assoc, this, Matrix.mul_one]

end Blocks

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Boost

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem moebBall_transitive : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q → ∃ u : Ψ → Matrix (Sg j j') (Sg j j') ℂ, (∀ τ, IsSgU (u τ)) ∧ moebBall q u 0 = t := by
  intro Ψ _ j j' n q t ht
  have hW : ∀ τ, (1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ).PosDef := by
    intro τ
    have h := (ht τ).transpose
    have e : (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ = 1 - (ballMat q t τ)ᵀ * ((ballMat q t τ)ᵀ)ᴴ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]
      congr 2
    rwa [e] at h
  choose u hu hm using fun τ => Boost.exists_boost (hW τ)
  refine ⟨u, hu, ?_⟩
  have h0 : ∀ τ, moebW (u τ) (ballMat q 0 τ)ᵀ = (ballMat q t τ)ᵀ := by
    intro τ
    have hz : ballMat q 0 τ = 0 := by
      ext a b
      simp [ballMat]
    rw [hz, moebW, Matrix.transpose_zero, Matrix.mul_zero, Matrix.mul_zero, add_zero, add_zero]
    exact hm τ
  funext k
  simp only [moebBall, ballPt, h0]
  simp [ballMat]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitiveStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_mobius_transitive : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ), t ∈ ballDom q → ∃ u : Ψ → Matrix (Sg j j') (Sg j j') ℂ, (∀ τ, IsSgU (u τ)) ∧ moebBall q u 0 = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.moebBall_transitive <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignature
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignature
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim

theorem ringHom_injective {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun f : E →+* ℂ => f.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro f f' h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · intro s
    refine ⟨IsFractionRing.lift (ringHom_injective s), ?_⟩
    ext a
    simp

theorem natCard_ringHom (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card]
  exact NumberField.Embeddings.card E ℂ

def both {E Ψ : Type} [Field E] [NumberField E] (σ : Ψ → (𝓞 E →+* ℂ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ) :=
  Sum.elim σ fun τ => (starRingEnd ℂ).comp (σ τ)

theorem conj_conj_comp {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem both_bijective {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Function.Bijective (both σ) := by
  have hconj : Function.Injective fun s : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp s := by
    intro s t hst
    have := congrArg (fun u : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp u) hst
    simpa only [conj_conj_comp] using this
  have hcross : ∀ τ τ', σ τ ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' e
    exact ((h.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, e⟩
  constructor
  · rintro (τ | τ) (τ' | τ') e
    · exact congrArg Sum.inl (h.1 e)
    · exact absurd e (hcross τ τ')
    · exact absurd e.symm (hcross τ' τ)
    · exact congrArg Sum.inr (h.1 (hconj e))
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have h' : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hn
        exact hs ((h.2 s).2 hn)
      obtain ⟨τ, e⟩ := h'
      refine ⟨Sum.inr τ, ?_⟩
      show (starRingEnd ℂ).comp (σ τ) = s
      rw [e, conj_conj_comp]

theorem card_sum_eq_finrank {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
  rw [← natCard_ringHom E, ← Nat.card_congr (Equiv.ofBijective _ (both_bijective h)), Nat.card_eq_fintype_card]

theorem eigSp_le_eigenspace {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (s : 𝓞 E →+* ℂ) (θ : 𝓞 E) :
    eigSp B s ≤ Module.End.eigenspace (B θ) (s θ) := by
  intro x hx
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx θ

theorem iSupIndep_eigSp {E V ι : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (σ : ι → (𝓞 E →+* ℂ)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp B (σ s) := by
  obtain ⟨θ, m, -, -, -, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* ℂ) (P : Polynomial ℤ), τ (Polynomial.aeval θ P) = Polynomial.aeval (τ θ) P := fun τ P =>
    (Polynomial.aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  exact ((Module.End.eigenspaces_iSupIndep (B θ)).comp hinj).mono fun s => eigSp_le_eigenspace B (σ s) θ

theorem dim_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g j j' : ℕ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → (∀ τ, Module.finrank ℂ (eigSp B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp B ((starRingEnd ℂ).comp (σ τ))) = j) → g = Fintype.card Ψ * (j + j') := by
  intro E _ _ _ Ψ _ g j j' B σ hσ hdim
  classical
  have hb := both_bijective hσ
  have htop := iSup_eigSp_eq_top B (both σ) hb.1 (card_sum_eq_finrank hσ)
  have hind := iSupIndep_eigSp B (both σ) hb.1
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun s => eigSp B (both σ s)) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun, Fintype.sum_sum_type] at e
  have h1 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inl τ))) = j' := fun τ => (hdim τ).1
  have h2 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inr τ))) = j := fun τ => (hdim τ).2
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at e
  rw [← e]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignatureStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_eq_card_mul_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g j j' : ℕ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → (∀ τ, Module.finrank ℂ (eigSp B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp B ((starRingEnd ℂ).comp (σ τ))) = j) → g = Fintype.card Ψ * (j + j') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim.dim_eq_card_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImage
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImage
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem exists_bigZe_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ) (hs : Zᵀ = Z)
    (hZ : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) :
    ∃ t, bigZe e q t = Z := by
  have hz : ∀ i k, ¬ ((e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → Z i k = 0 :=
    fun i k h => by_contra fun h0 => h (hZ i k h0)
  have hsym : ∀ i k, Z i k = Z k i := fun i k => by
    have := congrFun (congrFun hs k) i
    simpa [Matrix.transpose_apply] using this
  let t : Fin n → ℂ := fun m => Z (e (Sum.inr (q.symm m).2.1, (q.symm m).1)) (e (Sum.inl (q.symm m).2.2, (q.symm m).1))
  have hb : ∀ τ a b, ballMat q t τ a b = Z (e (Sum.inr a, τ)) (e (Sum.inl b, τ)) := by
    intro τ a b
    simp [ballMat, t]
  refine ⟨t, ?_⟩
  ext i k
  obtain ⟨⟨x, τ⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨y, τ'⟩, rfl⟩ := e.surjective k
  simp only [bigZe, bigZ, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  by_cases hτ : τ = τ'
  · subst hτ
    rw [Matrix.blockDiagonal_apply_eq]
    rcases x with a | a <;> rcases y with b | b
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.transpose_apply, hb, hsym]
    · rw [Matrix.fromBlocks_apply₂₁, hb]
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hτ]
    exact (hz _ _ (by simp [hτ])).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImageStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_pattern_matrix_mem_range_bigZe : ∀ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ), Zᵀ = Z → (∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → ∃ t, bigZe e q t = Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.exists_bigZe_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesAction
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesAction
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem emb_mul_bigZ {E : Type} [Field E] [NumberField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ}
    (σ : Ψ → (𝓞 E →+* ℂ)) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (a : 𝓞 E) (i k : Ix Ψ j j') :
    emb σ i a * bigZ q t i k = bigZ q t i k * star (emb σ k a) := by
  obtain ⟨i1, τ⟩ := i
  obtain ⟨k1, τ'⟩ := k
  by_cases h : τ = τ'
  · subst h
    rcases i1 with i1 | i1 <;> rcases k1 with k1 | k1 <;>
      simp [bigZ, emb, blockDiagonal_apply, mul_comm]
  · simp [bigZ, blockDiagonal_apply_ne _ _ _ h]

theorem tz_bigZe_comm : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  intro E _ _ _ Ψ _ _ j j' n g σ e q t B _ hB a x
  funext i
  have hsub : B a (tz (bigZe e q t) x) i
      = B a x i - B a (bigZe e q t *ᵥ star x) i := by
    simp only [tz, map_sub, Pi.sub_apply]
  rw [hsub]
  simp only [tz, Pi.sub_apply]
  congr 1
  rw [hB a (bigZe e q t *ᵥ star x) i]
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := emb_mul_bigZ σ q t a (e.symm i) (e.symm k)
  have hx : star (B a x) k = star (emb σ (e.symm k) a) * star (x k) := by
    simp [hB, mul_comm]
  rw [hx, ← mul_assoc, ← mul_assoc]
  simp only [bigZe, submatrix_apply, Pi.star_apply]
  rw [hk]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelTransformCommutesActionStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_transform_commutes_action : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)), IsCMFam σ → (∀ a x k, B a x k = emb σ (e.symm k) a * x k) → ∀ a x, tz (bigZe e q t) (B a x) = B a (tz (bigZe e q t) x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | exact GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Univ.tz_bigZe_comm <;> assumption)
end
end
