module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitary

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrame
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_coeff_of_linearIndependent (n m g : ℕ) (U : Set (Fin n → ℂ))
    (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ)
    (w : (Fin n → ℂ) → Fin m → ℂ) (hU : IsOpen U)
    (hd : ∀ b, DifferentiableOn ℂ (d b) U) (hx : DifferentiableOn ℂ x U)
    (hli : ∀ t ∈ U, LinearIndependent ℂ (fun b => d b t))
    (hw : ∀ t ∈ U, x t = ∑ b, w t b • d b t) : DifferentiableOn ℂ w U := by
  intro t₀ ht₀
  apply DifferentiableAt.differentiableWithinAt
  have hUn : U ∈ 𝓝 t₀ := hU.mem_nhds ht₀

  let φ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ (fun b => d b t₀)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have h0 := Fintype.linearIndependent_iff.1 (hli t₀ ht₀) v
      (by simpa [φ, Fintype.linearCombination_apply] using hv)
    exact funext h0
  obtain ⟨L0, hL0⟩ := φ.exists_leftInverse_of_injective hφ
  let L : (Fin g → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap L0
  have hLd : ∀ b, L (d b t₀) = Pi.single b 1 := by
    intro b
    have h1 : φ (Pi.single b 1) = d b t₀ := by
      simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
    have h2 := LinearMap.congr_fun hL0 (Pi.single b 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, h1] at h2
    exact h2
  let T : (Fin n → ℂ) → ((Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) := fun t =>
    ∑ b, (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))
  have hTapply : ∀ t v, T t v = ∑ b, v b • L (d b t) := by
    intro t v
    simp [T, ContinuousLinearMap.sum_apply]
  have hT0 : T t₀ = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    rw [hTapply]
    simp only [hLd]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hTd : DifferentiableAt ℂ T t₀ := by
    have hb : ∀ b ∈ (Finset.univ : Finset (Fin m)), DifferentiableAt ℂ (fun t =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b).smulRight (L (d b t))) t₀ := by
      intro b _
      exact (ContinuousLinearMap.smulRightL ℂ (Fin m → ℂ) (Fin m → ℂ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) b)).differentiableAt.comp t₀
        (L.differentiableAt.comp t₀ ((hd b).differentiableAt hUn))
    exact DifferentiableAt.fun_sum hb
  have hTu : ∀ᶠ t in 𝓝 t₀, IsUnit (T t) := by
    have hc : ContinuousAt T t₀ := hTd.continuousAt
    have : {u : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ) | IsUnit u} ∈ 𝓝 (T t₀) := by
      rw [hT0]
      exact Units.isOpen.mem_nhds isUnit_one
    exact hc this
  have heq : w =ᶠ[𝓝 t₀] fun t => Ring.inverse (T t) (L (x t)) := by
    filter_upwards [hTu, hUn] with t hu ht
    obtain ⟨u, hu'⟩ := hu
    have h1 : L (x t) = T t (w t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hw t ht, hTapply, map_sum]
      simp
    rw [h1, ← hu', Ring.inverse_unit, ← ContinuousLinearMap.mul_apply, u.inv_mul]
    rfl
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hinv : DifferentiableAt ℂ (fun t => Ring.inverse (T t)) t₀ := by
    have : DifferentiableAt ℂ Ring.inverse (T t₀) := by
      rw [hT0]
      exact differentiableAt_inverse isUnit_one
    exact this.comp t₀ hTd
  have hLx : DifferentiableAt ℂ (fun t => L (x t)) t₀ :=
    L.differentiableAt.comp t₀ (hx.differentiableAt hUn)
  exact hinv.clm_apply hLx

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicCoefficientsInFrameStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_coefficients_in_frame : ∀ (n m g : ℕ) (U : Set (Fin n → ℂ)) (d : Fin m → (Fin n → ℂ) → Fin g → ℂ) (x : (Fin n → ℂ) → Fin g → ℂ) (w : (Fin n → ℂ) → Fin m → ℂ), IsOpen U → (∀ b, DifferentiableOn ℂ (d b) U) → DifferentiableOn ℂ x U → (∀ t ∈ U, LinearIndependent ℂ (fun b => d b t)) → (∀ t ∈ U, x t = ∑ b, w t b • d b t) → DifferentiableOn ℂ w U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.differentiableOn_coeff_of_linearIndependent <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZero
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZero
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex

theorem re_star_dotProduct_self {κ : Type} [Fintype κ] (w : κ → ℂ) :
    (star w ⬝ᵥ w).re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star (w i) * w i).re = Complex.normSq (w i) := by
    simp [Complex.normSq_apply]
  rw [this, Complex.normSq_eq_norm_sq]

theorem re_form_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) (v : κ' → ℂ) :
    (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re = ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
  have h : star v ⬝ᵥ ((Zᴴ * Z) *ᵥ v) = star (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h, Complex.sub_re,
    re_star_dotProduct_self, re_star_dotProduct_self]

theorem posDef_iff {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ ∀ v : κ' → ℂ, v ≠ 0 → ‖WithLp.toLp 2 (Z *ᵥ v)‖ < ‖WithLp.toLp 2 v‖ := by
  have hH : (1 - Zᴴ * Z).IsHermitian :=
    (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)
  constructor
  · intro h v hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv)).1
    have h0 : (0 : ℝ) < ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
      rw [← re_form_eq]
      simpa using hpos
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (sub_pos.mp h0)
  · intro h
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun v hv => ?_⟩
    have hre : 0 < (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re := by
      rw [re_form_eq, sub_pos]
      exact pow_lt_pow_left₀ (h v hv) (norm_nonneg _) two_ne_zero
    have hstar : star (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)) = star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v) := by
      conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
    have him : (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem ballMat_combo {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (s t : Fin n → ℂ) (a b : ℝ) (τ : Ψ) :
    ballMat q (a • s + b • t) τ = a • ballMat q s τ + b • ballMat q t τ := by
  ext x y
  simp [ballMat]

theorem convex_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) [Fintype Ψ] :
    Convex ℝ (ballDom q) := by
  intro s hs t ht a b ha hb hab τ
  refine (posDef_iff _).mpr fun v hv => ?_
  have h1 := (posDef_iff _).mp (hs τ) v hv
  have h2 := (posDef_iff _).mp (ht τ) v hv
  have hc := convex_ball (0 : EuclideanSpace ℂ (Fin j)) ‖WithLp.toLp 2 v‖
    (x := WithLp.toLp 2 (ballMat q s τ *ᵥ v)) (y := WithLp.toLp 2 (ballMat q t τ *ᵥ v))
    (by simpa using h1) (by simpa using h2) ha hb hab
  have he : WithLp.toLp 2 (ballMat q (a • s + b • t) τ *ᵥ v) =
      a • WithLp.toLp 2 (ballMat q s τ *ᵥ v) + b • WithLp.toLp 2 (ballMat q t τ *ᵥ v) := by
    rw [ballMat_combo, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    rfl
  rw [he]
  simpa using hc

theorem zero_mem_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have h : ballMat q (0 : Fin n → ℂ) τ = 0 := by
    ext x y
    simp [ballMat]
  rw [h]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin j') (Fin j') ℂ).PosDef)

theorem ballDom_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n),
    IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q :=
  fun _ _ _ _ _ q => ⟨BallInverse.isOpen_ballDom q, convex_ballDom q, zero_mem_ballDom q⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZeroStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_domain_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCount
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCount
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem dim_eq_of_holo_inverse {a b : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas a X) (B : FinHolAtlas b Y) (f : X → Y) (g : Y → X)
    (hf : HoloMap A B f) (hg : HoloMap B A g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (x : X) :
    a = b := by
  obtain ⟨j, hj⟩ := A.cover x
  obtain ⟨k, hk⟩ := B.cover (f x)
  have hu_t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hw_t : B.chart k (f x) ∈ (B.chart k).target := (B.chart k).map_source hk
  have hsu : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hsw : (B.chart k).symm (B.chart k (f x)) = f x := (B.chart k).left_inv hk
  let F : (Fin a → ℂ) → (Fin b → ℂ) := B.chart k ∘ f ∘ (A.chart j).symm
  let G : (Fin b → ℂ) → (Fin a → ℂ) := A.chart j ∘ g ∘ (B.chart k).symm
  have hFu : F (A.chart j x) = B.chart k (f x) := by
    show B.chart k (f ((A.chart j).symm (A.chart j x))) = _
    rw [hsu]
  have hGw : G (B.chart k (f x)) = A.chart j x := by
    show A.chart j (g ((B.chart k).symm (B.chart k (f x)))) = _
    rw [hsw, hgf]
  have dF : DifferentiableAt ℂ F (A.chart j x) :=
    (hf.2 j k _ ⟨hu_t, by
      show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
      rw [hsu]; exact hk⟩).differentiableAt
  have dG : DifferentiableAt ℂ G (B.chart k (f x)) :=
    (hg.2 k j _ ⟨hw_t, by
      show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
      rw [hsw, hgf]; exact hj⟩).differentiableAt
  have e1 : G ∘ F =ᶠ[𝓝 (A.chart j x)] id := by
    have c : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
      hf.1.continuousAt.comp ((A.chart j).continuousAt_symm hu_t)
    have hs : ∀ᶠ v in 𝓝 (A.chart j x), (f ∘ (A.chart j).symm) v ∈ (B.chart k).source :=
      c.eventually ((B.chart k).open_source.mem_nhds (by
        show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
        rw [hsu]; exact hk))
    filter_upwards [hs, (A.chart j).open_target.mem_nhds hu_t] with v h1 h2
    have h1' : f ((A.chart j).symm v) ∈ (B.chart k).source := h1
    show A.chart j (g ((B.chart k).symm (B.chart k (f ((A.chart j).symm v))))) = v
    rw [(B.chart k).left_inv h1', hgf, (A.chart j).right_inv h2]
  have e2 : F ∘ G =ᶠ[𝓝 (B.chart k (f x))] id := by
    have c : ContinuousAt (g ∘ (B.chart k).symm) (B.chart k (f x)) :=
      hg.1.continuousAt.comp ((B.chart k).continuousAt_symm hw_t)
    have hs : ∀ᶠ v in 𝓝 (B.chart k (f x)), (g ∘ (B.chart k).symm) v ∈ (A.chart j).source :=
      c.eventually ((A.chart j).open_source.mem_nhds (by
        show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
        rw [hsw, hgf]; exact hj))
    filter_upwards [hs, (B.chart k).open_target.mem_nhds hw_t] with v h1 h2
    have h1' : g ((B.chart k).symm v) ∈ (A.chart j).source := h1
    show B.chart k (f ((A.chart j).symm (A.chart j (g ((B.chart k).symm v))))) = v
    rw [(A.chart j).left_inv h1', hfg, (B.chart k).right_inv h2]
  have d1 : (fderiv ℂ G (B.chart k (f x))).comp (fderiv ℂ F (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    have dG' : DifferentiableAt ℂ G (F (A.chart j x)) := by rw [hFu]; exact dG
    have h := fderiv_comp (A.chart j x) dG' dF
    rw [e1.fderiv_eq, fderiv_id, hFu] at h
    exact h.symm
  have d2 : (fderiv ℂ F (A.chart j x)).comp (fderiv ℂ G (B.chart k (f x))) = ContinuousLinearMap.id ℂ _ := by
    have dF' : DifferentiableAt ℂ F (G (B.chart k (f x))) := by rw [hGw]; exact dF
    have h := fderiv_comp (B.chart k (f x)) dF' dG
    rw [e2.fderiv_eq, fderiv_id, hGw] at h
    exact h.symm
  let E : (Fin a → ℂ) ≃ₗ[ℂ] (Fin b → ℂ) := LinearEquiv.ofLinearMap
    (fderiv ℂ F (A.chart j x) : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    (fderiv ℂ G (B.chart k (f x)) : (Fin b → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (LinearMap.ext fun v => congrArg (fun L : (Fin b → ℂ) →L[ℂ] (Fin b → ℂ) => L v) d2)
    (LinearMap.ext fun v => congrArg (fun L : (Fin a → ℂ) →L[ℂ] (Fin a → ℂ) => L v) d1)
  simpa using E.finrank_eq

theorem dim_eq_of_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {a b : ℕ}
    (R : AnLogRes P ⊤ a) (hJ : J = ⊤) (R' : AnLogRes P J b) (x : R'.X) : a = b := by
  subst hJ
  have hP : P ≤ imageZ id P := fun f hf => by
    show rename id f ∈ P
    rwa [rename_id_apply]
  obtain ⟨h, hh, ho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ a b R R' isBlockMap_id hP
  obtain ⟨g, hg, go⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ b a R' R isBlockMap_id hP
  have hemp : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun z hz => by
    have := hz.2 1 trivial
    simp at this
  have hgh : ∀ x, g (h x) = x := fun x => R'.inj _ _ (hemp _) (orbit_trans (go (h x)) (ho x))
  have hhg : ∀ x, h (g x) = x := fun x => R.inj _ _ (hemp _) (orbit_trans (ho (g x)) (go x))
  exact dim_eq_of_holo_inverse R.A R'.A g h hg hh hhg hgh (h x)

theorem flagAn_dim : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hk : ∀ k, k ∈ Set.range (id : K → K) ↔
      ((∀ p, M.blk p ≠ some k) ∨ ∃ p, (fun _ : Ψ × Fin N => True) p ∧ M.blk p = some k) := fun k =>
    ⟨fun _ => by
      by_cases h : ∀ p, M.blk p ≠ some k
      · exact Or.inl h
      · obtain ⟨p, hp⟩ := not_forall.1 h
        exact Or.inr ⟨p, trivial, not_not.1 hp⟩, fun _ => ⟨k, rfl⟩⟩
  obtain ⟨e, R, he, -⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n _ BM.Rb rfl (fun _ => True) K ι id id isBlockMap_id hk
  have R2 : AnLogRes (mCoordIdeal y) ⊤ e := R
  obtain ⟨z, hz, hJ⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts FA.Re.arith FA.Re.R.nondeg
  obtain ⟨x, -⟩ := FA.Re.R.surj z hz hJ
  rw [← he fun _ => trivial]
  exact (dim_eq_of_res R2 FA.J_top FA.Re.R x).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticDimensionCountStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_analytic_dimension_count : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.flagAn_dim <;> assumption)
end
end
