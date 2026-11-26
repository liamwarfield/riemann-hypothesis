module

public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUnimodDiv
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPeriod

open GlobalTheory.SiegelNormalForm Matrix

theorem exists_siegel_form : ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, EF (bas a) (bas b) = omegaStd a b) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → ∃ h τ : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ h⁻¹ = (Matrix.of fun i j => Q (bas (Pi.single (.inr j) 1)) i) ∧ τ = h * (Matrix.of fun i j => Q (bas (Pi.single (.inl j) 1)) i) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ z w, hermForm Hm z w = hermForm (((τ.map Complex.im)⁻¹).map Complex.ofReal) (h.mulVec z) (h.mulVec w)) ∧ ∀ a, h.mulVec (Q (bas a)) = τ.mulVec (fun i => (a (.inl i) : ℂ)) + fun i => (a (.inr i) : ℂ) := by
  intro La _ EF g bas Q Hm hbas ⟨_, _, _, hH, hpos, hE⟩
  unfold hermForm at hpos hE ⊢
  set e : Fin g → Fin g → ℂ := fun i => Q (bas (Pi.single (.inr i) 1)) with he
  set f : Fin g → Fin g → ℂ := fun i => Q (bas (Pi.single (.inl i) 1)) with hf
  have hee : ∀ i j, (e i ⬝ᵥ Hm *ᵥ star (e j)).im = 0 := fun i j => by
    simp only [he]
    rw [hE, hbas]; simp [omegaStd]
  have hff : ∀ i j, (f i ⬝ᵥ Hm *ᵥ star (f j)).im = 0 := fun i j => by
    simp only [hf]
    rw [hE, hbas]; simp [omegaStd]
  have hef : ∀ i j, (e i ⬝ᵥ Hm *ᵥ star (f j)).im = if i = j then -1 else 0 := fun i j => by
    simp only [he, hf]
    rw [hE, hbas]
    by_cases hij : i = j
    · subst hij; simp [omegaStd, Pi.single_apply]
    · simp [omegaStd, Pi.single_apply, hij, Ne.symm hij]
  let P : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => e i k
  let F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k i => f i k
  have hP : ∀ i, P *ᵥ Pi.single i 1 = e i := fun i => by
    ext k; simp [P]
  have hF : ∀ i, F *ᵥ Pi.single i 1 = f i := fun i => by
    ext k; simp [F]
  let Y : Matrix (Fin g) (Fin g) ℝ := (Pᵀ * Hm * P.map star).map Complex.re
  have hYe : ∀ i j, (Pᵀ * Hm * P.map star) i j = e i ⬝ᵥ Hm *ᵥ star (e j) := fun i j => by
    rw [← form_single (Pᵀ * Hm * P.map star), ← form_pull, hP, hP]
  have hY : Pᵀ * Hm * P.map star = Y.map (↑) := by
    ext i j
    apply Complex.ext
    · simp [Y]
    · rw [hYe, hee]; simp
  have hPu : IsUnit P := isUnit_of_lagrangian P Hm f hpos Y hY
    (fun i j => by rw [hP, hef])
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hPi : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.2 hPu
  have hPP : ∀ z, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv P hPd, Matrix.one_mulVec]
  let τ : Matrix (Fin g) (Fin g) ℂ := P⁻¹ * F
  have hPτ : ∀ z, P *ᵥ (τ *ᵥ z) = F *ᵥ z := fun z => by
    rw [← Matrix.mulVec_mulVec, hPP]
  have hτ : ∀ j, P *ᵥ (τ *ᵥ Pi.single j 1) = f j := fun j => by
    rw [hPτ, hF]
  have hform : ∀ z w, (P *ᵥ z) ⬝ᵥ Hm *ᵥ star (P *ᵥ w) = z ⬝ᵥ Y.map (↑) *ᵥ star w :=
    fun z w => by rw [form_pull, hY]
  have hYs : Yᵀ = Y := by
    ext i j
    have := congrArg Complex.re (form_conj hH (e i) (e j))
    simp only [Complex.star_def, Complex.conj_re] at this
    simp only [Y, Matrix.transpose_apply, Matrix.map_apply, hYe, this]
  have hYp : Y.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hYs) ?_
    intro a ha
    have hne : P *ᵥ (fun i => (a i : ℂ)) ≠ 0 := by
      intro h0
      have := hPi (h0.trans (Matrix.mulVec_zero P).symm)
      exact ha (funext fun i => by simpa using congrFun this i)
    have := hpos _ hne
    rw [hform] at this
    simpa [Matrix.mulVec, dotProduct] using this
  obtain ⟨hτs, hτp, hYτ⟩ := siegel_of_relations Y hYp τ
    (fun i j => by rw [← hform, hP, hτ, hef]) (fun i j => by rw [← hform, hτ, hτ, hff])
  have hYi : (τ.map Complex.im)⁻¹ = Y := Matrix.inv_eq_left_inv hYτ
  refine ⟨P⁻¹, τ, Matrix.isUnit_nonsing_inv_iff.2 hPu, Matrix.nonsing_inv_nonsing_inv P hPd, rfl,
    hτs, hτp, fun z w => ?_, fun a => hPi ?_⟩
  · rw [hYi, ← hform, hPP, hPP]
  · have h1 : ∀ m : Fin g → ℤ, (fun i => (m i : ℂ)) = ∑ i, m i • (Pi.single i 1 : Fin g → ℂ) := by
      intro m; ext k; simp [Finset.sum_apply, Pi.single_apply]
    have h2 : a = ∑ i, a (.inl i) • Pi.single (.inl i) 1 + ∑ i, a (.inr i) • Pi.single (.inr i) 1 := by
      ext k; rcases k with k | k <;> simp [Finset.sum_apply, Pi.single_apply]
    rw [hPP, h1 (fun i => a (.inl i)), h1 (fun i => a (.inr i))]
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, hP, hτ]
    conv_lhs => rw [h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_zsmul, he, hf]

end GlobalTheory.SiegelPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SubfieldChart


open Filter Topology in
theorem exists_finite_test {A : Type} {e : A → ℂ} {N : Set (A → ℂ)} (hN : N ∈ 𝓝 e) :
    ∃ (n : ℕ) (r : Fin n → A) (ε : ℝ), 0 < ε ∧ ∀ u : A → ℂ, (∀ i, ‖u (r i) - e (r i)‖ < ε) → u ∈ N := by
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  obtain ⟨n, r, hr⟩ := hI.fin_param
  have h1 : Set.pi Set.univ (fun i => t (r i)) ∈ 𝓝 (fun i => e (r i)) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ht (r i)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 h1
  refine ⟨n, r, ε, hε, fun u hu => hsub fun a ha => ?_⟩
  rw [← hr.2] at ha
  obtain ⟨i, rfl⟩ := ha
  refine hb (a := fun i => u (r i)) ?_ i trivial
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro j
  rw [dist_eq_norm]
  exact hu j

section Ring

variable {k A : Type} [Field k] [Algebra k ℂ] [CommRing A] [Algebra k A]

def extPt (x : A →ₐ[k] ℂ) : ℂ ⊗[k] A →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) x fun _ _ => Commute.all _ _

def resPt (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) : A →ₐ[k] ℂ :=
  (z.restrictScalars k).comp Algebra.TensorProduct.includeRight

theorem extPt_tmul (x : A →ₐ[k] ℂ) (c : ℂ) (a : A) : extPt x (c ⊗ₜ a) = c * x a := by
  simp [extPt]

theorem resPt_apply (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) (a : A) : resPt z a = z (1 ⊗ₜ a) := rfl

theorem resPt_extPt (x : A →ₐ[k] ℂ) : resPt (extPt x) = x := by
  ext a
  rw [resPt_apply, extPt_tmul, _root_.one_mul]

theorem extPt_resPt (z : ℂ ⊗[k] A →ₐ[ℂ] ℂ) : extPt (resPt z) = z := by
  ext a
  simp [extPt_tmul, resPt_apply]

theorem exists_continuous_extPt (t : ℂ ⊗[k] A) :
    ∃ F : (A → ℂ) → ℂ, Continuous F ∧ ∀ x : A →ₐ[k] ℂ, F x = extPt x t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨fun _ => 0, continuous_const, fun x => by simp⟩
  | tmul c a => exact ⟨fun u => c * u a, by fun_prop, fun x => (extPt_tmul x c a).symm⟩
  | add s t hs ht =>
    obtain ⟨F, hF, hF'⟩ := hs
    obtain ⟨G, hG, hG'⟩ := ht
    exact ⟨fun u => F u + G u, hF.add hG, fun x => by simp [hF', hG']⟩

theorem exists_chart_algebra (d : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension d k A]
    (e : A →ₐ[k] ℂ) :
    ∃ (W : Set (Fin d → ℂ)) (p : (Fin d → ℂ) → (A →ₐ[k] ℂ)) (n : ℕ) (r : Fin n → A) (ε : ℝ),
      IsOpen W ∧ 0 ∈ W ∧ p 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => p w a) W) ∧
      Set.InjOn p W ∧ ∀ x : A →ₐ[k] ℂ, (∀ i, ‖x (r i) - e (r i)‖ < ε) → ∃ w ∈ W, x = p w := by
  have hc : (algebraMap ℂ (ℂ ⊗[k] A)).IsStandardSmoothOfRelativeDimension d :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap d).2 inferInstance
  obtain ⟨φ, hφc, hφ, hφ0⟩ := HolChart.exists_etale_coords_vanishing _ hc (extPt e).toRingHom
    (fun a => (extPt e).commutes a)
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin d) ℂ) (ℂ ⊗[k] A) := hφ
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ :=
    exists_holomorphic_section_of_etale d (ℂ ⊗[k] A) (extPt e) hφ0
  choose F hF hF' using fun j => exists_continuous_extPt (f j)
  have hN : {u : A → ℂ | ∀ j, ‖F j u - extPt e (f j)‖ < ε} ∈ nhds (e : A → ℂ) := by
    refine IsOpen.mem_nhds ?_ fun j => ?_
    · rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun j =>
        isOpen_lt (((hF j).sub continuous_const).norm) continuous_const
    · rw [hF', sub_self, norm_zero]; exact hε
  obtain ⟨m, r, δ, hδ, hr⟩ := exists_finite_test hN
  refine ⟨W, fun w => resPt (σ w), m, r, δ, hW, hW0, ?_, hδ, fun a => hσd (1 ⊗ₜ a), ?_, ?_⟩
  · show resPt (σ 0) = e
    rw [hσ0, resPt_extPt]
  · intro w hw w' hw' h
    have h1 : σ w = σ w' := by
      rw [← extPt_resPt (σ w), ← extPt_resPt (σ w')]
      exact congrArg extPt h
    funext i
    rw [← hσt w hw i, h1, hσt w' hw' i]
  · intro x hx
    obtain ⟨w, hw, h⟩ := hσs (extPt x) fun j => by
      rw [← hF']; exact hr x hx j
    exact ⟨w, hw, (resPt_extPt x).symm.trans (congrArg resPt h)⟩

end Ring

theorem exists_holomorphic_chart :
    ∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀ : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X, U)), IsOpen B ∧ (0 : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B := by
  intro k _ σ X s d y₀ hX hy₀
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (y₀ (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : s (y₀ (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = s (y₀ (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : k →+* Γ(X, U) :=
    (s.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  have hc : c.IsStandardSmoothOfRelativeDimension d :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (s.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hsm
  let _ : Algebra k ℂ := σ.toAlgebra
  let _ : Algebra k Γ(X, U) := c.toAlgebra
  have _ : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, U) := hc
  let pt : (Γ(X, U) →+* ℂ) → (Sp ℂ ⟶ X) := fun e =>
    Spec.map (CommRingCat.ofHom e : Γ(X, U) ⟶ CommRingCat.of ℂ) ≫ hU.fromSpec
  have hptU : ∀ e, ⊤ ≤ pt e ⁻¹ᵁ U := fun e p _ => hU.range_fromSpec.le ⟨_, rfl⟩
  have hptv : ∀ e f, valAt' (pt e) U f = e f := fun e f => by
    rw [valAt', dite_eq_left (hptU e)]
    exact congrArg (fun ψ => ψ.hom f)
      (AffinePointValues.appLE_specMap_fromSpec hU (CommRingCat.ofHom e) (hptU e))
  have hpts : ∀ e, pt e ≫ s = spMap (e.comp c) := fun e => by
    simp only [pt]
    rw [Category.assoc, AffinePointValues.fromSpec_comp hU s hle, ← Spec.map_comp]
    rfl
  have hsurj : ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U →
      ∃ e : Γ(X, U) →ₐ[k] ℂ, pt e.toRingHom = x := by
    intro x hxs hx
    let e : Γ(X, U) →+* ℂ := (x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom
    have he : pt e = x := AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x hx
    have h1 : spMap (e.comp c) = spMap σ := by rw [← hpts, he, hxs]
    have h2 : e.comp c = σ := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    exact ⟨{ e with commutes' := fun a => RingHom.congr_fun h2 a }, he⟩
  have hyU : ⊤ ≤ y₀ ⁻¹ᵁ U := ((valAt'_rules X y₀).1 U).2 hp
  obtain ⟨e, rfl⟩ := hsurj y₀ hy₀ hyU
  obtain ⟨W, p, n, r, ε, hW, hW0, hp0, hε, hpd, hpi, hps⟩ := exists_chart_algebra d e
  refine ⟨W, fun w => pt (p w).toRingHom, U, fun _ => 0, n, r, hW, hW0, by simp only [hp0],
    fun b _ => ?_, fun V f => ?_, fun w hw w' hw' h => hpi hw hw' ?_, hyU, ε, hε,
    fun x hxs hx hxe => ?_⟩
  · rw [hpts]
    congr 2
    exact RingHom.ext fun a => (p b).commutes a
  · exact HolChart.hol_of_affine valAt'_rules hU hW (fun w => pt (p w).toRingHom)
      (fun w _ => hptU _) (fun a => (hpd a).congr fun w _ => hptv _ a) V f
  · refine AlgHom.ext fun a => ?_
    have h1 := hptv (p w).toRingHom a
    have h' : pt (p w).toRingHom = pt (p w').toRingHom := h
    rw [h', hptv] at h1
    exact h1.symm
  · obtain ⟨e', rfl⟩ := hsurj x hxs hx
    obtain ⟨w, hw, h⟩ := hps e' fun i => by
      have := hxe i
      rw [hptv, hptv] at this
      exact this
    exact ⟨w, hw, by rw [h]⟩

end GlobalTheory.SubfieldChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoHeckeQuotient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeTate

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

def form (D : Datum H) : D.La →+ D.La →+ ℤ :=
  AddMonoidHom.mk' (fun x => (D.EF x).toAddMonoidHom) fun a b => by rw [map_add (f := _)]; rfl

theorem form_apply (x y : D.La) : form D x y = D.EF x y := rfl

theorem form_isUnimod (D : Datum H) : IsUnimod H.bar (form D) := by
  refine ⟨fun x y => ?_, D.adj, fun x y h => D.unimod.1 (LinearMap.ext fun a => DFunLike.congr_fun h a),
    fun f => ?_⟩
  · exact (LinearMap.IsAlt.neg (B := D.EF) D.alt y x).symm
  · obtain ⟨x, hx⟩ := D.unimod.2 f.toIntLinearMap
    exact ⟨x, AddMonoidHom.ext fun a => LinearMap.congr_fun hx a⟩

variable {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

def evHom (I : TateIso D k Q act e) (n : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev n a)) fun a b => by rw [I.add]; rfl

theorem ev_zero (I : TateIso D k Q act e) (n : ℕ) : I.ev n 0 = 1 := (evHom I n).map_zero

theorem ev_nsmul (I : TateIso D k Q act e) (n m : ℕ) (a : D.La) : I.ev n (m • a) = I.ev n a ^ m :=
  (evHom I n).map_nsmul m a

theorem ev_sub (I : TateIso D k Q act e) (n : ℕ) (a b : D.La) : I.ev n (a - b) = I.ev n a / I.ev n b :=
  (evHom I n).map_sub a b

end

end GlobalTheory.HeckeTate

namespace GlobalTheory

open HeckeTate

theorem exists_tateIso_heckeQuotient :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), 1 ≤ D.p + D.q → (∀ (g : Sim D) (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧ IsCoprime (g.ν n) (n : ℤ)) ∧ (∃ g : Sim D, ∀ n, g.f n = LinearMap.id ∧ g.ν n = 1) ∧ (∀ g g' : Sim D, ∃ g'' : Sim D, ∀ n, g''.f n = g.f n ∘ₗ g'.f n ∧ g''.ν n = g.ν n * g'.ν n) ∧ (∀ g : Sim D, ∃ g' : Sim D, ∀ n, 0 < n → (∀ a, D.ModN n (g'.f n (g.f n a) - a) ∧ D.ModN n (g.f n (g'.f n a) - a)) ∧ (n : ℤ) ∣ g.ν n * g'.ν n - 1)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (𝔓 : Ideal (𝓞 E)) (p : ℕ) (k : Type) [Field k] (Q Q' : Type) [CommGroup Q] [CommGroup Q'] (act : 𝓞 E → Q → Q) (act' : 𝓞 E → Q' → Q') (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → kˣ → Prop) (I : TateIso D k Q act e) (ψ : Q →* Q'), 𝔓.IsMaximal → 𝔓 ⊔ 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → p.Prime → (p : 𝓞 E) ∈ 𝔓 → Function.Surjective ψ → (∀ a x, ψ (act a x) = act' a (ψ x)) → (∀ J : Ideal (𝓞 E), J * 𝔓 = Ideal.span {(p : 𝓞 E)} → ∀ x, x ^ p = 1 → (∀ a ∈ J, act a x = 1) → ψ x = 1) → (∀ x, ψ x = 1 → x ^ p ^ 2 = 1 ∧ ∀ a ∈ Ideal.span {(p : 𝓞 E)} * 𝔓.map (H.bar : 𝓞 E →+* 𝓞 E), act a x = 1) → (∀ x y, ψ x = 1 → ψ y = 1 → e (p ^ 2) x y 1) → Nat.card ψ.ker = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) → (∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c') → (∀ n x y c, 0 < n → ψ x ^ n = 1 → ψ y ^ n = 1 → e (n * p ^ 2) x y c → e' n (ψ x) (ψ y) c) → ∃ I' : TateIso D k Q' act' e', I'.ζ = I.ζ ∧ ∀ n p' : ℕ, 0 < n → p * p' ≡ 1 [MOD n] → ∀ a, I'.ev n a = ψ (I.ev n (p' • a)) := by
  intro h₀ E _ _ _ H D P p k _ Q Q' _ _ act act' e e' I ψ hP hPP hp hpP hψ hact hlow hup hiso hcard huniq he'
  clear h₀
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq : 0 < p ^ 2 := pow_pos hp.pos 2
  have := D.fin
  have := D.proj
  have := datum_free_int D
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let C : Submodule (𝓞 E) D.La :=
    { carrier := {a | ψ (I.ev (p ^ 2) a) = 1}
      add_mem' := fun {a b} ha hb => by
        change ψ _ = 1 at ha hb ⊢
        rw [I.add, map_mul, ha, hb, _root_.one_mul]
      zero_mem' := by
        change ψ _ = 1
        rw [ev_zero, map_one]
      smul_mem' := fun c a ha => by
        change ψ _ = 1 at ha ⊢
        have h0 := hact c (I.ev (p ^ 2) 0)
        rw [← I.lin, smul_zero, ev_zero, map_one] at h0
        rw [I.lin, hact, ha, ← h0] }
  have hC : ∀ a, a ∈ C ↔ ψ (I.ev (p ^ 2) a) = 1 := fun _ => Iff.rfl
  have hsq : ∀ a, (p ^ 2) • a ∈ C := fun a => by
    rw [hC, (I.ker _ hq _).2 ⟨a, rfl⟩, map_one]
  have hCiso : ∀ x ∈ C, ∀ y ∈ C, ((p ^ 2 : ℕ) : ℤ) ∣ form D x y := fun x hx y hy => by
    have := huniq _ _ _ _ _ hq ((I.onto _ hq _).2 ⟨x, rfl⟩) ((I.onto _ hq _).2 ⟨y, rfl⟩)
      (I.isom _ hq x y) (hiso _ _ hx hy)
    exact ((I.ζ_prim _ hq).zpow_eq_one_iff_dvd _).1 this
  have hidx : (nsmulAddMonoidHom (α := D.La) (p ^ 2)).range.relIndex C.toAddSubgroup = Nat.card ψ.ker := by
    let f : C.toAddSubgroup →+ Additive ψ.ker := AddMonoidHom.mk'
      (fun a => Additive.ofMul ⟨I.ev (p ^ 2) a, a.2⟩) fun a b => by
        rw [← ofMul_mul]
        exact congrArg _ (Subtype.ext (I.add _ _ _))
    have hf : Function.Surjective f := fun x => by
      obtain ⟨a, ha⟩ := (I.onto _ hq _).1 (hup _ x.toMul.2).1
      exact ⟨⟨a, (hC a).2 (ha ▸ x.toMul.2)⟩, Additive.toMul.injective (Subtype.ext ha)⟩
    have hker : f.ker = (nsmulAddMonoidHom (α := D.La) (p ^ 2)).range.addSubgroupOf C.toAddSubgroup := by
      ext a
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
      constructor
      · intro h
        obtain ⟨b, hb⟩ := (I.ker _ hq a).1 (congrArg (fun z => (z.toMul : Q)) h)
        exact ⟨b, hb.symm⟩
      · rintro ⟨b, hb⟩
        exact Additive.toMul.injective (Subtype.ext ((I.ker _ hq a).2 ⟨b, hb.symm⟩))
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf,
      AddSubgroup.card_top]
    rfl
  have horth := mem_of_orth (form D) (form_isUnimod D).bij (m := p ^ 2) (c := Nat.card ψ.ker) hq.ne'
    (by rw [hcard, datum_finrank_int]; ring) C.toAddSubgroup (by rintro _ ⟨a, rfl⟩; exact hsq a) hidx hCiso
  obtain ⟨B', hB', hBB⟩ := exists_unimod_div (form_isUnimod D) hq.ne' C hsq hCiso horth
  have hsq' : ∀ a, ∃ y : C, C.subtype y = (p : 𝓞 E) ^ 2 • a := fun a =>
    ⟨⟨_, hsq a⟩, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; rfl⟩
  have hlow' : ∀ g ∈ P, ∀ a, ∃ y : C, C.subtype y = (g * p) • a := fun g hg a => by
    obtain ⟨J, hJ⟩ : P ∣ Ideal.span {(p : 𝓞 E)} := Ideal.dvd_iff_le.2 (by simpa using hpP)
    refine ⟨⟨(g * p) • a, hlow J (by rw [hJ, _root_.mul_comm]) (I.ev (p ^ 2) ((g * p) • a)) ?_ fun c hc => ?_⟩, rfl⟩
    · rw [← ev_nsmul, I.ker _ hq]
      refine ⟨g • a, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.1 (hJ ▸ Ideal.mul_mem_mul hg hc)
      rw [← I.lin, I.ker _ hq]
      refine ⟨d • a, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul, smul_smul]
      congr 1
      push_cast
      linear_combination (p : 𝓞 E) * hd
  have hrank : Module.finrank (𝓞 E) D.La = Module.finrank (𝓞 E) C := by
    refine le_antisymm ?_ C.finrank_le
    let u : D.La →ₗ[𝓞 E] C := LinearMap.codRestrict C ((p ^ 2) • LinearMap.id) hsq
    refine LinearMap.finrank_le_finrank_of_injective (f := u) fun x y h => ?_
    refine (form_isUnimod D).smul_cancel hq.ne' ?_
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    exact congrArg Subtype.val h
  have := hP.isPrime
  obtain ⟨φ, φ', s, hs, hφ, hφ'⟩ := exists_local_iso hrank P
  obtain ⟨G, G1, G2, G3, G4, G5⟩ := exists_glued (form_isUnimod D) hB' (bar_bar H) hP hPP hp0 hpP C.subtype
    C.injective_subtype (fun x y => by simpa using hBB x y) hsq' hlow' φ φ' hs hφ hφ'
  have hpos : ∀ n : ℕ, 0 < n → 0 < n * p ^ 2 := fun n hn => Nat.mul_pos hn hq
  have hdown : ∀ n : ℕ, 0 < n → ∀ a, I.ev (n * p ^ 2) a ^ n = I.ev (p ^ 2) a := fun n hn a => by
    rw [_root_.mul_comm, I.tower _ _ hq hn]
  have hkey : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) = 1 ↔ y ∈ mults C (n : 𝓞 E) := by
    intro n hn y
    rw [mem_mults]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (I.onto _ hq _).1 (hup _ h).1
      have hcC : c ∈ C := (hC c).2 (hc ▸ h)
      have : I.ev (n * p ^ 2) (y - n • c) = 1 := by
        rw [ev_sub, ev_nsmul, hdown n hn, hc, div_self']
      obtain ⟨b, hb⟩ := (I.ker _ (hpos n hn) _).1 this
      refine ⟨⟨c, hcC⟩ + ⟨_, hsq b⟩, Subtype.ext ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      change (y : D.La) = n • (c + (p ^ 2) • b)
      rw [smul_add, ← mul_smul, ← hb]
      abel
    · rintro ⟨z, rfl⟩
      rw [Nat.cast_smul_eq_nsmul]
      change ψ (I.ev _ (n • (z : D.La))) = 1
      rw [ev_nsmul, hdown n hn]
      exact z.2
  have hkey' : ∀ n : ℕ, 0 < n → ∀ y y' : C, y - y' ∈ mults C (n : 𝓞 E) →
      ψ (I.ev (n * p ^ 2) y) = ψ (I.ev (n * p ^ 2) y') := fun n hn y y' h => by
    have := (hkey n hn _).2 h
    rwa [Submodule.coe_sub, ev_sub, map_div, div_eq_one] at this
  have htor : ∀ n : ℕ, 0 < n → ∀ y : C, ψ (I.ev (n * p ^ 2) y) ^ n = 1 := fun n hn y => by
    rw [← map_pow, hdown n hn]
    exact y.2
  refine ⟨⟨I.ζ, I.ζ_prim, I.ζ_pow, fun n a => ψ (I.ev (n * p ^ 2) (G n a)), fun n a b => ?_, fun n c a => ?_,
    fun n hn a => ?_, fun n hn x => ⟨fun hx => ?_, ?_⟩, fun n m hn hm a => ?_, fun n hn a b => ?_⟩, rfl,
    fun n p' hn hpp a => ?_⟩
  · rw [map_add (f := _), Submodule.coe_add, I.add, map_mul]
  · rw [map_smul, Submodule.coe_smul, I.lin, hact]
  · rw [hkey n hn]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := mem_mults.1 (G1 n hn a h)
      exact ⟨b, by rw [hb, Nat.cast_smul_eq_nsmul]⟩
    · rintro ⟨b, rfl⟩
      exact map_mem_mults _ (mem_mults.2 ⟨b, (Nat.cast_smul_eq_nsmul _ _ _).symm⟩)
  · obtain ⟨x, rfl⟩ := hψ x
    have h1 := (hup _ ((map_pow ψ x n).trans hx)).1
    rw [← pow_mul] at h1
    obtain ⟨b, rfl⟩ := (I.onto _ (hpos n hn) _).1 h1
    have hb : b ∈ C := by rw [hC, ← hdown n hn, map_pow, hx]
    obtain ⟨a, ha⟩ := G2 n hn ⟨b, hb⟩
    exact ⟨a, hkey' n hn _ _ ha⟩
  · rintro ⟨a, rfl⟩
    exact htor n hn _
  · rw [← map_pow, mul_right_comm, I.tower _ _ (hpos n hn) hm]
    exact hkey' n hn _ _ (G3 n m hn hm a)
  · refine he' n _ _ _ hn (htor n hn _) (htor n hn _) ?_
    have h1 := I.isom _ (hpos n hn) (G n a) (G n b)
    obtain ⟨t, ht⟩ := G4 n hn a b
    have h2 : D.EF (G n a) (G n b) = (p ^ 2 : ℕ) * (D.EF a b + n * t) := by
      rw [← ht, ← form_apply, hBB, form_apply]
      ring
    rw [h2, zpow_mul, zpow_natCast, I.ζ_pow _ _ hn hq, zpow_add, zpow_mul, zpow_natCast,
      (I.ζ_prim n hn).pow_eq_one, one_zpow, _root_.mul_one] at h1
    exact h1
  · have hcop : n.Coprime p := (Nat.coprime_of_mul_modEq_one p' hpp).symm
    change ψ (I.ev (n * p ^ 2) (G n a)) = _
    rw [← I.tower n _ hn hq, ← ev_nsmul]
    refine hkey' n hn _ ⟨_, hsq _⟩ ?_
    obtain ⟨b, hb⟩ := mem_mults.1 (G5 n hn hcop a)
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd.1 hpp)
    have ht' := congrArg (Int.castRingHom (𝓞 E)) ht
    simp only [eq_intCast] at ht'
    push_cast at ht'
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 (hcop.pow_right 2)).map (Int.castRingHom (𝓞 E))
    simp only [eq_intCast, Int.cast_natCast] at huv
    set y : C := G n a - ⟨_, hsq (p' • a)⟩ with hy
    have h1 : (y : D.La) = (n : 𝓞 E) • (b + ((p : 𝓞 E) * t) • a) := by
      rw [smul_add, ← hb, hy, Submodule.coe_sub, Submodule.subtype_apply]
      simp only [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]
      rw [sub_add, ← sub_smul]
      congr 2
      push_cast
      linear_combination (-(p : 𝓞 E)) * ht'
    generalize b + ((p : 𝓞 E) * t) • a = z at h1
    refine mem_mults.2 ⟨u • y + v • ⟨_, hsq z⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_smul, Submodule.coe_add, h1, ← Nat.cast_smul_eq_nsmul (𝓞 E), smul_smul]
    rw [← add_smul, huv, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOpenPosDefOfContinuous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isOpen_posDef_of_continuous {X n : Type} [TopologicalSpace X] [Fintype n]
    (M : X → Matrix n n ℝ) (hc : Continuous M) (hs : ∀ x, (M x).IsHermitian) :
    IsOpen {x | (M x).PosDef} := by
  rw [isOpen_iff_mem_nhds]
  intro x₀ hx₀
  have hK : IsCompact (Metric.sphere (0 : n → ℝ) 1) := isCompact_sphere _ _
  have hcont : Continuous (fun p : X × (n → ℝ) => dotProduct (star p.2) ((M p.1).mulVec p.2)) :=
    (continuous_snd.star).dotProduct ((hc.comp continuous_fst).matrix_mulVec continuous_snd)
  have hev : ∀ᶠ x in nhds x₀, ∀ v ∈ Metric.sphere (0 : n → ℝ) 1,
      0 < dotProduct (star v) ((M x).mulVec v) := by
    apply hK.eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hx₀).2 hv0
    exact (isOpen_lt continuous_const hcont).mem_nhds hpos
  filter_upwards [hev] with x hx
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hs x, fun v hv => ?_⟩
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 := hx (‖v‖⁻¹ • v) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  simp only [star_trivial, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 ⊢
  have hi : 0 < ‖v‖⁻¹ := inv_pos.mpr hn
  exact (mul_pos_iff_of_pos_left hi).mp ((mul_pos_iff_of_pos_left hi).mp h1)

theorem card_sym2_fin (h : ℕ) : Fintype.card (Sym2 (Fin h)) = h * (h + 1) / 2 := by
  rw [Sym2.card, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

theorem exists_siegel_coordinates :
    ∀ h : ℕ, ∃ (B : Set (Fin (h * (h + 1) / 2) → ℂ)) (τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ), IsOpen B ∧ Convex ℝ B ∧ (∀ i j, Differentiable ℂ (fun b => τ b i j)) ∧ (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) ∧ ∀ t : Matrix (Fin h) (Fin h) ℂ, t.IsSymm → (t.map Complex.im).PosDef → ∃! b, b ∈ B ∧ τ b = t := by
  intro h
  let e : Sym2 (Fin h) ≃ Fin (h * (h + 1) / 2) := Fintype.equivFinOfCardEq (card_sym2_fin h)
  let τ : (Fin (h * (h + 1) / 2) → ℂ) → Matrix (Fin h) (Fin h) ℂ :=
    fun b => Matrix.of fun i j => b (e s(i, j))
  have hτ : ∀ b i j, τ b i j = b (e s(i, j)) := fun _ _ _ => rfl
  have hsymm : ∀ b, (τ b).IsSymm := by
    intro b
    ext i j
    rw [Matrix.transpose_apply, hτ, hτ, Sym2.eq_swap]
  refine ⟨{b | ((τ b).map Complex.im).PosDef}, τ, ?_, ?_, ?_, ?_, ?_⟩
  · apply isOpen_posDef_of_continuous (fun b => (τ b).map Complex.im)
    · refine continuous_matrix fun i j => ?_
      exact Complex.continuous_im.comp (continuous_apply (e s(i, j)))
    · intro b
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.map_apply, hτ]
      rw [Sym2.eq_swap]
  · intro x hx y hy a b ha hb hab
    have key : (τ (a • x + b • y)).map Complex.im
        = a • (τ x).map Complex.im + b • (τ y).map Complex.im := by
      ext i j
      simp [hτ]
    change ((τ (a • x + b • y)).map Complex.im).PosDef
    rw [key]
    rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by simpa using hab
      subst this
      simpa using hy
    · exact (Matrix.PosDef.smul hx ha').add_posSemidef
        (Matrix.PosSemidef.smul (Matrix.PosDef.posSemidef hy) hb)
  · intro i j
    exact differentiable_apply (𝕜 := ℂ) (e s(i, j))
  · intro b hb
    exact ⟨hsymm b, hb⟩
  · intro t ht hp
    let f : Sym2 (Fin h) → ℂ := Sym2.lift ⟨fun i j => t i j, fun i j => (ht.apply i j).symm⟩
    have hf : τ (fun k => f (e.symm k)) = t := by
      ext i j
      change f (e.symm (e s(i, j))) = t i j
      rw [Equiv.symm_apply_apply]
      rfl
    refine ⟨fun k => f (e.symm k), ⟨?_, hf⟩, ?_⟩
    · change ((τ (fun k => f (e.symm k))).map Complex.im).PosDef
      rw [hf]; exact hp
    · rintro b ⟨-, hb⟩
      funext k
      obtain ⟨z, rfl⟩ := e.surjective k
      induction z using Sym2.ind with
      | _ i j =>
        rw [Equiv.symm_apply_apply]
        exact congrFun (congrFun hb i) j

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsVeryGeneralPointOfHolomorphicFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_veryGeneral_point_of_holomorphic_family :
    ∀ (o : Type) [CommRing o] [Countable o] (em : o →+* ℂ) (I : Type) [Countable I] (m : ℕ) (B : Set (Fin m → ℂ)) (θ : (Fin m → ℂ) → I → ℂ), IsOpen B → IsPreconnected B → B.Nonempty → (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) → ∃ z ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ F : MvPolynomial I o, MvPolynomial.eval₂ em (c • θ z) F = 0 → ∀ z' ∈ B, ∀ c' : ℂ, c' ≠ 0 → MvPolynomial.eval₂ em (c' • θ z') F = 0 := by
  intro o _ _ em I _ m B θ hB hBc hBne hθ
  classical
  have : Countable (MvPolynomial I o) :=
    Function.Surjective.countable
      (f := (AddMonoidAlgebra.ofCoeff : ((I →₀ ℕ) →₀ o) → MvPolynomial I o))
      fun F => ⟨AddMonoidAlgebra.coeff F, rfl⟩

  set Ω : Set (Fin (m + 1) → ℂ) := {p | Fin.tail p ∈ B ∧ p 0 ∈ ({0}ᶜ : Set ℂ)} with hΩ
  have htail : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => Fin.tail p) :=
    differentiable_pi.2 fun i => differentiable_apply _
  have hhead : Differentiable ℂ (fun p : Fin (m + 1) → ℂ => p 0) := differentiable_apply _
  have hΩo : IsOpen Ω :=
    (hB.preimage htail.continuous).inter (isOpen_compl_singleton.preimage hhead.continuous)
  have hΩimg : Ω = (fun q : (Fin m → ℂ) × ℂ => (Fin.cons q.2 q.1 : Fin (m + 1) → ℂ)) ''
      (B ×ˢ ({0}ᶜ : Set ℂ)) := by
    ext p
    constructor
    · intro hp
      exact ⟨(Fin.tail p, p 0), ⟨hp.1, hp.2⟩, Fin.cons_self_tail p⟩
    · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, rfl⟩
      exact ⟨by simpa using hz, by simpa using hc⟩
  have hΩc : IsPreconnected Ω := by
    rw [hΩimg]
    refine (hBc.prod (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected).image _ ?_
    · rw [Complex.rank_real_complex]; norm_num
    · exact (Continuous.finCons (A := fun _ => ℂ) continuous_snd continuous_fst).continuousOn
  have hΩne : Ω.Nonempty := by
    obtain ⟨z₀, hz₀⟩ := hBne
    exact ⟨Fin.cons 1 z₀, by simpa using hz₀, by simp⟩

  let f : MvPolynomial I o → (Fin (m + 1) → ℂ) → ℂ :=
    fun F p => MvPolynomial.eval₂ em (p 0 • θ (Fin.tail p)) F
  have hfd : ∀ F, DifferentiableOn ℂ (f F) Ω := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a =>
      simp only [f, MvPolynomial.eval₂_C]
      exact differentiableOn_const _
    | add F G hF hG =>
      simp only [f, MvPolynomial.eval₂_add]
      exact hF.add hG
    | mul_X F a hF =>
      have ha : DifferentiableOn ℂ (fun p : Fin (m + 1) → ℂ => θ (Fin.tail p) a) Ω :=
        (hθ a).comp htail.differentiableOn fun p hp => hp.1
      simp only [f, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.smul_apply, smul_eq_mul]
      exact hF.mul (hhead.differentiableOn.mul ha)
  have hfa : ∀ F, AnalyticOnNhd ℂ (f F) Ω := fun F =>
    ReciprocityTheory.AnForm.Osgood.osgood (m + 1) Ω (f F) hΩo (hfd F)

  let W : MvPolynomial I o → Set (Fin (m + 1) → ℂ) := fun F =>
    if Set.EqOn (f F) 0 Ω then Set.univ else (Ω ∩ f F ⁻¹' {0}ᶜ) ∪ (closure Ω)ᶜ
  have hWo : ∀ F, IsOpen (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact isOpen_univ
    · simp only [W, if_neg h]
      exact ((hfd F).continuousOn.isOpen_inter_preimage hΩo isOpen_compl_singleton).union
        isClosed_closure.isOpen_compl
  have hWd : ∀ F, Dense (W F) := by
    intro F
    by_cases h : Set.EqOn (f F) 0 Ω
    · simp only [W, if_pos h]
      exact dense_univ
    · simp only [W, if_neg h]
      have hsub : Ω ⊆ closure (Ω ∩ f F ⁻¹' {0}ᶜ) := by
        intro q hq
        by_contra hq'
        apply h
        refine (hfa F).eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩc hq ?_
        have hn : (closure (Ω ∩ f F ⁻¹' {0}ᶜ))ᶜ ∩ Ω ∈ nhds q :=
          Filter.inter_mem (isClosed_closure.isOpen_compl.mem_nhds hq') (hΩo.mem_nhds hq)
        filter_upwards [hn] with p hp
        by_contra hne
        exact hp.1 (subset_closure ⟨hp.2, hne⟩)
      intro x
      by_cases hx : x ∈ closure Ω
      · exact closure_mono Set.subset_union_left (closure_minimal hsub isClosed_closure hx)
      · exact subset_closure (Or.inr hx)

  obtain ⟨p, hpΩ, hpW⟩ := (dense_iInter_of_isOpen hWo hWd).inter_open_nonempty Ω hΩo hΩne
  refine ⟨Fin.tail p, hpΩ.1, p 0, hpΩ.2, fun F hF z' hz' c' hc' => ?_⟩
  by_cases h : Set.EqOn (f F) 0 Ω
  · have hmem : (Fin.cons c' z' : Fin (m + 1) → ℂ) ∈ Ω := ⟨by simpa using hz', by simpa using hc'⟩
    simpa [f] using h hmem
  · have hpW' := Set.mem_iInter.1 hpW F
    simp only [W, if_neg h] at hpW'
    rcases hpW' with hp' | hp'
    · exact absurd hF hp'.2
    · exact absurd (subset_closure hpΩ) hp'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankMapAddFinrankInfKerOfFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolynomialFinrankHomogeneousSubmoduleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule : ∀ (σ : Type) [Finite σ] [Nonempty σ], ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (e : ℕ), ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e) : ℕ) : ℚ) = Q.eval (e : ℚ) := by
  first | exact @GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | exact GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule | (intros; apply GlobalTheory.exists_polynomial_finrank_homogeneousSubmodule <;> assumption)
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem finrank_map_add_finrank_inf_ker_of_finite {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) (P : Submodule K M) [Module.Finite K P] :
    Module.finrank K ↥(P.map f) + Module.finrank K ↥(P ⊓ LinearMap.ker f) = Module.finrank K P := by
  have h := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq P, Submodule.map_comap_subtype] at h
  exact h

theorem mem_homogeneousSubmodule_mul_of_add {K σ : Type*} [Field K] {m n : ℕ}
    {F : MvPolynomial σ K} (hF : F.IsHomogeneous (m + n)) :
    F ∈ homogeneousSubmodule σ K m * homogeneousSubmodule σ K n := by
  rw [← homogeneousSubmodule_one_pow K m, ← homogeneousSubmodule_one_pow K n, ← pow_add,
    homogeneousSubmodule_one_pow]
  exact hF

theorem sub_rename_mem_span_degree {K σ : Type*} [Field K] (t : σ → σ)
    (I : Ideal (MvPolynomial σ K)) (hI : ∀ F, F - rename t F ∈ I) {d : ℕ} (hd : 1 ≤ d)
    {e : ℕ} (he : d ≤ e) : ∀ F : MvPolynomial σ K, F.IsHomogeneous e →
      F - rename t F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
  have hk : ∀ (l : MvPolynomial σ K), l.IsHomogeneous 1 → l ∈ I → ∀ n, d ≤ n →
      ∀ H : MvPolynomial σ K, H.IsHomogeneous n →
      l * H ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d} := by
    intro l hl hlI n hn H hH
    have hn' : n = (d - 1) + (n - (d - 1)) := by omega
    rw [hn'] at hH
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hH) ?_ ?_
    · intro A hA B _
      rw [← _root_.mul_assoc]
      refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨Ideal.mul_mem_right _ _ hlI, ?_⟩)
      have h := hl.mul hA
      rwa [show 1 + (d - 1) = d by omega] at h
    · intro x y hx hy
      rw [mul_add]
      exact add_mem hx hy
  induction e, he using Nat.le_induction with
  | base =>
    intro F hF
    exact Ideal.subset_span ⟨hI F, hF.sub hF.rename_isHomogeneous⟩
  | succ n hn ih =>
    intro F hF
    rw [add_comm] at hF
    refine Submodule.mul_induction_on (mem_homogeneousSubmodule_mul_of_add hF) ?_ ?_
    · intro l hl G hG
      have hl' : l.IsHomogeneous 1 := hl
      have hG' : G.IsHomogeneous n := hG
      have : l * G - rename t (l * G) =
          l * (G - rename t G) + (l - rename t l) * rename t G := by
        rw [map_mul]; ring
      rw [this]
      exact add_mem (Ideal.mul_mem_left _ _ (ih G hG'))
        (hk _ (hl'.sub hl'.rename_isHomogeneous) (hI l) n hn _ hG'.rename_isHomogeneous)
    · intro x y hx hy
      have : x + y - rename t (x + y) = (x - rename t x) + (y - rename t y) := by
        rw [map_add (f := _)]; ring
      rw [this]
      exact add_mem hx hy

theorem regularity_comap_rename_of_surjective :
    ∀ (σ σ₀ : Type) [Finite σ] [Finite σ₀] [Nonempty σ₀] (r : σ → σ₀) (Q₀ : Polynomial ℚ), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] (I₀ : Ideal (MvPolynomial σ₀ K)) (I : Ideal (MvPolynomial σ K)) (d : ℕ), I = I₀.comap (MvPolynomial.rename r) → 1 ≤ d → ∀ e ≥ d, (((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ₀ K e ⊓ (I₀).restrictScalars K) : ℕ) : ℚ) = Q₀.eval (e : ℚ) → ((Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ (I).restrictScalars K) : ℕ) : ℚ) = Q.eval (e : ℚ)) ∧ ((∀ F ∈ I₀, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d}) → ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}) := by
  intro σ σ₀ _ _ _ r Q₀ hr
  obtain ⟨s, hs⟩ := hr.hasRightInverse
  haveI : Nonempty σ := ⟨s (Classical.arbitrary _)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule σ
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_polynomial_eval_eq_finrank_homogeneousSubmodule σ₀
  refine ⟨Q₀ + P - P₀, ?_⟩
  intro K _ I₀ I d hI hd e he
  have hrs : ∀ G : MvPolynomial σ₀ K, rename r (rename s G) = G := by
    intro G
    rw [rename_rename, hs.comp_eq_id, rename_id_apply]
  have hmem : ∀ F, F ∈ I ↔ rename r F ∈ I₀ := by
    intro F
    rw [hI]; exact Ideal.mem_comap
  constructor
  · intro h
    haveI : Module.Finite K (homogeneousSubmodule σ K e) :=
      Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
    haveI : Module.Finite K ↥(homogeneousSubmodule σ K e ⊓ I.restrictScalars K) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have h1 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap (homogeneousSubmodule σ K e)
    have h2 := finrank_map_add_finrank_inf_ker_of_finite
      (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap
      (homogeneousSubmodule σ K e ⊓ I.restrictScalars K)
    have e1 : (homogeneousSubmodule σ K e).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact IsHomogeneous.rename_isHomogeneous hF
      · intro G hG
        exact ⟨rename s G, IsHomogeneous.rename_isHomogeneous hG, hrs G⟩
    have e2 : (homogeneousSubmodule σ K e ⊓ I.restrictScalars K).map
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ₀ K e ⊓ I₀.restrictScalars K := by
      apply le_antisymm
      · rintro _ ⟨F, hF, rfl⟩
        exact ⟨IsHomogeneous.rename_isHomogeneous hF.1, (hmem F).1 hF.2⟩
      · intro G hG
        refine ⟨rename s G, ⟨IsHomogeneous.rename_isHomogeneous hG.1, (hmem _).2 ?_⟩, hrs G⟩
        rw [hrs]; exact hG.2
    have e3 : homogeneousSubmodule σ K e ⊓ I.restrictScalars K ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap =
        homogeneousSubmodule σ K e ⊓ LinearMap.ker
        (rename r : MvPolynomial σ K →ₐ[K] MvPolynomial σ₀ K).toLinearMap := by
      apply le_antisymm
      · exact inf_le_inf_right _ inf_le_left
      · intro F hF
        refine ⟨⟨hF.1, (hmem F).2 ?_⟩, hF.2⟩
        have : rename r F = 0 := hF.2
        rw [this]; exact zero_mem _
    rw [e1] at h1
    rw [e2, e3] at h2
    rw [Polynomial.eval_sub, Polynomial.eval_add, ← h, ← hP K e, ← hP₀ K e, ← h1, ← h2]
    push_cast
    ring
  · intro h F hF hFe
    have hA := sub_rename_mem_span_degree (s ∘ r) I (fun G => by
      rw [hmem, map_sub, ← rename_rename, hrs, sub_self]; exact zero_mem _) hd he F hFe
    have hB : Ideal.span {G | G ∈ I₀ ∧ G.IsHomogeneous d} ≤
        (Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d}).comap (rename s) := by
      rw [Ideal.span_le]
      intro G hG
      refine Ideal.mem_comap.mpr (Ideal.subset_span ⟨(hmem _).2 ?_, hG.2.rename_isHomogeneous⟩)
      rw [hrs]; exact hG.1
    have hC := Ideal.mem_comap.mp (hB (h _ ((hmem F).1 hF) hFe.rename_isHomogeneous))
    rw [rename_rename] at hC
    simpa using add_mem hA hC

end GlobalTheory
end
