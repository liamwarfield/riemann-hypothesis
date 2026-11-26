module

public import Development.AutomorphicArithmetic.TwistedTraces.ReInnerGeOfSpanEigenvectors

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.CasimirEqOfOrthonormalBases
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.casimir_eq_of_orthonormal_bases :
    ∀ (L : Type) [LieRing L] [LieAlgebra ℝ L] (B : LinearMap.BilinForm ℝ L) (ι ι' : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (b : Module.Basis ι ℝ L) (ε : ι → ℝ) (b' : Module.Basis ι' ℝ L) (ε' : ι' → ℝ), (∀ X Y, B X Y = B Y X) → (∀ i, ε i * ε i = 1) → (∀ i j, B (b i) (b j) = if i = j then ε i else 0) → (∀ i, ε' i * ε' i = 1) → (∀ i j, B (b' i) (b' j) = if i = j then ε' i else 0) → casimir b ε = casimir b' ε' := by
  intro L _ _ B ι ι' _ _ _ _ b ε b' ε' hs hε hb hε' hb'
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L) with hu
  have e1 : ∀ i, u (b i) = ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) := by
    intro i
    conv_lhs => rw [eq_sum_of_orthogonal hε' hb' (b i)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have e2 : ∀ j, u (b' j) = ∑ i, (ε i * B (b i) (b' j)) • u (b i) := by
    intro j
    conv_lhs => rw [eq_sum_of_orthogonal hε hb (b' j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  simp only [casimir]
  calc ∑ i, ε i • (u (b i) * u (b i))
      = ∑ i, ∑ j, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : u (b i) * u (b i) = u (b i) * ∑ j, (ε' j * B (b' j) (b i)) • u (b' j) :=
          congrArg (fun x => u (b i) * x) (e1 i)
        rw [h, Finset.mul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, smul_smul]
    _ = ∑ j, ∑ i, (ε i * (ε' j * B (b' j) (b i))) • (u (b i) * u (b' j)) := Finset.sum_comm
    _ = ∑ j, ε' j • (u (b' j) * u (b' j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have h : u (b' j) * u (b' j) = (∑ i, (ε i * B (b i) (b' j)) • u (b i)) * u (b' j) :=
          congrArg (fun x => x * u (b' j)) (e2 j)
        rw [h, Finset.sum_mul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, smul_smul, hs (b' j) (b i)]
        congr 1
        ring
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.NormCuspVecLGkActionLeOfAevalEqZero
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.NormDerivOrbitLeOfPolynomialAnnihilated
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.NormGeneratorLeOfPolynomialAnnihilated
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.NormSkewAdjointLeOfEigenvalueBound
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (D : Module.End ℂ E) (M : ℝ), (∀ x y, inner ℂ (D x) y + inner ℂ x (D y) = 0) → (∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ D M hskew hev x
  have hT : (Complex.I • D : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    have h := hskew x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
    linear_combination (-Complex.I) * h
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  have hb : ∀ i, |hT.eigenvalues hn i| ≤ M := by
    intro i
    have h1 := hT.apply_eigenvectorBasis hn i
    have h2 : D (hT.eigenvectorBasis hn i) = (-Complex.I * (hT.eigenvalues hn i : ℂ)) • hT.eigenvectorBasis hn i := by
      have h3 : D (hT.eigenvectorBasis hn i) = (-Complex.I) • ((Complex.I • D : E →ₗ[ℂ] E) (hT.eigenvectorBasis hn i)) := by
        rw [LinearMap.smul_apply, smul_smul]; simp
      rw [h3, h1, smul_smul]; rfl
    have h4 : D.HasEigenvalue (-Complex.I * (hT.eigenvalues hn i : ℂ)) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 h2, (hT.eigenvectorBasis hn).orthonormal.ne_zero i⟩
    have h5 := hev _ h4
    simpa using h5
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb ⟨0, Module.finrank_pos⟩)
  have hDx : ‖D x‖ = ‖(Complex.I • D : E →ₗ[ℂ] E) x‖ := by
    simp [norm_smul]
  rw [hDx, ← (hT.eigenvectorBasis hn).repr.norm_map ((Complex.I • D : E →ₗ[ℂ] E) x),
    ← (hT.eigenvectorBasis hn).repr.norm_map x]
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h6 := hT.eigenvectorBasis_apply_self_apply hn x i
  rw [h6, norm_mul, mul_pow]
  gcongr
  simpa using hb i
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_generator_le_of_polynomial_annihilated :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (u : ℝ → Module.End ℂ E) (D : Module.End ℂ E) (p : ℝ → ℂ[X]) (M : ℝ), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → (∀ x, HasDerivAt (fun t : ℝ => u t x) (D x) 0) → (∀ t, aeval (u t) (p t) = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ u D p M h0 hadd hiso hder hroot hM x
  have hshift : ∀ (t : ℝ) (w : E), HasDerivAt (fun s : ℝ => u s w) (u t (D w)) t := by
    intro t w
    let L : E →L[ℂ] E := LinearMap.toContinuousLinearMap (u t)
    let LR : E →L[ℝ] E := L.restrictScalars ℝ
    have h1 : HasDerivAt (fun s : ℝ => LR (u s w)) (LR (D w)) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 (hder w)
    have h2 : HasDerivAt (fun s : ℝ => LR (u (s - t) w)) (LR (D w)) t := by
      apply HasDerivAt.comp_sub_const t t (f := fun s : ℝ => LR (u s w))
      simpa using h1
    have h3 : (fun s : ℝ => LR (u (s - t) w)) = fun s => u s w := by
      funext s
      show u t (u (s - t) w) = u s w
      rw [← Module.End.mul_apply, ← hadd]
      congr 2
      ring
    rw [h3] at h2
    exact h2
  have hinner : ∀ (t : ℝ) (a b : E), inner ℂ (u t a) (u t b) = inner ℂ a b := by
    intro t a b
    exact LinearIsometry.inner_map_map (⟨u t, hiso t⟩ : E →ₗᵢ[ℂ] E) a b
  have h0' : ∀ a : E, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hskew : ∀ a b : E, inner ℂ (D a) b + inner ℂ a (D b) = 0 := by
    intro a b
    have h1 := (hder a).inner ℂ (hder b)
    have h2 : (fun t : ℝ => inner ℂ (u t a) (u t b)) = fun _ => inner ℂ a b := by
      funext t
      exact hinner t a b
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ a b))
    rw [h0', h0'] at h3
    rw [add_comm]
    exact h3
  have hev : ∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_hasEigenvector
    have hDw : D w = z • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    have hconst : ∀ t : ℝ, Complex.exp (-(z * t)) • u t w = w := by
      have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)) • u s w) 0 t := by
        intro t
        have he : HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)))
            (Complex.exp (-(z * t)) * (-z)) t := by
          have hl : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-z) t := by
            have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
              simpa using (hasDerivAt_id t).ofReal_comp
            have h2 := h.const_mul (-z)
            simpa [neg_mul] using h2
          exact hl.cexp
        have h1 := he.smul (hshift t w)
        have h2 : Complex.exp (-(z * t)) • u t (D w) + (Complex.exp (-(z * t)) * (-z)) • u t w = 0 := by
          rw [hDw, map_smul, smul_smul, ← add_smul]
          have : Complex.exp (-(z * t)) * z + Complex.exp (-(z * t)) * (-z) = 0 := by ring
          rw [this, zero_smul]
        rw [h2] at h1
        exact h1
      intro t
      have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => Complex.exp (-(z * s)) • u s w)
        (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
      simpa [h0'] using hc
    have hut : ∀ t : ℝ, u t w = Complex.exp (z * t) • w := by
      intro t
      have h1 := congrArg (fun v => Complex.exp (z * t) • v) (hconst t)
      simp only [smul_smul] at h1
      rw [← Complex.exp_add] at h1
      simpa using h1
    apply hM
    intro t
    have hvec : (u t).HasEigenvector (Complex.exp (z * t)) w :=
      ⟨Module.End.mem_eigenspace_iff.2 (hut t), hw0⟩
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p t) hvec
    rw [hroot t] at h1
    have h2 : (p t).eval (Complex.exp (z * t)) • w = 0 := by
      rw [← h1]
      rfl
    exact (smul_eq_zero.1 h2).resolve_right hw0
  exact UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound E D M hskew hev x
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : ℝ → H →L[ℂ] H) (p : ℝ → ℂ[X]) (M : ℝ) (v y : H), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => u t v)) → HasDerivAt (fun t : ℝ => u t v) y 0 → (∀ t, aeval (u t) (p t) v = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ‖y‖ ≤ M * ‖v‖ := by
  intro H _ _ u p M v y h0 hadd hiso hfin hy hp hM
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ H, E = Submodule.span ℂ (Set.range fun t => u t v) := ⟨_, rfl⟩
  rw [← hE] at hfin
  haveI : FiniteDimensional ℂ E := hfin
  have hcomm : ∀ s t x, u s (u t x) = u t (u s x) := by
    intro s t x
    have h : u s * u t = u t * u s := by rw [← hadd, ← hadd, add_comm]
    exact DFunLike.congr_fun h x
  have h0' : ∀ a, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hstab : ∀ s, ∀ x ∈ E, u s x ∈ E := by
    intro s x hx
    rw [hE] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact Submodule.subset_span ⟨s + t, by simp [hadd]⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using Submodule.add_mem _ ha hb
    | smul c a _ ha => simpa using Submodule.smul_mem _ c ha
  have hvE : v ∈ E := by
    rw [hE]
    exact Submodule.subset_span ⟨0, h0' v⟩
  have hclosed : IsClosed (E : Set H) := Submodule.closed_of_finiteDimensional E
  have hlim : ∀ w ∈ E, ∀ d, HasDerivAt (fun t : ℝ => u t w) d 0 → d ∈ E := by
    intro w hw d hd
    have ht := hasDerivAt_iff_tendsto_slope.1 hd
    refine hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (E.restrictScalars ℝ).smul_mem _ (E.sub_mem (hstab t w hw) (hstab 0 w hw))
  have hsh : ∀ (s : ℝ) (w d : H), HasDerivAt (fun t : ℝ => u t w) d 0 →
      HasDerivAt (fun t : ℝ => u t (u s w)) (u s d) 0 := by
    intro s w d hd
    let LR : H →L[ℝ] H := (u s).restrictScalars ℝ
    have h1 : HasDerivAt (fun t : ℝ => LR (u t w)) (LR d) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 hd
    have h2 : (fun t : ℝ => LR (u t w)) = fun t => u t (u s w) := by
      funext t
      exact hcomm s t w
    rw [h2] at h1
    exact h1
  have hder : ∀ w ∈ E, ∃ d, HasDerivAt (fun t : ℝ => u t w) d 0 := by
    intro w hw
    rw [hE] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact ⟨u s y, hsh s v y hy⟩
    | zero => exact ⟨0, by simpa using hasDerivAt_const (0 : ℝ) (0 : H)⟩
    | add a b _ _ ha hb =>
      obtain ⟨da, hda⟩ := ha
      obtain ⟨db, hdb⟩ := hb
      refine ⟨da + db, ?_⟩
      convert hda.add hdb using 1
      funext t
      simp
    | smul c a _ ha =>
      obtain ⟨da, hda⟩ := ha
      refine ⟨c • da, ?_⟩
      convert hda.const_smul c using 1
      funext t
      simp
  have hd : ∀ w : E, HasDerivAt (fun t : ℝ => u t (w : H)) (deriv (fun t : ℝ => u t (w : H)) 0) 0 := by
    intro w
    obtain ⟨d, hd⟩ := hder w w.2
    rw [hd.deriv]
    exact hd
  let D : Module.End ℂ E :=
    { toFun := fun w => ⟨deriv (fun t : ℝ => u t (w : H)) 0, hlim _ w.2 _ (hd w)⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        refine (hd (a + b)).unique ?_
        convert (hd a).add (hd b) using 1
        · funext t
          simp
      map_smul' := by
        intro c a
        apply Subtype.ext
        refine (hd (c • a)).unique ?_
        convert (hd a).const_smul c using 1
        · funext t
          simp
      }
  let u' : ℝ → Module.End ℂ E := fun t => (u t : H →ₗ[ℂ] H).restrict (hstab t)
  have hu' : ∀ t (x : E), ((u' t x : E) : H) = u t (x : H) := fun t x => rfl
  have hD : ∀ x : E, ((D x : E) : H) = deriv (fun t : ℝ => u t (x : H)) 0 := fun x => rfl
  have haev : ∀ (t : ℝ) (q : ℂ[X]) (x : E), ((aeval (u' t) q x : E) : H) = aeval (u t) q (x : H) := by
    intro t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul (aeval (u' t)) (C a * X ^ n) X, map_mul (aeval (u t)) (C a * X ^ n) X, aeval_X, aeval_X, Module.End.mul_apply, ContinuousLinearMap.mul_apply, ih, hu']
  have hcq : ∀ (s t : ℝ) (q : ℂ[X]) (x : H), aeval (u t) q (u s x) = u s (aeval (u t) q x) := by
    intro s t q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [aeval_C]
    | add f g hf hg =>
      intro x
      simp [hf, hg]
    | monomial n a ih =>
      intro x
      have h1 : (C a * X ^ (n + 1) : ℂ[X]) = (C a * X ^ n) * X := by ring
      rw [h1, map_mul, aeval_X, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm t s, ih]
  have hkill : ∀ t, ∀ x ∈ E, aeval (u t) (p t) x = 0 := by
    intro t x hx
    rw [hE] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      show aeval (u t) (p t) (u s v) = 0
      rw [hcq, hp, map_zero]
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have hder' : ∀ x : E, HasDerivAt (fun t : ℝ => u' t x) (D x) 0 := by
    intro x
    rw [hasDerivAt_iff_tendsto_slope]
    have h := hasDerivAt_iff_tendsto_slope.1 (hd x)
    rw [tendsto_subtype_rng]
    refine h.congr fun t => ?_
    simp [slope_def_module, hu']
  have hbound := UpperTheory.norm_generator_le_of_polynomial_annihilated E u' D p M
    (by
      ext x
      simp [hu', h0'])
    (by
      intro s t
      ext x
      simp [hu', hadd])
    (by
      intro t x
      exact hiso t x)
    hder'
    (by
      intro t
      ext x
      rw [haev]
      simpa using hkill t x x.2)
    hM ⟨v, hvE⟩
  have hDv : ((D ⟨v, hvE⟩ : E) : H) = y := by
    rw [hD]
    exact hy.deriv
  have hn : ‖D ⟨v, hvE⟩‖ = ‖y‖ := by
    rw [← hDv]
    rfl
  rw [hn] at hbound
  exact hbound
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsBoundOfIsRootExpMulForall
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_bound_of_isRoot_exp_mul_forall :
    ∀ (d : ℕ) (p : ℝ → ℂ[X]), (∀ t, p t ≠ 0 ∧ (p t).natDegree ≤ d) → ∃ M : ℝ, ∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M := by
  intro d p hp
  classical
  have hfin : Set.Finite {z : ℂ | ∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))} := by
    by_contra hinf
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    obtain ⟨R, hR⟩ := (F.finite_toSet.isBounded).exists_norm_le
    set S : ℝ := |R| + 1 with hS
    have hSpos : 0 < S := by positivity
    have hRS : ∀ z ∈ F, ‖z‖ ≤ S := fun z hz => by
      have h1 := hR z (Finset.mem_coe.mpr hz)
      have h2 := le_abs_self R
      linarith
    set t : ℝ := S⁻¹ with ht
    have htpos : 0 < t := inv_pos.mpr hSpos
    have hn : ∀ z ∈ F, ‖z * (t : ℂ)‖ ≤ 1 := fun z hz => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos, ht]
      rw [mul_inv_le_iff₀ hSpos, one_mul]
      exact hRS z hz
    have hinj : Set.InjOn (fun z : ℂ => Complex.exp (z * (t : ℂ))) F := by
      intro z hz w hw h
      obtain ⟨n, hn'⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
      have h1 := hn z hz
      have h2 := hn w hw
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ ≤ 2 := by
        have : (n : ℂ) * (2 * Real.pi * Complex.I) = z * t - w * t := by rw [hn']; ring
        rw [this]
        have := norm_sub_le (z * (t : ℂ)) (w * t)
        linarith
      have hn0 : n = 0 := by
        by_contra hne
        have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hne
        have h5 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
          simp [abs_of_pos Real.pi_pos]
        have h6 := Real.pi_gt_three
        rw [h5] at h3
        nlinarith
      rw [hn0] at hn'
      have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
      have : z * (t : ℂ) = w * t := by simpa using hn'
      exact mul_right_cancel₀ htne this
    have hsub : (F.image (fun z : ℂ => Complex.exp (z * (t : ℂ)))).val ⊆ (p t).roots := by
      intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hx)
      exact (Polynomial.mem_roots (hp t).1).mpr (hF (Finset.mem_coe.mpr hz) t)
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj, hcard] at hle
    have := (hp t).2
    omega
  obtain ⟨M, hM⟩ := hfin.isBounded.exists_norm_le
  exact ⟨M, fun z hz => hM z hz⟩
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem pow_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (k : archCompact K n) (m : ℕ) :
    ∀ φ ∈ centralCuspForms K n, (archRepT μ (k : archGroup K n) ^ m) (cuspVecL μ φ) =
      cuspVecL μ (((gkModuleCusp K n).σ k ^ m) φ) := by
  induction m with
  | zero =>
    intro φ _
    simp
  | succ m ih =>
    intro φ hφ
    rw [pow_succ, pow_succ, ContinuousLinearMap.mul_apply, Module.End.mul_apply, ← cuspToL2_sigma μ k hφ,
      ih _ (σ_mem_centralCuspForms k hφ)]

private theorem aeval_cuspVecL {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n)))
    [μ.IsHaarMeasure] (k : archCompact K n) (q : ℂ[X]) {φ : cuspForms K n}
    (hφ : φ ∈ centralCuspForms K n) :
    aeval (archRepT μ (k : archGroup K n)) q (cuspVecL μ φ) =
      cuspVecL μ (aeval ((gkModuleCusp K n).σ k) q φ) := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add (f := _), ContinuousLinearMap.add_apply, LinearMap.add_apply, ha, hb]
  | monomial m c =>
    rw [aeval_monomial, aeval_monomial, Module.End.mul_apply, ContinuousLinearMap.mul_apply,
      pow_cuspVecL μ k m φ hφ]
    simp [Algebra.algebraMap_eq_smul_one]

theorem UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (d : ℕ) (p : archCompact K n → ℂ[X]) (Y : (isExpLieAlgebra K n).lieSubalgebra), (∀ k, p k ≠ 0 ∧ (p k).natDegree ≤ d) → (∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y) ∈ archCompact K n) → ∃ M : ℝ, ∀ φ ∈ centralCuspForms K n, (∀ k, aeval ((gkModuleCusp K n).σ k) (p k) φ = 0) → ‖cuspVecL μ ((gkModuleCusp K n).ρ Y φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
  intro K _ _ n μ _ d p Y hp hk
  let kk : ℝ → archCompact K n := fun t => ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y), hk t⟩
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_isRoot_exp_mul_forall d (fun t => p (kk t)) (fun t => hp _)
  refine ⟨M, fun φ hφ hkill => ?_⟩
  have hy := (isExpLieAlgebra K n).hasDerivAt_derivOp (archRepT μ) (isSmoothVector_cuspToL2 μ hφ)
    ((isExpLieAlgebra K n).ofLie Y)
  have e := derivOp_cuspVecL μ hφ ((isExpLieAlgebra K n).ofLie Y)
  rw [IsExpLieAlgebra.toLie_ofLie] at e
  rw [e] at hy
  have hu : ∀ t : ℝ, (archRepT μ ((kk t : archCompact K n) : archGroup K n)) =
      archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) := fun t => rfl
  refine UpperTheory.norm_deriv_orbit_le_of_polynomial_annihilated (CuspL2 μ)
    (fun t => archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)))
    (fun t => p (kk t)) M (cuspVecL μ φ) _ ?_ ?_ ?_ ?_ hy ?_ hM
  · ext1 x
    simp [(isExpLieAlgebra K n).expG_zero]
  · intro s t
    ext1 x
    rw [(isExpLieAlgebra K n).expG_add_smul, BanachRep.map_mul_apply]
    rfl
  · intro t x
    rw [archRepT_apply]
    exact UnitaryRep.norm_map _ _ _
  · have hfin := (gkModuleCusp K n).locallyFinite φ
    have hle : Submodule.span ℂ (Set.range fun t : ℝ =>
        archRepT μ ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie Y)) (cuspVecL μ φ)) ≤
        (Submodule.span ℂ (Set.range fun k => (gkModuleCusp K n).σ k φ)).map (cuspVecL μ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨t, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨kk t, rfl⟩, cuspToL2_sigma μ (kk t) hφ⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro t
    have := aeval_cuspVecL μ (kk t) (p (kk t)) hφ
    rw [hkill, map_zero] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalCuspFormsOfLevelAndDerivOpBound
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsNhdsDisplacementLeHalfOfDerivOpBound
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.NormExpSmulSubLeNormDerivOp
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_exp_smul_sub_le_norm_derivOp :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E) (X : 𝔤), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → ‖π (h.expG X) v - v‖ ≤ ‖h.derivOp π X v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h E _ _ π v X hπ hv
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => π (h.expG (s • X)) v)
      (π (h.expG (t • X)) (h.derivOp π X v)) t := by
    intro t
    have h2 := ((π (h.expG (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (h.hasDerivAt_derivOp π hv X)
    have h3 : HasDerivAt (fun s : ℝ => π (h.expG ((t + s) • X)) v)
        (π (h.expG (t • X)) (h.derivOp π X v)) (t - t) := by
      rw [sub_self]
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
      rw [h.expG_add_smul, BanachRep.map_mul_apply]
    have h4 := h3.comp_sub_const t t
    simpa only [add_sub_cancel] using h4
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun s : ℝ => π (h.expG (s • X)) v)
    (f' := fun t : ℝ => π (h.expG (t • X)) (h.derivOp π X v)) (C := ‖h.derivOp π X v‖)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => (hπ _ _).le)
  simpa using hm
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound :
    ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (C : ℝ), ∃ N ∈ 𝓝 (1 : G), ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (v : E), (∀ g w, ‖π g w‖ = ‖w‖) → h.IsSmoothVector π v → (∀ i, ‖h.derivOp π (h.ofLie (b i)) v‖ ≤ C * ‖v‖) → ∀ a ∈ N, ‖π a v - v‖ ≤ 1 / 2 * ‖v‖ := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b C
  let T : 𝔤 →ₗ[ℝ] h.lieSubalgebra :=
    { toFun := h.toLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let S : h.lieSubalgebra →ₗ[ℝ] 𝔤 :=
    { toFun := h.ofLie, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hST : ∀ X : 𝔤, S (T X) = X := fun _ => rfl
  let f : 𝔤 → ℝ := fun X => (∑ i, |b.repr (h.toLie X) i|) * |C|
  have hf : Continuous f := by
    refine Continuous.mul (continuous_finsetSum _ fun i _ => ?_) continuous_const
    exact (LinearMap.continuous_of_finiteDimensional ((b.coord i) ∘ₗ T)).abs
  have hf0 : f 0 = 0 := by
    have : h.toLie 0 = 0 := rfl
    simp [f, this]
  have hO : {X : 𝔤 | f X < 1 / 2} ∈ 𝓝 (0 : 𝔤) :=
    (isOpen_lt hf continuous_const).mem_nhds (by simp [hf0])
  have h0 : (0 : 𝔤) ∈ (h.chart 1).symm.source := h.zero_mem_nhd
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext
    simp [IsExpLieAlgebra.coe_expG]
  refine ⟨h.expG '' {X : 𝔤 | f X < 1 / 2}, ?_, ?_⟩
  · have h1 := (h.chart 1).symm.image_mem_nhds h0 hO
    have e1 : (h.chart 1).symm 0 = 1 := by
      show 1 * h.expG 0 = 1
      rw [hexp0, one_mul]
    rw [e1] at h1
    refine Filter.mem_of_superset h1 ?_
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨X, hX, ?_⟩
    show h.expG X = 1 * h.expG X
    rw [one_mul]
  · rintro E _ _ π v hπ hv hb _ ⟨X, hX, rfl⟩
    refine (UpperTheory.norm_exp_smul_sub_le_norm_derivOp 𝔸 G 𝔤 h E π v X hπ hv).trans ?_
    have hsum : X = ∑ i, b.repr (h.toLie X) i • h.ofLie (b i) := by
      conv_lhs => rw [← hST X]
      show S (h.toLie X) = _
      conv_lhs => rw [← b.sum_repr (h.toLie X)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul S _ _
    have hD : h.derivOp π X v =
        ∑ i, b.repr (h.toLie X) i • h.derivOp π (h.ofLie (b i)) v := by
      show fderiv ℝ (h.expOrbit π v) 0 X = ∑ i, b.repr (h.toLie X) i •
        fderiv ℝ (h.expOrbit π v) 0 (h.ofLie (b i))
      conv_lhs => rw [hsum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    have hbound : ‖h.derivOp π X v‖ ≤ f X * ‖v‖ := by
      rw [hD]
      refine (norm_sum_le _ _).trans ?_
      simp only [f, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, Real.norm_eq_abs, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (hb i).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg v))
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_of_lt hX) (norm_nonneg v))
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalOfCompactNearIdentity
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_of_compact_near_identity :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (S : Submodule ℂ H), IsCompactOperator T → (∀ v ∈ S, ‖T v - v‖ ≤ 1 / 2 * ‖v‖) → FiniteDimensional ℂ S := by
  intro H _ _ _ T S hT hS
  have hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖ := by
    intro v hv
    have : closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
      closure_minimal (fun w hw => hS w hw) hcl
    exact this hv
  haveI : CompleteSpace S.topologicalClosure :=
    S.isClosed_topologicalClosure.completeSpace_coe
  let f : S.topologicalClosure →L[ℂ] H := T.comp S.topologicalClosure.subtypeL
  have hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖ := by
    intro x
    have h1 := hS' x.1 x.2
    have h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖ := by
      have : (x : H) = T x - (T x - x) := by abel
      calc ‖(x : H)‖ = ‖T x - (T x - x)‖ := congrArg norm this
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x‖ = ‖(x : H)‖ := rfl
    have h4 : f x = T x := rfl
    rw [h3, h4]
    push_cast
    linarith
  have hanti : AntilipschitzWith 2 f := f.antilipschitz_of_bound hf
  have hemb : IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  obtain ⟨K, hK, hKsub⟩ := IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1
  have hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    apply hKsub
    refine ⟨(x : H), ?_, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx
  haveI : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsNhdsOneNormOneGLFactorization
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_nhds_one_normOneGL_factorization :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (N : Set (archGroup K n)) (U : Subgroup (AdelicGLn.integralFiniteGL K n)), N ∈ 𝓝 (1 : archGroup K n) → IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → ∃ N' ∈ 𝓝 (1 : normOneGL (K := K) (n := n)), ∀ g ∈ N', ∃ a ∈ N, ∃ u ∈ U, g = archP K n a * retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n)) := by
  intro K _ _ n N U hN hU
  have hU' : IsOpen (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))) :=
    (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU
  have hp : Continuous fun g : normOneGL (K := K) (n := n) => AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n) :=
    (AdelicGLn.prodEquiv K n).continuous.comp continuous_subtype_val
  have ha : Continuous fun g : normOneGL (K := K) (n := n) =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1 :=
    (archEquiv K n).continuous.comp hp.fst
  have hf : Continuous fun g : normOneGL (K := K) (n := n) =>
      (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := hp.snd
  refine ⟨(fun g : normOneGL (K := K) (n := n) =>
      archEquiv K n (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).1) ⁻¹' N ∩
    (fun g : normOneGL (K := K) (n := n) => (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2) ⁻¹'
      (Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n))), Filter.inter_mem ?_ ?_, ?_⟩
  · refine ha.continuousAt.preimage_mem_nhds ?_
    simpa only [OneMemClass.coe_one, map_one, Prod.fst_one] using hN
  · refine (hU'.preimage hf).mem_nhds ⟨1, U.one_mem, ?_⟩
    simp only [OneMemClass.coe_one, map_one, Prod.snd_one]
  · rintro g ⟨hg, u, hu, e⟩
    refine ⟨_, hg, u, hu, ?_⟩
    have e' : (u : AdelicGLn.FiniteAdelicGL K n) = (AdelicGLn.prodEquiv K n (g : AdelicGLn.AdelicGL K n)).2 := e
    rw [e']
    calc g = retractOne (g : AdelicGLn.AdelicGL K n) := (retractOne_coe g).symm
      _ = retractOne (infEmb K n (archEquiv K n (AdelicGLn.prodEquiv K n g).1) *
            finEmb K n (AdelicGLn.prodEquiv K n g).2) := by rw [infEmb_mul_finEmb]
      _ = _ := by rw [retractOne_mul, retract_infEmb]
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsApproximateIdentityIntegrated
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_approximate_identity_integrated :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [OpensMeasurableSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (N : Set G), N ∈ 𝓝 (1 : G) → ∃ f : CompactlySupportedContinuousMap G ℂ, ∀ (v : H) (r : ℝ), (∀ g ∈ N, ‖π g v - v‖ ≤ r) → ‖π.integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ r := by
  intro G H _ _ _ _ _ _ _ _ _ _ π μ _ _ N hN
  obtain ⟨U, hUsub, hUo, h1U⟩ := mem_nhds_iff.1 hN
  obtain ⟨h, h1, h0, hcs, hrange⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : G))) hUo.isClosed_compl
    (Set.disjoint_singleton_left.2 fun h => h h1U)
  have hnn : ∀ g, 0 ≤ h g := fun g => (hrange g).1
  set c : ℝ := ∫ g, h g ∂μ with hc
  have hcpos : 0 < c := h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs hnn
    (by rw [h1 (Set.mem_singleton 1)]; exact one_ne_zero)
  let k : G → ℝ := fun g => c⁻¹ * h g
  have hkc : Continuous k := continuous_const.mul h.continuous
  have hkcs : HasCompactSupport k := by
    have : k = (fun _ => c⁻¹) * (h : G → ℝ) := rfl
    rw [this]
    exact hcs.mul_left
  have hknn : ∀ g, 0 ≤ k g := fun g => mul_nonneg (inv_nonneg.2 hcpos.le) (hnn g)
  have hkint : Integrable k μ := hkc.integrable_of_hasCompactSupport hkcs
  have hk1 : ∫ g, k g ∂μ = 1 := by
    simp only [k]
    rw [integral_const_mul, ← hc, inv_mul_cancel₀ hcpos.ne']
  let f : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun g => (k g : ℂ), by fun_prop⟩, hkcs.comp_left Complex.ofReal_zero⟩
  have hfg : ∀ g, f g = (k g : ℂ) := fun _ => rfl
  refine ⟨f, fun v r hr => ?_⟩
  have hint1 : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hint2 : Integrable (fun g => f g • v) μ :=
    (f.continuous.smul continuous_const).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  have hv : ∫ g, f g • v ∂μ = v := by
    rw [integral_smul_const]
    simp only [hfg]
    have : ∫ g, (k g : ℂ) ∂μ = ((1 : ℝ) : ℂ) := by
      rw [← hk1]; exact integral_ofReal
    rw [this]
    simp
  have key : π.integrated μ (UnitaryRep.ccToL1 μ f) v - v = ∫ g, f g • (π g v - v) ∂μ := by
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, hv, UnitaryRep.integrated_ccToL1_apply]
  have hbound : ‖∫ g, f g • (π g v - v) ∂μ‖ ≤ ∫ g, k g * r ∂μ := by
    refine norm_integral_le_of_norm_le (hkint.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, hfg, Complex.norm_real, Real.norm_of_nonneg (hknn g)]
    by_cases hg : g ∈ U
    · exact mul_le_mul_of_nonneg_left (hr g (hUsub hg)) (hknn g)
    · have : k g = 0 := by
        simp only [k]
        rw [h0 hg]
        simp
      rw [this]
      simp
  rw [key]
  rw [integral_mul_const, hk1, one_mul] at hbound
  exact hbound
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

set_option maxHeartbeats 20000000 in
theorem UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (C : ℝ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (S : Submodule ℂ (cuspForms K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → S ≤ centralCuspForms K n → (∀ φ ∈ S, ∀ u ∈ U, finRepCusp K n (u : AdelicGLn.integralFiniteGL K n) φ = φ) → (∀ φ ∈ S, ∀ i, ‖cuspVecL μ ((gkModuleCusp K n).ρ (b i) φ)‖ ≤ C * ‖cuspVecL μ φ‖) → FiniteDimensional ℂ S := by
  intro K _ _ n μ _ d b C U S hU hS hfix hbound
  obtain ⟨N, hN, hNv⟩ := UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound _ _ _ (isExpLieAlgebra K n) d b C
  obtain ⟨N', hN', hN'd⟩ := UpperTheory.exists_nhds_one_normOneGL_factorization K n N U hN hU
  have hApprox := UpperTheory.exists_approximate_identity_integrated
    (normOneGL (K := K) (n := n)) (CuspL2 μ) (cuspRepT μ) μ N' hN'
  obtain ⟨f, hf⟩ := hApprox
  have key : ∀ v ∈ S.map (cuspVecL μ),
      ‖(cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ 1 / 2 * ‖v‖ := by
    rintro _ ⟨φ, hφ, rfl⟩
    apply hf (cuspVecL μ φ) (1 / 2 * ‖cuspVecL μ φ‖)
    intro g hg
    obtain ⟨a, ha, u, hu, rfl⟩ := hN'd g hg
    have hφ' : φ ∈ centralCuspForms K n := hS hφ
    have hfx : cuspRepT μ (retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n))) (cuspVecL μ φ) =
        cuspVecL μ φ := by
      rw [← cuspToL2_finRepCusp μ _ hφ', hfix φ hφ u hu]
    rw [(cuspRepT μ).map_mul_apply, hfx, ← archRepT_apply]
    refine hNv (CuspL2 μ) (archRepT μ) (cuspVecL μ φ) (fun g w => ?_)
      (isSmoothVector_cuspToL2 μ hφ') (fun i => ?_) a ha
    · rw [archRepT_apply]
      exact UnitaryRep.norm_map _ _ _
    · rw [derivOp_cuspVecL μ hφ']
      exact hbound φ hφ i
  haveI : FiniteDimensional ℂ (S.map (cuspVecL μ)) :=
    UpperTheory.finiteDimensional_of_compact_near_identity (CuspL2 μ) _ (S.map (cuspVecL μ)) (isCompactOperator_cuspRep μ f) key
  exact UnitaryAdmissible.finiteDimensional_of_map_mem (E := S.map (cuspVecL μ)) (cuspVecL μ)
    (fun x hx => Submodule.mem_map_of_mem hx)
    (fun x hx h => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hS hx) h)
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.NormApplyLeOfLaplacianLowerBound
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_apply_le_of_laplacian_lower_bound :
    ∀ (d : ℕ) (c C : ℝ) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∃ C' : ℝ, ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (A : Fin d → Module.End ℂ M), (∀ i, ∀ x ∈ V, A i x ∈ V) → (∀ i, ∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (A i x)) (j y) + inner ℂ (j x) (j (A i y)) = 0) → ∀ v ∈ V, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re → (∀ i, ε i = -1 → ‖j (A i v)‖ ≤ C * ‖j v‖) → ∀ i, ‖j (A i v)‖ ≤ C' * ‖j v‖ := by
  intro d c C ε hε
  refine ⟨Real.sqrt (|c| + (d + 1) * C ^ 2), ?_⟩
  intro M H _ _ _ _ j V A hA hskew v hv hcas hC i
  have h1 : ∀ k, inner ℂ (j v) (j (A k (A k v))) = -((‖j (A k v)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have h := hskew k v hv (A k v) (hA k v hv)
    rw [inner_self_eq_norm_sq_to_K] at h
    push_cast
    exact eq_neg_of_add_eq_zero_right h
  have h2 : (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re
      = -∑ k, ε k * ‖j (A k v)‖ ^ 2 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right, h1 k, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [h2] at hcas
  have h3 : ∀ k, ε k = -1 → ‖j (A k v)‖ ^ 2 ≤ C ^ 2 * ‖j v‖ ^ 2 := by
    intro k hk
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC k hk) 2
  have hCN : 0 ≤ C ^ 2 * ‖j v‖ ^ 2 := by positivity
  have h4 : ∀ k, 0 ≤ ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2 := by
    intro k
    rcases hε k with hk | hk
    · rw [hk]; positivity
    · have := h3 k hk
      rw [hk]; linarith
  have h5 : ε i * ‖j (A i v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2
      ≤ ∑ k, (ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2) :=
    Finset.single_le_sum (f := fun k => ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2)
      (fun k _ => h4 k) (Finset.mem_univ i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h5
  have hc : c * ‖j v‖ ^ 2 ≤ |c| * ‖j v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  have hc0 : 0 ≤ |c| * ‖j v‖ ^ 2 := by positivity
  have hd : 0 ≤ (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) := by positivity
  have h6 : ‖j (A i v)‖ ^ 2 ≤ (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2 := by
    have e : (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2
        = |c| * ‖j v‖ ^ 2 + (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) + C ^ 2 * ‖j v‖ ^ 2 := by ring
    rw [e]
    rcases hε i with hk | hk
    · rw [hk] at h5; linarith
    · have := h3 i hk
      linarith
  have h7 := Real.le_sqrt_of_sq_le h6
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at h7
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.ConvolutionTheory.C.nearFinite :
    UpperTheory.ConvolutionTheory.C.NearFinite := by
  intro K _ _ n ι _ _ b ε hε horth U hU X _ _ _ τ c
  obtain ⟨B, hB, hsym, d, b', ε', hε', horth', hK⟩ := UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact K n
  have hcas : casimir b ε = casimir b' ε' :=
    UpperTheory.casimir_eq_of_orthonormal_bases _ B ι (Fin d) b ε b' ε' hsym hε (fun i j => by rw [hB, horth])
      (fun i => by rcases hε' i with h | h <;> rw [h] <;> norm_num) horth'
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (normOneGL (K := K) (n := n)), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have hM : ∀ i, ∃ M : ℝ, ε' i = -1 → ∀ φ ∈ centralCuspForms K n,
      (∀ k, Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k)) φ = 0) →
      ‖cuspVecL μ ((gkModuleCusp K n).ρ (b' i) φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
    intro i
    by_cases hi : ε' i = -1
    · obtain ⟨M, hM⟩ := UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero K n μ (Module.finrank ℂ X) (fun k => LinearMap.charpoly (τ k)) (b' i)
        (fun k => ⟨(LinearMap.charpoly_monic _).ne_zero, (LinearMap.charpoly_natDegree _).le⟩) (hK i hi)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose M hM using hM
  obtain ⟨C', hC'⟩ := UpperTheory.norm_apply_le_of_laplacian_lower_bound d c (∑ i, |M i|) ε' hε'
  rw [hcas]
  suffices key : ∀ s : Set (cuspForms K n), (∀ φ ∈ s, φ ∈ centralCuspForms K n ∧
      (∀ u ∈ U, ∀ g, φ.1 (g * finEmb K n (u : AdelicGLn.integralFiniteGL K n)) = φ.1 g) ∧
      (∃ f : X →ₗ[ℂ] cuspForms K n, (∀ k x g, (f (τ k x)).1 g = (f x).1 (g * infEmb K n (k : archGroup K n))) ∧
        φ ∈ LinearMap.range f) ∧
      ∃ (h : φ.1 ∈ archSmooth K n) (κ : ℂ), -c ≤ κ.re ∧
        uAction (casimir b' ε') ⟨φ.1, h⟩ = κ • ⟨φ.1, h⟩) → FiniteDimensional ℂ (Submodule.span ℂ s) from
    key _ fun _ h => h
  intro s hs
  have hcent : Submodule.span ℂ s ≤ centralCuspForms K n := Submodule.span_le.2 fun φ hφ => (hs φ hφ).1
  have hskew : ∀ Y, ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (cuspVecL μ ((gkModuleCusp K n).ρ Y x)) (cuspVecL μ y) +
        inner ℂ (cuspVecL μ x) (cuspVecL μ ((gkModuleCusp K n).ρ Y y)) = 0 :=
    fun Y x hx y hy => petersson_inner_lieAlgebra_skewAdjoint μ Y hx hy
  have hT : ∀ φ : cuspForms K n, uActionCusp K n (casimir b' ε') φ =
      ∑ i, (ε' i : ℂ) • (gkModuleCusp K n).ρ (b' i) ((gkModuleCusp K n).ρ (b' i) φ) := by
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [casimir, map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.mul_apply, gkModuleCusp_ρ_apply, Complex.coe_smul]
  have hsymT : ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (cuspVecL μ (uActionCusp K n (casimir b' ε') x)) (cuspVecL μ y) =
        inner ℂ (cuspVecL μ x) (cuspVecL μ (uActionCusp K n (casimir b' ε') y)) := by
    intro x hx y hy
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, hT, map_sum, map_sum, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hskew (b' i) _ (ρ_mem_centralCuspForms (b' i) hx) y hy
    have h2 := hskew (b' i) x hx _ (ρ_mem_centralCuspForms (b' i) hy)
    rw [map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (ε' i : ℂ) * (h1 - h2)
  have hlow := UpperTheory.re_inner_ge_of_span_eigenvectors _ _ (cuspVecL μ) (centralCuspForms K n) (uActionCusp K n (casimir b' ε')) c s hsymT
    (fun x hx => by
      obtain ⟨h1, -, -, h, κ, hκ, he⟩ := hs x hx
      exact ⟨h1, κ, hκ, Subtype.ext (congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ)) he)⟩)
  have hpoly : ∀ k, ∀ φ ∈ Submodule.span ℂ s,
      Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k)) φ = 0 := by
    intro k
    have hle : Submodule.span ℂ s ≤
        LinearMap.ker (Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k))) := by
      refine Submodule.span_le.2 ?_
      intro φ hφ
      obtain ⟨-, -, ⟨f, hf, x, rfl⟩, -⟩ := hs φ hφ
      have h := map_aeval_apply_of_intertwine f (A := τ k) (B := (gkModuleCusp K n).σ k)
        (fun m => Subtype.ext (funext fun g => hf k m g)) (LinearMap.charpoly (τ k)) x
      rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at h
      exact h.symm
    exact fun φ hφ => hle hφ
  refine UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound K n μ d b' C' U _ hU hcent (fun φ hφ u hu => ?_) (fun φ hφ => ?_)
  · have hle : Submodule.span ℂ s ≤ LinearMap.eqLocus
        (finRepCusp K n (u : AdelicGLn.integralFiniteGL K n)) LinearMap.id :=
      Submodule.span_le.2 fun ψ hψ => Subtype.ext (funext fun g => (hs ψ hψ).2.1 u hu g)
    exact hle hφ
  · refine hC' _ _ (cuspVecL μ) (centralCuspForms K n) (fun i => (gkModuleCusp K n).ρ (b' i))
      (fun i x hx => ρ_mem_centralCuspForms _ hx) (fun i => hskew (b' i)) φ (hcent hφ) ?_ fun i hi => ?_
    · rw [← hT]
      exact hlow φ hφ
    · refine (hM i hi φ (hcent hφ) fun k => hpoly k φ hφ).trans ?_
      refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (norm_nonneg _)
      exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
