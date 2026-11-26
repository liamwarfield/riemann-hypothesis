module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem GlobalTheory.WeierstrassCurve.isAbelianScheme_schemeOver :
    ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ →
      ∀ [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → IsAbelianScheme (schemeOver W) := by
  intro R _ W hΔ _ hc
  have hs := smoothOfRelativeDimension_toSpec_of_isUnit W hΔ
  exact ⟨hc, SmoothOfRelativeDimension.smooth 1 (toSpec W), isProper_toSpec W,
    geometricallyConnected_toSpec W⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ChartRig

variable {X Y : Scheme.{0}}

theorem res_pullU_eq (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U x) = Units.map (f.appLE U V h).hom.toMonoidHom x := by
  ext
  rfl

theorem res_res_pullU (f : Y ⟶ X) (U : X.Opens) (V W : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ V)
    (x : Γ(X, U)ˣ) : res h' (res h (pullU f U x)) = res (h'.trans h) (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl

theorem res_pullU_res (f : Y ⟶ X) (U U' : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : U' ≤ U)
    (h'' : V ≤ f ⁻¹ᵁ U) (x : Γ(X, U)ˣ) :
    res h (pullU f U' (res h' x)) = res h'' (pullU f U x) := by
  rw [res_pullU_eq, res_pullU_eq]
  ext
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U' V h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl

theorem exists_gen_pull (L : LB X) (f : Y ⟶ X) (i : L.ι) (hL : L.IsLB) (hi : ⊤ ≤ f ⁻¹ᵁ L.U i) :
    ∃ t : LB.Gen (L.pull f), t.IsGen := by
  have le1 : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => f) j ≤ f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U i) :=
    fun j => le_inf (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit) (le_top.trans hi)
  refine ⟨⟨fun j => res (le1 j) (pullU f _ (L.g (j PUnit.unit) i))⟩, fun j k => ?_⟩
  have le2 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => f) j PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => f) k PUnit.unit))
  have le3 : LB.wchart L (fun _ : PUnit => f) j ⊓ LB.wchart L (fun _ : PUnit => f) k ≤
      f ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (k PUnit.unit) ⊓ L.U i) :=
    le_inf le2 (le_top.trans hi)
  have gg : (L.pull f).g j k = res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit))) :=
    (Fintype.prod_unique (fun _ : PUnit =>
      (res le2 (pullU f _ (L.g (j PUnit.unit) (k PUnit.unit)))) ^ (1 : ℤ))).trans (zpow_one _)
  have c := congrArg (fun x => res le3 (pullU f _ x)) (hL.cocycle (j PUnit.unit) (k PUnit.unit) i)
  simp only [map_mul] at c
  rw [res_pullU_res f _ _ _ le3 _ le2, res_pullU_res f _ _ _ le3 _ (inf_le_right.trans (le1 k)),
    res_pullU_res f _ _ _ le3 _ (inf_le_left.trans (le1 j))] at c
  rw [gg]
  exact (res_res_pullU f _ _ _ (le1 j) inf_le_left _).trans
    (c.symm.trans (congrArg _ (res_res_pullU f _ _ _ (le1 k) inf_le_right _).symm))

end GlobalTheory.ChartRig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VolumeFundamentalDomainStdRealBasis
noncomputable section

open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.UnimodVol

def stdRealBasis (g : ℕ) : Module.Basis (Σ _ : Fin g, Fin 2) ℝ (Fin g → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem volume_fundamentalDomain_stdRealBasis (g : ℕ) :
    volume (ZSpan.fundamentalDomain (stdRealBasis g)) = 1 := by
  have h : ZSpan.fundamentalDomain (stdRealBasis g) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, stdRealBasis, Pi.basis_repr, Sigma.forall, Fin.forall_fin_two]
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]

theorem re_dotProduct_star {g : ℕ} (z w : Fin g → ℂ) :
    (z ⬝ᵥ star w).re = ∑ k, (stdRealBasis g).repr z k * (stdRealBasis g).repr w k := by
  simp [stdRealBasis, Pi.basis_repr, Fintype.sum_sigma, Fin.sum_univ_two, dotProduct]

theorem im_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (hermForm Hm z w).im = (z ⬝ᵥ star ((Complex.I • Hm.map star) *ᵥ w)).re := by
  have : star ((Complex.I • Hm.map star) *ᵥ w) = (-Complex.I) • Hm *ᵥ star w := by
    ext k
    simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this, dotProduct_smul, hermForm]
  simp

theorem det_gram_im {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by
  set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT
  have h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) =
      ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v) := by
    ext i j
    rw [Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]
    rfl
  have hd : LinearMap.det T = ‖Hm.det‖ ^ 2 := by
    have : (Hm.map star).det = star Hm.det := ((starRingEnd ℂ).map_det Hm).symm
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, Matrix.det_smul, this]
    simp
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    Module.Basis.det_comp, hd]
  ring

theorem posDef_of_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have h1 := hpos (star x) (by simpa using hx)
  have h2 := hH.im_star_dotProduct_mulVec_self x
  rw [hermForm, star_star] at h1
  exact Complex.pos_iff.2 ⟨h1, h2.symm⟩

theorem det_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    0 < Hm.det.re ∧ ‖Hm.det‖ = Hm.det.re := by
  have h := (posDef_of_hermForm hH hpos).det_pos
  exact ⟨(Complex.pos_iff.1 h).1, (Complex.re_eq_norm.2 h.le).symm⟩

end GlobalTheory.UnimodVol

namespace GlobalTheory

open UnimodVol

theorem volume_mul_det_eq_one_of_unimodular (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) : (volume Fd).toReal * Hm.det.re = 1 := by
  have : IsZLattice ℝ Λ := ⟨hfull⟩
  let b₁ := Module.Free.chooseBasis ℤ Λ
  let b := b₁.reindex ((b₁.ofZLatticeBasis ℝ Λ).indexEquiv (stdRealBasis g))
  have hvol : (volume Fd).toReal = |(stdRealBasis g).det (Subtype.val ∘ b)| := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain Λ volume hFd
    rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b (stdRealBasis g), Measure.real,
      volume_fundamentalDomain_stdRealBasis] at h1
    simpa [Measure.real] using h1.symm
  have hu := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Ef hbij) b b.dualBasis
  set M := LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective Ef hbij : Λ →ₗ[ℤ] Module.Dual ℤ Λ)
    with hM
  have hG : (Matrix.of fun i j => (hermForm Hm ((Subtype.val ∘ b) i) ((Subtype.val ∘ b) j)).im) =
      ((Int.castRingHom ℝ).mapMatrix M)ᵀ := by
    ext i j
    simp [hM, LinearMap.toMatrix_apply, hE]
  have hdet := det_gram_im Hm (Subtype.val ∘ b)
  rw [hG, Matrix.det_transpose, ← RingHom.map_det] at hdet
  obtain ⟨hp, hn⟩ := det_re_pos hH hpos
  have habs : |((M.det : ℤ) : ℝ)| = 1 := by
    rcases Int.isUnit_iff.1 hu with h | h <;> simp [h]
  rw [hn, eq_intCast] at hdet
  rw [hdet, ← mul_pow, abs_of_nonneg (sq_nonneg _), ← sq_abs, abs_mul, abs_of_pos hp,
    pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero] at habs
  rw [hvol, habs]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

noncomputable section

namespace GlobalTheory.WeierstrassLie

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem equation_inr (c : R) : (W.map (algebraMap R (DualNumber R))).toProjective.Equation
    ![TrivSqZeroExt.inr c, -1, 0] := by
  rw [equation_origin_iff]
  simp [pow_succ, TrivSqZeroExt.inr_mul_inr]

def vec (c : R) : Spec (.of (DualNumber R)) ⟶ scheme W :=
  ptHom W (algebraMap R (DualNumber R)) ![TrivSqZeroExt.inr c, -1, 0]
    (isUnimodularSol_origin (equation_inr W c))

theorem scale_vec (c : R) : spMap (epsScaleR c) ≫ vec W 1 = vec W c := by
  refine (SpecMap_ptHom W _ _ _ (epsScaleR c)).trans (ptHom_congr W _ _ _ ?_ ?_ _)
  · ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp

theorem vec_inj {c d : R} (e : vec W c = vec W d) : c = d := by
  rw [vec, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W c),
    ← SpecMap_originEval_chartY W _ _ _ (equation_inr W d), cancel_mono] at e
  have e' : originEval W _ _ _ (equation_inr W c) = originEval W _ _ _ (equation_inr W d) :=
    congrArg (·.hom) (Spec.map_injective e)
  have := RingHom.congr_fun e' (originZ W)
  rw [originEval_originZ, originEval_originZ] at this
  simpa using congrArg TrivSqZeroExt.snd this

theorem fst_vec (c : R) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ vec W c = zero W := by
  refine (SpecMap_ptHom W _ _ _ (TrivSqZeroExt.fstHom R R R).toRingHom).trans ?_
  rw [zero, ← pt_smul W (A := R) _ _ isUnit_one.neg]
  refine ptHom_congr W _ _ _ ?_ ?_ _
  · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
  · ext1 j
    fin_cases j <;> simp

theorem surjective_fst :
    Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  refine ⟨PrimeSpectrum.comap (algebraMap R (DualNumber R)) p, PrimeSpectrum.ext (Ideal.ext fun a => ?_)⟩
  change algebraMap R (DualNumber R) a.fst ∈ p.asIdeal ↔ a ∈ p.asIdeal
  have h : (TrivSqZeroExt.inr a.snd : DualNumber R) ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact zero_mem _)
  conv_rhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq a]
  exact (Ideal.add_mem_iff_left _ h).symm

theorem exists_eq_vec (g : Spec (.of (DualNumber R)) ⟶ scheme W)
    (hg : g ≫ toSpec W = spMap (algebraMap R (DualNumber R)))
    (h0 : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ g = zero W) : ∃ c, g = vec W c := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := surjective_fst p
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    have : q ∈ zero W ⁻¹ᵁ coordOpen W 1 := by
      rw [zero_preimage_coordOpen_one]; trivial
    rw [← h0] at this
    exact this
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map φ ≫ chartY W = g := hφ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : φ.hom.comp (algebraMap R (OriginRing W)) = algebraMap R (DualNumber R) := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have ha : (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ.hom =
      (originAug W : OriginRing W →+* R) := by
    rw [← hl, ← SpecMap_originAug_chartY, ← Category.assoc, cancel_mono] at h0
    exact congrArg (·.hom) (Spec.map_injective ((Spec.map_comp _ _).trans h0))
  have hz : (φ.hom (originZ W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originZ W)
  have hw : (φ.hom (originW W)).fst = 0 := (RingHom.congr_fun ha _).trans (originAug_originW W)
  have hw0 : φ.hom (originW W) = 0 := by
    have e := congrArg φ.hom ((equation_origin_iff _ _ _).mp (equation_originZ_originW W))
    simp only [map_add (f := _), map_mul, map_pow] at e
    ext
    · exact hw
    · rw [e]
      simp [pow_succ, hz, hw]
  have hz0 : φ.hom (originZ W) = TrivSqZeroExt.inr (φ.hom (originZ W)).snd := by
    ext <;> simp [hz]
  refine ⟨(φ.hom (originZ W)).snd, ?_⟩
  rw [← hl, vec, ← SpecMap_originEval_chartY W _ _ _ (equation_inr W _)]
  congr 2
  ext1
  refine origin_hom_ext W (fun r => ?_) ?_ ?_
  · exact (RingHom.congr_fun hc r).trans (originEval_algebraMap W _ _ _ (equation_inr W _) r).symm
  · exact hz0.trans (originEval_originZ W _ _ _ (equation_inr W _)).symm
  · exact hw0.trans (originEval_originW W _ _ _ (equation_inr W _)).symm

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R)
    [GrpObj (schemeOver W)], η[schemeOver W].left = zero W → ∃ v : epsR R ⟶ schemeOver W,
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W _ hη
  let v : epsR R ⟶ schemeOver W := Over.homMk (vec W 1) (ptHom_toSpec ..)
  have key : ∀ (c : Fin 1 → R) (w : epsR R ⟶ schemeOver W),
      IsLieComb c ![v] w ↔ w.left = vec W (c 0) := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : (List.ofFn u).prod = u 0 := by simp
      rw [this]
      exact (hu 0).trans (scale_vec W _)
    · intro h
      refine ⟨fun _ => w, fun i => ?_, by simp⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h.trans (scale_vec W _).symm
  refine ⟨v, ⟨isUnimodularSol_origin (equation_inr W 1), rfl⟩, fun i => ?_, fun w hw => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact (fst_vec W 1).trans hη.symm
  · obtain ⟨c, hc⟩ := exists_eq_vec W w.left (Over.w w) (hw.trans hη)
    refine ⟨fun _ => c, (key _ _).mpr hc, fun d hd => ?_⟩
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact vec_inj W (((key _ _).mp hd).symm.trans hc)

end GlobalTheory.WeierstrassLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeOfGenericallySurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem surjective_of_generic_fibre_subset_range
    {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Sp V) [UniversallyClosed f] [Flat g]
    (h : ∀ y : Y, g y ∈ Set.range (spMap (algebraMap V K)) → y ∈ Set.range f) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  let e : Sp V := (⊥ : PrimeSpectrum V)
  have hη : e ⤳ g y := (PrimeSpectrum.le_iff_specializes _ _).mp (bot_le (α := PrimeSpectrum V))
  obtain ⟨y', hy', hy''⟩ := Flat.generalizingMap g hη
  refine hy'.mem_closed hcl (h y' ?_)
  rw [hy'']
  refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap V K) ⊥ = ⊥
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)

theorem isAbelianScheme_of_generically_surjective :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
      [IsFractionRing V K] (B G : Over (Sp V)) [GrpObj B] [GrpObj G],
      IsAbelianScheme B → IsSemiAbelian G → ∀ ψ : B ⟶ G,
      (∀ x : G.left, G.hom x ∈ Set.range (spMap (algebraMap V K)) → x ∈ Set.range ψ.left) →
      IsAbelianScheme G := by
  intro V K _ _ _ _ _ _ B G _ _ hB hG ψ h
  have := hB.proper
  have := hG.smooth
  have := hG.separated
  have hw : ψ.left ≫ G.hom = B.hom := Over.w ψ
  have : IsProper (ψ.left ≫ G.hom) := hw ▸ hB.proper
  have : IsProper ψ.left := IsProper.of_comp ψ.left G.hom
  have : Surjective ψ.left := surjective_of_generic_fibre_subset_range ψ.left G.hom h
  have : UniversallyClosed G.hom := UniversallyClosed.of_comp_surjective ψ.left G.hom
  exact ⟨hG.comm, hG.smooth, ⟨⟩, hG.geomConnected⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPeriodPairOfLatticeInLine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_periodPair_of_lattice_in_line :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ), g = 1 → w ≠ 0 → DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ L : PeriodPair, ∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ := by
  intro g Λ w hg hw hdisc hspan
  subst hg
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext j
    fin_cases j
    simpa using h

  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] (Fin 1 → ℂ), ∀ z, e z = z • w := by
    let φ : ℂ →ₗ[ℝ] (Fin 1 → ℂ) :=
      { toFun := fun z => z • w
        map_add' := fun a b => add_smul a b w
        map_smul' := fun r z => by
          simp only [RingHom.id_apply]
          exact smul_assoc r z w }
    have hinj : Function.Injective φ := fun a b h => smul_left_injective ℂ hw h
    have hsurj : Function.Surjective φ := by
      intro y
      refine ⟨y 0 / w 0, ?_⟩
      funext j
      fin_cases j
      simp [φ, hw0]
    exact ⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun z => rfl⟩

  have : DiscreteTopology Λ := hdisc
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  set Λ' := ZLattice.comap ℝ Λ e.toLinearMap with hΛ'
  have hrank : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ Λ', Complex.finrank_real_complex]
  set b := Module.finBasisOfFinrankEq ℤ Λ' hrank with hb
  set bR := b.ofZLatticeBasis ℝ Λ' with hbR
  refine ⟨⟨bR 0, bR 1, ?_⟩, fun z => ?_⟩
  · have hv : ![bR 0, bR 1] = ⇑bR := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact bR.linearIndependent
  · have hr : ({bR 0, bR 1} : Set ℂ) = Set.range bR := by
      ext x
      simp [Fin.exists_fin_two, eq_comm]
    rw [PeriodPair.lattice]
    dsimp only
    rw [hr, hbR, Module.Basis.ofZLatticeBasis_span, ← SetLike.mem_coe, hΛ', ZLattice.coe_comap]
    simp [he]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqPtHomOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory

theorem exists_eq_ptHom_of_isLocalRing : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (A : Type) [CommRing A] [IsLocalRing A] (ρ : R →+* A) (x : Sp A ⟶ scheme W), x ≫ toSpec W = spMap ρ → ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
  intro R _ W A _ _ ρ x hx
  have key : ∀ i : Fin 3, x (IsLocalRing.closedPoint A) ∈ coordOpen W i →
      ∃ (P : Fin 3 → A) (h : IsUnimodularSol (W.map ρ) P), x = ptHom W ρ P h := by
    intro i hi
    have htop : x ⁻¹ᵁ coordOpen W i = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff (R := A) (x ⁻¹ᵁ coordOpen W i)).mp hi
    have hr : Set.range x ⊆ Set.range (awayChart W i) := by
      rintro _ ⟨y, rfl⟩
      have hy : y ∈ x ⁻¹ᵁ coordOpen W i := htop.ge trivial
      rw [← opensRange_awayChart] at hy
      exact hy
    obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift (awayChart W i) x hr)
    have hx' : x = Spec.map (CommRingCat.ofHom g.hom) ≫ awayChart W i := by
      rw [CommRingCat.ofHom_hom, hg, IsOpenImmersion.lift_fac]
    rw [SpecMap_awayChart] at hx'
    have hρ : g.hom.comp (awayConst W i) = ρ := by
      rw [hx', ptHom_toSpec] at hx
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
    subst hρ
    exact ⟨_, _, hx'⟩
  have h : x (IsLocalRing.closedPoint A) ∈ coordOpen W 1 ⊔ coordOpen W 2 := by
    rw [coordOpen_one_sup_coordOpen_two]
    trivial
  rcases h with h | h
  · exact key 1 h
  · exact key 2 h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUnitMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SameZeroScheme

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom a = _
  rw [← X.presheaf.map_comp]
  rfl

theorem top_le_preimage {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro x _
  apply h
  have : hU.fromSpec (Spec.map φ x) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
  rw [hU.range_fromSpec] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
theorem appLE_spec {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    {A : CommRingCat.{0}} (φ : Γ(Y, U) ⟶ A) :
    (Spec.map φ ≫ hU.fromSpec).appLE V ⊤ (top_le_preimage hU h φ) =
      Y.presheaf.map (homOfLE h).op ≫ φ ≫ (Scheme.ΓSpecIso A).inv := by
  have h1 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ V := by
    rw [← hU.fromSpec_preimage_self]
    exact fun x hx => h hx
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) hU.fromSpec V ⊤ ⊤ h1 le_top,
    Scheme.ΓSpecIso_inv_naturality]
  have e1 : hU.fromSpec.appLE V ⊤ h1 =
      Y.presheaf.map (homOfLE h).op ≫ (Scheme.ΓSpecIso Γ(Y, U)).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_of_le V h, Category.assoc, Category.assoc,
      ← Functor.map_comp]
    congr 1
  have e2 : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [e1, e2, Category.assoc]

theorem dvd_on_affine {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (h : U ≤ V)
    (a b : Γ(Y, V))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 → (t.appLE V ⊤ h).hom b = 0) :
    resG Y h a ∣ resG Y h b := by
  let I : Ideal Γ(Y, U) := Ideal.span {resG Y h a}
  let φ : Γ(Y, U) ⟶ CommRingCat.of (Γ(Y, U) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have key := H _ _ (top_le_preimage hU h φ)
  rw [appLE_spec hU h φ] at key
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).commRingCatIsoToRingEquiv.symm.injective
  have ha : Ideal.Quotient.mk I (resG Y h a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hb := key (by
    change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, U) ⧸ I))).inv.hom
      (Ideal.Quotient.mk I (resG Y h a)) = 0
    rw [ha]; exact map_zero _)
  have hb' : Ideal.Quotient.mk I (resG Y h b) = 0 :=
    hinj (hb.trans (map_zero _).symm)
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hb')

theorem exists_unit_mul (Y : Scheme.{0}) (V : Y.Opens) (a b : Γ(Y, V))
    (ha : ∀ (V' : Y.Opens) (h : V' ≤ V), resG Y h a ∈ nonZeroDivisors Γ(Y, V'))
    (H : ∀ (T : Scheme.{0}) (t : T ⟶ Y) (h : ⊤ ≤ t ⁻¹ᵁ V),
      (t.appLE V ⊤ h).hom a = 0 ↔ (t.appLE V ⊤ h).hom b = 0) :
    ∃ c : Γ(Y, V)ˣ, b = (c : Γ(Y, V)) * a := by
  let J := {U : Y.Opens // IsAffineOpen U ∧ U ≤ V}
  let W : J → Y.Opens := fun i => i.1
  have hW : ∀ i, W i ≤ V := fun i => i.2.2
  have hcov : ∀ y ∈ V, ∃ i, y ∈ W i := fun y hy => by
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    exact ⟨⟨U, hU, hUV⟩, hyU⟩
  have hc : V ≤ iSup W := fun y hy => TopologicalSpace.Opens.mem_iSup.2 (hcov y hy)
  have hloc : ∀ i, ∃ c : Γ(Y, W i), IsUnit c ∧ resG Y (hW i) b = c * resG Y (hW i) a := fun i => by
    obtain ⟨c, hc⟩ := dvd_on_affine i.2.1 (hW i) a b fun T t h => (H T t h).1
    obtain ⟨d, hd⟩ := dvd_on_affine i.2.1 (hW i) b a fun T t h => (H T t h).2
    refine ⟨c, ?_, hc.trans (mul_comm _ _)⟩
    have e : (c * d) * resG Y (hW i) a = 1 * resG Y (hW i) a := by
      rw [_root_.one_mul]
      conv_rhs => rw [hd, hc]
      ring
    exact IsUnit.of_mul_eq_one d ((mul_cancel_right_mem_nonZeroDivisors (ha _ (hW i))).1 e)
  choose u hu hub using hloc
  have hh : ∀ i j, resG Y (inf_le_left : W i ⊓ W j ≤ W i) (u i) = resG Y inf_le_right (u j) := by
    intro i j
    have e₁ := congrArg (resG Y (inf_le_left : W i ⊓ W j ≤ W i)) (hub i)
    have e₂ := congrArg (resG Y (inf_le_right : W i ⊓ W j ≤ W j)) (hub j)
    rw [map_mul, res_res, res_res] at e₁ e₂
    exact (mul_cancel_right_mem_nonZeroDivisors (ha _ (inf_le_left.trans (hW i)))).1
      (e₁.symm.trans e₂)
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W V (fun i => homOfLE (hW i)) hc u hh
  have hs' : ∀ i, resG Y (hW i) (show Γ(Y, V) from s) = u i := hs
  have hunit : IsUnit (show Γ(Y, V) from s) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ V _ fun y hy => by
      obtain ⟨i, hi⟩ := hcov y hy
      have h1 := (hu i).map (Y.presheaf.germ (W i) y hi).hom
      rw [← hs' i] at h1
      have h2 := Y.presheaf.germ_res_apply (homOfLE (hW i)) y hi (show Γ(Y, V) from s)
      exact h2 ▸ h1
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  apply Y.sheaf.eq_of_locally_eq' W V (fun i => homOfLE (hW i)) hc
  intro i
  change resG Y (hW i) b = resG Y (hW i) ((show Γ(Y, V) from s) * a)
  rw [map_mul, hs', hub]

end GlobalTheory.SameZeroScheme
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SameZeroScheme

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((f.appLE U V h).hom a) = (f.appLE U W (h'.trans h)).hom a := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom a = _
  rw [Scheme.Hom.appLE_map]

theorem appLE_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : U ≤ U') (h'' : V ≤ f ⁻¹ᵁ U') (a : Γ(X, U')) :
    (f.appLE U V h).hom (resG X h' a) = (f.appLE U' V h'').hom a := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U V h).hom a = _
  rw [Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y T : Scheme.{0}} (t : T ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ t ⁻¹ᵁ V) (h'' : ⊤ ≤ (t ≫ f) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (t.appLE V ⊤ h').hom ((f.appLE U V h).hom a) = ((t ≫ f).appLE U ⊤ h'').hom a := by
  change (f.appLE U V h ≫ t.appLE V ⊤ h').hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]

theorem appLE_compat {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (f : Y ⟶ X) (i j : L.ι) {W : Y.Opens}
    (hi : W ≤ f ⁻¹ᵁ L.U i) (hj : W ≤ f ⁻¹ᵁ L.U j) (hij : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) :
    (f.appLE (L.U i) W hi).hom (θ.f i) =
      (res hij (pullU f (L.U i ⊓ L.U j) (L.g i j)) : Γ(Y, W)ˣ) * (f.appLE (L.U j) W hj).hom (θ.f j) := by
  have e := congrArg (f.appLE (L.U i ⊓ L.U j) W hij).hom (θ.compat i j)
  rw [map_mul] at e
  exact (appLE_resG f hij inf_le_left hi _).symm.trans
    (e.trans (congrArg₂ (· * ·) rfl (appLE_resG f hij inf_le_right hj _)))

theorem unit_eq_of_mul {R : Type*} [CommRing R] {a a' b b' : R} {c c' g₀ g₁ : Rˣ}
    (ha : a ∈ nonZeroDivisors R) (h : b = c * a) (h' : b' = c' * a') (hb : b = g₀ * b')
    (haa : a = g₁ * a') : c = g₀ ^ (1 : ℤ) * g₁ ^ (-1 : ℤ) * c' := by
  apply Units.ext
  apply (mul_cancel_right_mem_nonZeroDivisors ha).1
  rw [← h, hb, h', zpow_one, zpow_neg_one, haa]
  have := g₁.inv_mul
  push_cast
  linear_combination (-(g₀ * c' * a' : R)) * this

theorem exists_isGen_linComb : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  intro X Y L θ φ ψ _ _ hψ H
  have h0 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L ![φ, ψ] j 0
  have h1 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ ψ ⁻¹ᵁ L.U (j 1) :=
    fun j => LB.wchart_le L ![φ, ψ] j 1
  have hc : ∀ j : Fin 2 → L.ι, ∃ c : Γ(Y, L.wchart ![φ, ψ] j)ˣ,
      (φ.appLE _ _ (h0 j)).hom (θ.f (j 0)) = c * (ψ.appLE _ _ (h1 j)).hom (θ.f (j 1)) := by
    intro j
    apply exists_unit_mul
    · intro V' h
      rw [resG_appLE]
      exact hψ _ _ _
    · intro T t h
      have k0 : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U (j 0) := fun x hx => h0 j (h hx)
      have k1 : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U (j 1) := fun x hx => h1 j (h hx)
      rw [appLE_appLE t φ _ h k0, appLE_appLE t ψ _ h k1]
      exact (H T t _ _ k0 k1).symm
  choose c hc using hc
  refine ⟨⟨c⟩, fun i j => ?_⟩
  let W : Y.Opens := L.wchart ![φ, ψ] i ⊓ L.wchart ![φ, ψ] j
  have wi : W ≤ L.wchart ![φ, ψ] i := inf_le_left
  have wj : W ≤ L.wchart ![φ, ψ] j := inf_le_right
  have ei := congrArg (resG Y wi) (hc i)
  have ej := congrArg (resG Y wj) (hc j)
  rw [map_mul, resG_appLE, resG_appLE] at ei ej
  have p0 : W ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) := le_inf (wi.trans (h0 i)) (wj.trans (h0 j))
  have p1 : W ≤ ψ ⁻¹ᵁ (L.U (i 1) ⊓ L.U (j 1)) := le_inf (wi.trans (h1 i)) (wj.trans (h1 j))
  have key := unit_eq_of_mul (c := res wi (c i)) (c' := res wj (c j)) (hψ _ _ _) ei ej
    (appLE_compat θ φ (i 0) (j 0) _ _ p0) (appLE_compat θ ψ (i 1) (j 1) _ _ p1)
  refine key.trans ?_
  congr 1
  exact (Fin.prod_univ_two (fun k : Fin 2 => (res (le_inf (wi.trans (LB.wchart_le L ![φ, ψ] i k))
    (wj.trans (LB.wchart_le L ![φ, ψ] j k)) : W ≤ (![φ, ψ] k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
    (pullU (![φ, ψ] k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ((![1, -1] : Fin 2 → ℤ) k))).symm

end GlobalTheory.SameZeroScheme
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isoLineBundle_of_regularPullbacks_sameZeroScheme : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  first | exact @GlobalTheory.SameZeroScheme.exists_isGen_linComb | exact GlobalTheory.SameZeroScheme.exists_isGen_linComb | (intros; apply GlobalTheory.SameZeroScheme.exists_isGen_linComb <;> assumption)
end
end
