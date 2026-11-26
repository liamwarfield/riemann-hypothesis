module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

namespace SmoothGrowth

theorem isOpenEmbedding_valGLInf :
    Topology.IsOpenEmbedding (fun g : GL (Fin n) (Cinf E) => fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) := by
  open scoped Matrix.Norms.Operator in exact Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) (Cinf E))

theorem isOpen_isUnit_ofInf : IsOpen {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} := by
  have := (isOpenEmbedding_valGLInf (E := E) (n := n)).isOpen_range
  convert this using 1
  ext x
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨u, hu⟩⟩

theorem continuousOn_toGLInf :
    ContinuousOn (fun x : Fin n → Fin n → Cinf E => toGLInf (Matrix.of x)) {x | IsUnit (Matrix.of x)} := by
  rw [isOpenEmbedding_valGLInf.isInducing.continuousOn_iff]
  exact continuousOn_id.congr fun x hx => val_toGLInf hx

theorem continuous_compGL (w : InfinitePlace E) : Continuous (compGL (n := n) w) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) := Units.continuous_val
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))
  · have h : Continuous fun g : GL (Fin n) (Cinf E) => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) :=
      Units.continuous_coe_inv
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have e : (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j) =
        fun g => ((g⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j w := by
      funext g
      rw [← map_inv]; rfl
    change Continuous (fun g : GL (Fin n) (Cinf E) => ((compGL w g)⁻¹ : GL (Fin n) ℂ).val i j)
    rw [e]
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp h))

theorem continuous_htInf : Continuous (htInf : GL (Fin n) (Cinf E) → ℝ) := by
  unfold htInf
  exact continuous_finsetProd _ fun w _ => continuous_htGL.comp (continuous_compGL w)

theorem htInf_pos' (g : GL (Fin n) (Cinf E)) : 0 < htInf g := by
  unfold htInf
  exact Finset.prod_pos fun w _ => htGL_pos _

theorem htInf_mul_le (g h : GL (Fin n) (Cinf E)) : htInf (g * h) ≤ htInf g * htInf h := by
  unfold htInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun w _ => (htGL_pos _).le) fun w _ => ?_
  rw [map_mul]
  exact htGL_mul_le _ _

theorem measurable_comp_GLInf {X β : Type} [MeasurableSpace X] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    {F : GL (Fin n) (Cinf E) → β} (hF : Continuous F) {γ : X → GL (Fin n) (Cinf E)}
    (hγ : ∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) : Measurable fun x => F (γ x) := by
  letI : MeasurableSpace (GL (Fin n) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf E)) := ⟨rfl⟩
  have h : Measurable γ := (isOpenEmbedding_valGLInf.measurableEmbedding.measurable_comp_iff).1
    (Measurable.of_eval fun i => Measurable.of_eval fun j => hγ i j)
  exact hF.measurable.comp h

theorem measurable_toGLInf_entry (i j : Fin n) :
    Measurable fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
  classical
  have : (fun x : Fin n → Fin n → Cinf E => (toGLInf (Matrix.of x) : Matrix (Fin n) (Fin n) (Cinf E)) i j) =
      fun x => if x ∈ {x : Fin n → Fin n → Cinf E | IsUnit (Matrix.of x)} then x i j
        else (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j := by
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [toGLInf, h]
  rw [this]
  exact Measurable.ite isOpen_isUnit_ofInf.measurableSet (by fun_prop) measurable_const

theorem smoothMatInf_integrand_eq (α : (Fin n → Fin n → Cinf E) → ℂ)
    (hsub : tsupport α ⊆ {x | IsUnit (Matrix.of x)}) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E))
    (a : Fin n → Fin n → Cinf E) :
    α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a) = α a * W (g * toGLInf (Matrix.of a)) := by
  by_cases ha : a ∈ tsupport α
  · have hu : IsUnit (Matrix.of a) := hsub ha
    have : (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a =
        ((g * toGLInf (Matrix.of a) : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) := by
      rw [Units.val_mul, val_toGLInf hu]
    rw [this, onMatInf_val]
  · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul, zero_mul]

end SmoothGrowth

open SmoothGrowth

theorem isModGrowthInf_smoothMatInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ),
    Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} →
    ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  intro E _ _ n α hα hcs hsub W hW
  haveI : FirstCountableTopology (GL (Fin n) (Cinf E)) :=
    (isOpenEmbedding_valGLInf (E := E) (n := n)).isInducing.firstCountableTopology
  obtain ⟨hWc, C, N, hC⟩ := hW
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (pow_pos (htInf_pos' _) _)
  have hK : IsCompact (tsupport α) := hcs
  have hcont : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
    continuous_htInf.comp_continuousOn (continuousOn_toGLInf.mono hsub)
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn hcont
  set R : ℝ := max R₀ 1
  have hRb : ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R := fun a ha => by
    have := hR₀ a ha
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans (le_max_left _ _))
  have hαi : Integrable (fun a => ‖α a‖) (volume : Measure (Fin n → Fin n → Cinf E)) :=
    (hα.integrable_of_hasCompactSupport hcs).norm
  set F : GL (Fin n) (Cinf E) → (Fin n → Fin n → Cinf E) → ℂ := fun g a => α a * W (g * toGLInf (Matrix.of a)) with hF
  have hsm : smoothMatInf α W = fun g => ∫ a, F g a := by
    funext g
    unfold smoothMatInf
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => smoothMatInf_integrand_eq α hsub W g a)
  have hbound : ∀ g a, ‖F g a‖ ≤ ‖α a‖ * (C * R ^ N * htInf g ^ N) := by
    intro g a
    by_cases ha : a ∈ tsupport α
    · simp only [hF, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 : htInf (g * toGLInf (Matrix.of a)) ≤ htInf g * R :=
        (htInf_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hRb a ha) (htInf_pos' _).le)
      have h2 := pow_le_pow_left₀ (htInf_pos' _).le h1 N
      calc ‖W (g * toGLInf (Matrix.of a))‖ ≤ C * htInf (g * toGLInf (Matrix.of a)) ^ N := hC _
        _ ≤ C * (htInf g * R) ^ N := mul_le_mul_of_nonneg_left h2 hC0
        _ = C * R ^ N * htInf g ^ N := by ring
    · simp [hF, image_eq_zero_of_notMem_tsupport ha]
  have hmeas : ∀ g, AEStronglyMeasurable (F g) volume := fun g =>
    (hα.measurable.mul (measurable_comp_GLInf (F := fun q => W (g * q)) (by fun_prop)
      (fun i j => measurable_toGLInf_entry i j))).aestronglyMeasurable
  rw [hsm]
  refine ⟨?_, C * R ^ N * ∫ a, ‖α a‖, N, fun g => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have hev : ∀ᶠ g in nhds g₀, htInf g ≤ htInf g₀ + 1 :=
      (continuous_htInf.continuousAt).eventually (gt_mem_nhds (lt_add_one (htInf g₀))) |>.mono fun _ h => h.le
    refine continuousAt_of_dominated (bound := fun a => ‖α a‖ * (C * R ^ N * (htInf g₀ + 1) ^ N))
      (Filter.Eventually.of_forall hmeas) ?_ (hαi.mul_const _) ?_
    · filter_upwards [hev] with g hg
      refine Filter.Eventually.of_forall fun a => (hbound g a).trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (norm_nonneg _)
      exact pow_le_pow_left₀ (htInf_pos' _).le hg N
    · refine Filter.Eventually.of_forall fun a => ?_
      exact (continuous_const.mul (hWc.comp (continuous_id.mul continuous_const))).continuousAt
  · calc ‖∫ a, F g a‖ ≤ ∫ a, ‖α a‖ * (C * R ^ N * htInf g ^ N) :=
          norm_integral_le_of_norm_le (hαi.mul_const _) (Filter.Eventually.of_forall (hbound g))
      _ = C * R ^ N * (∫ a, ‖α a‖) * htInf g ^ N := by rw [integral_mul_const]; ring

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegrStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArchimedeanModerateGrowth_matrixSmoothingIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (α : (Fin n → Fin n → Cinf E) → ℂ), Continuous α → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → IsModGrowthInf (smoothMatInf α W) := by
  first | (exact @GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf) | (exact GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf) | (intros; apply GlobalTheory.JSW.MirCinf.isModGrowthInf_smoothMatInf  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv.MapIff

theorem eval₂_mul_of_isHomogeneous' {R S σ : Type} [CommRing R] [CommRing S] [Fintype σ] (g : R →+* S)
    (x : σ → S) (u : S) {F : MvPolynomial σ R} {d : ℕ} (hF : F.IsHomogeneous d) :
    MvPolynomial.eval₂ g (fun j => u * x j) F = u ^ d * MvPolynomial.eval₂ g x F := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hF (MvPolynomial.mem_support_iff.1 hm)
    rw [← this, Finsupp.weight_apply]
    simp [Finsupp.sum_fintype]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

section
variable {X Z : Scheme.{0}}

def gsH (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gsH_apply (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gsH r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_eval₂Hom {R σ : Type} [CommRing R] (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (g : R →+* Γ(X, U)) (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom g x F) =
      MvPolynomial.eval₂Hom ((gsH r z U h).comp g) (fun j => gs r z U (x j)) F := by
  rw [← gsH_apply r z U h, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  congr 2
  funext j
  exact gsH_apply r z U h _

theorem gs_cst_gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (c : R) :
    gs r z U (GlobalTheory.AbLaw.cst f U c) = gc (r ≫ f) z c := by
  rw [GlobalTheory.MapToProj.gs_cst f r z U h c, gs_eq _ z ⊤ trivial]
  rfl

theorem gs_eval_cst {R σ : Type} [CommRing R] (f : X ⟶ Sp R) (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U)
    (x : σ → Γ(X, U)) (F : MvPolynomial σ R) :
    gs r z U (MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst f U) x F) =
      MvPolynomial.eval₂Hom (gc (r ≫ f) z) (fun j => gs r z U (x j)) F := by
  rw [gs_eval₂Hom r z U h, show (gsH r z U h).comp (GlobalTheory.AbLaw.cst f U) = gc (r ≫ f) z from
    RingHom.ext fun c => (gsH_apply r z U h _).trans (gs_cst_gc f r z U h c)]

end

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem exists_combSec (hN : N.IsLB) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : ∃ s : Fin mB → LB.Sec (N.pull φ), ∀ j z q, φ z ∈ N.U q →
      gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q)) = comb a φ p c z q j := by
  have le : ∀ J : PUnit → N.ι, (N.pull φ).U J ≤ φ ⁻¹ᵁ N.U (J PUnit.unit) := fun J _ hy => mem_pull.1 hy
  let F : Fin mB → ∀ J : PUnit → N.ι, Γ(X, (N.pull φ).U J) := fun j J =>
    ∑ i, (p.appLE ⊤ ((N.pull φ).U J) le_top).hom (c i j) *
      (φ.appLE (N.U (J PUnit.unit)) ((N.pull φ).U J) (le J)).hom ((a i).f (J PUnit.unit))
  have hF : ∀ j (J : PUnit → N.ι) z, z ∈ (N.pull φ).U J →
      gs (𝟙 X) z ((N.pull φ).U J) (F j J) = comb a φ p c z (J PUnit.unit) j := by
    intro j J z hz
    simp only [F, comb]
    rw [GlobalTheory.AmpleSpan.gs_sum' (𝟙 X) z _ hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul (𝟙 X) z _ hz]
    exact congrArg₂ (· * ·) ((gs_appLE p ⊤ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
      ((gs_appLE φ _ _ _ (𝟙 X) z hz _).trans (by rw [Category.id_comp]))
  refine ⟨fun j => ⟨F j, fun J J' => fn_ext fun y hy => ?_⟩, fun j z q hz => hF j _ z (mem_pull.2 hz)⟩
  have hJ : φ y ∈ N.U (J PUnit.unit) := mem_pull.1 hy.1
  have hJ' : φ y ∈ N.U (J' PUnit.unit) := mem_pull.1 hy.2
  rw [gs_res (𝟙 X) y _ hy, gs_mul (𝟙 X) y _ hy, gs_res (𝟙 X) y _ hy, gs_unit (𝟙 X) y _ hy,
    gm_pull_g N φ (𝟙 X) y J J' hy.1 hy.2, hF j J y hy.1, hF j J' y hy.2, Category.id_comp]
  simp only [comb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_compat (a i) φ y hJ hJ']
  ring

end GlobalTheory.HomFixUniv.MapIff

namespace GlobalTheory.HomFixUniv

open MapIff

theorem formsOK_iff_exists_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg)
    (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H)
    (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)),
    GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c →
    (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔
      ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  intro Rg _ A₀ B₀ X T f fB N H mA mB a b φ p t c hE hH hN _ hG
  constructor
  · intro hF
    cases mB with
    | zero =>
      have : IsEmpty X := ⟨fun z => by
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, -⟩ := hG z q hq
        exact j.elim0⟩
      exact ⟨isInitialOfIsEmpty.to B₀, isInitialOfIsEmpty.hom_ext _ _, fun z => (IsEmpty.false z).elim⟩
    | succ n =>
      obtain ⟨s, hs⟩ := exists_combSec (mB := n + 1) hN a φ p c
      have hva : GlobalTheory.AbLaw.VeryAmpleBy fB H b := (GlobalTheory.AmpleSpan.embedsBy_spec_iff fB b).1 hE
      have hcov : ⨆ j, nonzeroLocus (s j) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        obtain ⟨q, hq⟩ := exists_chart hN (φ z)
        obtain ⟨j, hj⟩ := hG z q hq
        have hk : (𝟙 X : X ⟶ X) z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s j) (𝟙 X) z hk).2
          (by rw [hs j z q hq]; exact hj)⟩
      have hforms : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) Rg), F.IsHomogeneous d →
          (∀ k : H.ι, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0) →
          ∀ k : (N.pull φ).ι,
            MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst (p ≫ t) ((N.pull φ).U k)) (fun j => (s j).f k) F = 0 := by
        intro d F hFd hK k
        obtain ⟨q, rfl⟩ : ∃ q, k = fun _ => q := ⟨k PUnit.unit, rfl⟩
        refine fn_ext fun z hz => ?_
        have hq : φ z ∈ N.U q := mem_pull.1 hz
        have e : (fun j => gs (𝟙 X) z ((N.pull φ).U (fun _ => q)) ((s j).f (fun _ => q))) = comb a φ p c z q :=
          funext fun j => hs j z q hq
        rw [gs_eval_cst (p ≫ t) (𝟙 X) z _ hz, Category.id_comp, e, gs_eq (𝟙 X) z _ hz 0, map_zero, map_zero]
        exact hF d F hFd hK z q hq
      obtain ⟨Ψ, w, hΨ, -, hrel⟩ := GlobalTheory.exists_hom_of_veryAmpleBy Rg B₀ fB H n b hH hva X (p ≫ t) (N.pull φ) s
        (LB.isLB_linComb hN _ _) hcov hforms
      refine ⟨Ψ, hΨ, fun z q k hq hk j j' => ?_⟩
      have hz : z ∈ (N.pull φ).U (fun _ => q) := mem_pull.2 hq
      rw [hrel j z k (fun _ => q) hk hz, hrel j' z k (fun _ => q) hk hz, hs j z q hq, hs j' z q hq]
      ring
  · rintro ⟨Ψ, hΨ, hP⟩ d F hFd hK z q hq
    obtain ⟨j₀, hj₀⟩ := hG z q hq
    obtain ⟨j', hj'⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show Ψ z ∈ ⨆ j, nonzeroLocus (b j) by rw [hE.1]; trivial)
    obtain ⟨k, hk⟩ := GlobalTheory.AmpleSpan.exists_chart_of_mem (b j') hj'
    have hu' : IsUnit (gs Ψ z _ ((b j').f k)) := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b j') Ψ z hk).1 hj'
    have hPr := hP z q k hq hk
    have hB0 : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
      have hu : IsUnit (gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j') := hPr j' j₀ ▸ hu'.mul hj₀
      exact isUnit_of_mul_isUnit_left hu
    obtain ⟨u, hu⟩ := hj₀
    have hBC : ∀ j, gs Ψ z (H.U k) ((b j).f k) =
        (gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) * comb a φ p c z q j := fun j => by
      have h1 := hPr j j₀
      rw [← hu] at h1
      calc gs Ψ z (H.U k) ((b j).f k) = gs Ψ z (H.U k) ((b j).f k) * ↑u * ↑u⁻¹ := by simp
        _ = gs Ψ z (H.U k) ((b j₀).f k) * comb a φ p c z q j * ↑u⁻¹ := by rw [h1]
        _ = _ := by ring
    have hK' := congrArg (gs Ψ z (H.U k)) (hK k)
    rw [gs_eval_cst fB Ψ z _ hk, hΨ, gs_eq Ψ z _ hk 0, map_zero, map_zero, funext hBC,
      MvPolynomial.coe_eval₂Hom, eval₂_mul_of_isHomogeneous' _ _ _ hFd] at hK'
    have hl : IsUnit ((gs Ψ z (H.U k) ((b j₀).f k) * ↑u⁻¹) ^ d) := (hB0.mul u⁻¹.isUnit).pow d
    rw [MvPolynomial.coe_eval₂Hom]
    exact hl.mul_right_eq_zero.1 hK'

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingFormsIffProportionalPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishingForms_iff_proportional_pullbacks : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → φ ≫ f = p ≫ t → GlobalTheory.HomFixUniv.Generates a φ p c → (GlobalTheory.HomFixUniv.FormsOK a fB b φ p t c ↔ ∃ Ψ : X ⟶ B₀, Ψ ≫ fB = p ≫ t ∧ GlobalTheory.HomFixUniv.Proport a b φ p Ψ c) := by
  first | (exact @GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (exact GlobalTheory.HomFixUniv.formsOK_iff_exists_proport) | (intros; apply GlobalTheory.HomFixUniv.formsOK_iff_exists_proport  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateVacuumEntireGaussianGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateVacuumEntireGaussianGrowth
namespace GlobalTheory.ConjTranslate

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ConjJet
open scoped BigOperators

theorem mem_Th (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc a d _ _
    (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _ (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D hg cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  obtain ⟨hg, hperm⟩ := GlobalTheory.InducedType.induced_type D
  have hGT := mem_Th D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.ConjNorm.useNorm_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc Qbar ρ hρ hdata.2.1
    hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := hperm Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (thetaZeroNormSq_ne_zero_cmLattice D hg cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.GalExist.galEx_all D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y
    (2 * m) hy (by omega)
  have hgal := (GlobalTheory.GalTheta.gal_all D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1)
    (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [comb_one]; exact hA)
    (by rw [comb_one]; exact hAU y hy)).1
  rw [comb_one] at hgal
  rw [hgal]
  refine ⟨U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1, U_ne_zero D _ _ _ hne, fun z => ?_⟩
  have := sup_perm D hg cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
    hTh y' z
  rw [Hf_re, ← mul_div_assoc] at this
  exact this

theorem conj_any (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G)
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (ρ : Qbar →ₐ[ℚ] ℂ) :
    Differentiable ℂ (fnConj D Qbar ρ (U D (tor0 D cc δ) y G)) ∧
    fnConj D Qbar ρ (U D (tor0 D cc δ) y G) ≠ 0 ∧
    ∀ z, ‖fnConj D Qbar ρ (U D (tor0 D cc δ) y G) z‖ ^ 2 ≤ GlobalTheory.ColNorms.supConst D a d *
      normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
        (fnConj D Qbar ρ G) *
      Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / area (lamConj Qbar ρ (lamOf D cc δ))) := by
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc Qbar ρ hdata
  · exact conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy ρ hfix
  · obtain ⟨hd, hne, hle⟩ := conj_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy
      (rhoBar Qbar ρ) hfix
    obtain ⟨hTh, -⟩ := GlobalTheory.ThetaConj.useConj_all D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ
      hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [(hbar a d L L' G).1, htor, hn2, hL, area_conj] at hle
    rw [(hbar a d L L' _).1] at hd hne hle
    refine ⟨?_, fun h => hne ?_, fun z => ?_⟩
    · have := GlobalTheory.ThetaConj.differentiable_cBar hd
      rwa [GlobalTheory.ThetaConj.cBar_cBar] at this
    · rw [h]
      funext z
      simp [cBar]
    · have := hle (vBar D z)
      rw [cBar, GlobalTheory.ThetaConj.vBar_invol] at this
      simpa only [vBar, Complex.norm_conj] using this

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

theorem conj_translate : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ F : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → ∀ y, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl))) := by
  intro D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  obtain ⟨-, hAU, -⟩ := GlobalTheory.ThetaAlgebraic.taylor_algebraic D cc dl hc t0 ht a b L L' h1 h2 hev F hF
  obtain ⟨hd, hne, hle⟩ := conj_any D cc dl t0 hc ht a b L L' h1 h2 hev F hF y hy ρ
  exact ⟨GlobalTheory.ConjJet.U_diff D _ y F (mem_Th D cc dl t0 hc ht a b L L' h1 h2 F hF).1, hAU y hy,
    _, hd, (GlobalTheory.ConjSeries.taylor_fnConj D a b _ ρ _ hd hne).1, hle⟩

end GlobalTheory.ConjTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateVacuumEntireGaussianGrowthStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_torsion_translate_vacuum_entire_gaussian_growth : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ F : TaylorLogMetric.VC D a b → ℂ, StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F → ∀ y, StandardLatticesGL3.LaQ D (TaylorLogMetric.tor0 D cc dl) L L' y → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) y F) α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl))) := by
  first | exact @GlobalTheory.ConjTranslate.conj_translate | exact GlobalTheory.ConjTranslate.conj_translate | (intros; apply GlobalTheory.ConjTranslate.conj_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGro
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ConjComb

theorem normSq_nonneg (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} (La : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    0 ≤ TaylorLogMetric.normSq D T La G := by
  unfold TaylorLogMetric.normSq
  simp only [MeasureTheory.average_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg) (MeasureTheory.integral_nonneg fun z => by positivity)

theorem supConst_nonneg (D : D7) (a b : ℕ) : 0 ≤ supConst D a b := by
  have h : 0 ≤ D.host.rdE := by
    exact Real.rpow_nonneg (by positivity) _
  unfold supConst
  positivity

theorem sq_sum_le {k : ℕ} (c f : Fin k → ℂ) (n B : ℝ) (hB : 0 ≤ B) (hc : ∑ i, ‖c i‖ ≤ n) (hf : ∀ i, ‖f i‖ ^ 2 ≤ B) :
    ‖∑ i, c i * f i‖ ^ 2 ≤ n ^ 2 * B := by
  have h1 : ‖∑ i, c i * f i‖ ≤ n * √B := by
    calc ‖∑ i, c i * f i‖ ≤ ∑ i, ‖c i * f i‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖c i‖ * √B := Finset.sum_le_sum fun i _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hf i)) (norm_nonneg _)
      _ = (∑ i, ‖c i‖) * √B := (Finset.sum_mul _ _ _).symm
      _ ≤ n * √B := mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
  calc ‖∑ i, c i * f i‖ ^ 2 ≤ (n * √B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = n ^ 2 * B := by rw [mul_pow, Real.sq_sqrt hB]

theorem conj_pres : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  intro D cc dl t0 hC ht a b L L' hL hL' hev F₀ F n hF₀ hP ρ
  obtain ⟨k, r, y, hr, hy, hn, rfl⟩ := hP
  have h := fun i => GlobalTheory.T.conj_torsion_translate_vacuum_entire_gaussian_growth D cc dl t0 hC ht a b L L' hL hL' hev F₀ hF₀ (y i) (hy i) ρ
  choose h1 h2 F' h3 h4 h5 using h
  have hc : GlobalTheory.ThetaConj.CjF D TaylorLogMetric.Qbar ρ (fun z => ∑ i, r i * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc dl) (y i) F₀ z)
      (fun z => ∑ i, StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (r i) * F' i z) :=
    GlobalTheory.ThetaConj.CjF.sum Finset.univ fun i _ =>
      GlobalTheory.ThetaConj.CjF.mul ⟨h1 i, h3 i, fun α => ⟨h2 i α, h4 i α⟩⟩ (hr i)
  refine ⟨hc.1, fun α => (hc.2.2 α).1, _, hc.2.1, fun α => (hc.2.2 α).2, fun z => ?_⟩
  exact sq_sum_le _ _ n _
    (mul_nonneg (mul_nonneg (supConst_nonneg D a b) (normSq_nonneg _ _ _ _)) (Real.exp_pos _).le) (hn ρ) fun i => h5 i z

end GlobalTheory.ConjComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjTorsionTranslateCombinationEntireGaussianGroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_torsionTranslateCombination_entire_gaussianGrowth : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (t0 : ℂ), StandardLatticesGL3.Crv D cc dl → GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc dl) t0 → ∀ (a b : ℕ) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Even (a * b) → ∀ (F₀ F : TaylorLogMetric.VC D a b → ℂ) (n : ℝ), StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc dl) t0 L L' F₀ → Pres D (TaylorLogMetric.tor0 D cc dl) L L' F₀ F n → ∀ ρ : TaylorLogMetric.Qbar →ₐ[ℚ] ℂ, Differentiable ℂ F ∧ TaylorLogMetric.CoefIn D F TaylorLogMetric.Qbar ∧ ∃ F' : TaylorLogMetric.VC D a b → ℂ, Differentiable ℂ F' ∧ (∀ α, TaylorLogMetric.taylor D F' α = StandardLatticesGL3.cj TaylorLogMetric.Qbar ρ (TaylorLogMetric.taylor D F α)) ∧ ∀ z, ‖F' z‖ ^ 2 ≤ n ^ 2 * (supConst D a b * TaylorLogMetric.normSq D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) (TaylorLogMetric.La D (TaylorLogMetric.torConj D (TaylorLogMetric.tor0 D cc dl) TaylorLogMetric.Qbar ρ) L L') (TaylorLogMetric.fnConj D TaylorLogMetric.Qbar ρ F₀) * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / TaylorLogMetric.area (TaylorLogMetric.lamConj TaylorLogMetric.Qbar ρ (TaylorLogMetric.lamOf D cc dl)))) := by
  first | exact @GlobalTheory.ConjComb.conj_pres | exact GlobalTheory.ConjComb.conj_pres | (intros; apply GlobalTheory.ConjComb.conj_pres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAndIsPreconnected
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.SpecialisationPts

open GlobalTheory.AffinePoints GlobalTheory.CxPts

theorem nonempty_point (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem specializes_iff_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x z : X}
    (hz : z ∈ U) : x ⤳ z ↔ ∀ f : Γ(X, U), z ∈ X.basicOpen f → x ∈ X.basicOpen f := by
  refine ⟨fun h f hf => h.mem_open (X.basicOpen f).2 hf, fun h => ?_⟩
  rw [specializes_iff_forall_open]
  intro s hs hzs
  obtain ⟨g, hg, hzg⟩ := hU.exists_basicOpen_le (V := ⟨s, hs⟩) ⟨z, hzs⟩ hz
  exact hg (h g hzg)

theorem mem_basicOpen_iff_notMem {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) (f : Γ(X, U)) :
    x ∈ X.basicOpen f ↔ f ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f ↔ x ∈ X.basicOpen f := by
    change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f ↔ _
    rw [hU.fromSpec_primeIdealOf]
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl

theorem specializes_iff_ev {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) {y : GlobalTheory.CxPts p (RingHom.id ℂ)} (hy : y ∈ ptsIn p (RingHom.id ℂ) U) :
    x ⤳ y.1 (IsLocalRing.closedPoint ℂ) ↔
      ∀ f ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal, ev p (RingHom.id ℂ) U f y = 0 := by
  rw [specializes_iff_basicOpen hU (mem_ptsIn.1 hy)]
  refine forall_congr' fun f => ?_
  rw [mem_basicOpen_iff_notMem hU hx, ← mem_ptsIn, mem_ptsIn_basicOpen hy]
  exact not_imp_not

theorem nonempty_and_isPreconnected : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), LocallyOfFiniteType p →
    ∀ (U : X.Opens), IsAffineOpen U → ∀ x ∈ U,
    (∃ y : GlobalTheory.CxPts p (RingHom.id ℂ), y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧
      x ⤳ y.1 (IsLocalRing.closedPoint ℂ)) ∧
    _root_.IsPreconnected {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
  intro X p hp U hU x hx
  let : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p hp ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType ℂ Γ(X, U) := hft
  let P : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  have : P.IsPrime := (hU.primeIdealOf ⟨x, hx⟩).isPrime
  let Φ (φ : (Γ(X, U) ⧸ P) →ₐ[ℂ] ℂ) : GlobalTheory.CxPts p (RingHom.id ℂ) :=
    ofHom hU (φ.comp (Ideal.Quotient.mkₐ ℂ P)).toRingHom
      fun a => (φ.comp (Ideal.Quotient.mkₐ ℂ P)).commutes a
  have hmem (φ) : Φ φ ∈ ptsIn p (RingHom.id ℂ) U := ofHom_mem _ _ _
  have hev (φ) (f : Γ(X, U)) : ev p (RingHom.id ℂ) U f (Φ φ) = φ (Ideal.Quotient.mk P f) :=
    ev_ofHom _ _ _ f
  have hc : Continuous Φ := by
    refine continuous_iff_continuousAt.2 fun φ => tendsto_subtype_rng.2
      (GlobalTheory.Points.tendsto_of_isAffineOpen hU (hmem φ) (Filter.Eventually.of_forall hmem)
        fun f => ?_)
    have h := (continuous_eval (R := ℂ) (C := ℂ) (Ideal.Quotient.mk P f)).tendsto φ
    simp only [← hev] at h
    exact h
  have hr : Set.range Φ = {y : GlobalTheory.CxPts p (RingHom.id ℂ) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ U ∧ x ⤳ y.1 (IsLocalRing.closedPoint ℂ)} := by
    ext y
    constructor
    · rintro ⟨φ, rfl⟩
      refine ⟨mem_ptsIn.1 (hmem φ), (specializes_iff_ev hU hx (hmem φ)).2 fun f hf => ?_⟩
      rw [hev, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
    · rintro ⟨hy, hxy⟩
      have hy' := mem_ptsIn.2 hy
      let ψ : Γ(X, U) →ₐ[ℂ] ℂ :=
        { evHom hy' with commutes' := fun a => (ev_eq hy' _).symm.trans (ev_algX hy' a) }
      refine ⟨Ideal.Quotient.liftₐ P ψ fun f hf =>
        (ev_eq hy' f).symm.trans ((specializes_iff_ev hU hx hy').1 hxy f hf), ?_⟩
      refine Subtype.ext (GlobalTheory.Points.ext_of_valR hU (hmem _) hy' fun f => ?_)
      exact (hev _ f).trans (ev_eq hy' f).symm
  constructor
  · obtain ⟨φ⟩ := nonempty_point (Γ(X, U) ⧸ P)
    have h := Set.mem_range_self (f := Φ) φ
    rw [hr] at h
    exact ⟨_, h⟩
  · have := GlobalTheory.RootConst.preconnectedSpace_algHom (Γ(X, U) ⧸ P)
    rw [← hr]
    exact isPreconnected_range hc

end GlobalTheory.SpecialisationPts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X Z T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem comb_pull (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (r : Z ⟶ X) (z : Z) (q : N.ι) (h : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) (r ≫ p) c z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp r p z ⊤ trivial, gs_comp r φ z _ h]

theorem Generates.pull {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hg : Generates a φ p c) (r : Z ⟶ X) : Generates a (r ≫ φ) (r ≫ p) c := by
  intro z q hz
  obtain ⟨j, hj⟩ := hg (r z) q hz
  exact ⟨j, by rw [comb_pull a φ p c r z q hz]; exact hj.map _⟩

theorem Proport.pull {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hp : Proport a b φ p Ψ c) (r : Z ⟶ X) :
    Proport a b (r ≫ φ) (r ≫ p) (r ≫ Ψ) c := by
  intro z q k hq hk j j'
  rw [comb_pull a φ p c r z q hq, comb_pull a φ p c r z q hq, gs_comp r Ψ z _ hk, gs_comp r Ψ z _ hk,
    ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem gs_top_comp {S : Scheme.{0}} (t : T ⟶ S) (z : T) (x : Γ(S, ⊤)) :
    (t.stalkMap z).hom (gs (𝟙 S) (t z) ⊤ x) = gs (𝟙 T) z ⊤ (t.appTop x) := by
  rw [← gs_comp t (𝟙 S) z ⊤ trivial, Category.comp_id]
  have e := gs_pull (𝟙 T) t z ⊤ trivial x
  rw [Category.id_comp] at e
  exact e.symm

theorem proport_zero {S : Scheme.{0}} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {eA : S ⟶ A₀} {eB : S ⟶ B₀}
    {uA : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ} {uB : ∀ z : S, H.ι → (S.presheaf.stalk z)ˣ}
    {α : Fin mA → Γ(S, ⊤)} {β : Fin mB → Γ(S, ⊤)} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (ha : ∀ i, IsVal eA uA (a i) (α i)) (hb : ∀ j, IsVal eB uB (b j) (β j)) (hn : Normal t c α β) :
    Proport a b (t ≫ eA) (𝟙 T) (t ≫ eB) c := by
  intro z q k hq hk j j'
  have hc : ∀ j, comb a (t ≫ eA) (𝟙 T) c z q j =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uA (t z) q).val := by
    intro j
    simp only [comb]
    have e : ∀ i, gs (t ≫ eA) z (N.U q) ((a i).f q) =
        gs (𝟙 T) z ⊤ (t.appTop (α i)) * (t.stalkMap z).hom (uA (t z) q).val := by
      intro i
      rw [gs_comp t eA z _ hq, ha i (t z) q hq, map_mul, gs_top_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [e, hn j, gs_eq (𝟙 T) z ⊤ trivial, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
  have hbj : ∀ j, gs (t ≫ eB) z (H.U k) ((b j).f k) =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uB (t z) k).val := by
    intro j
    rw [gs_comp t eB z _ hk, hb j (t z) k hk, map_mul, gs_top_comp]
  rw [hc, hc, hbj, hbj]
  ring

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem snd_θ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : (snd (topS Rg) B).left ≫ θ B = 𝟙 _ := by
  have key : ∀ h : B ⟶ topS Rg, snd (topS Rg) B ≫ lift h (𝟙 B) = 𝟙 _ := by
    intro h
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply Over.OverMorphism.ext
      have : Mono (topS Rg).hom := by
        show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
      apply (cancel_mono (topS Rg).hom).1
      exact (Over.w _).trans (Over.w _).symm
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  rw [θ, ← Over.comp_left, key]
  rfl

theorem θ_comp_structure {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : θ B ≫ fA B = B.hom := by
  rw [θ]; exact Over.w _

end GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.hom_of_proport : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB T t A' B' _ _ φA' φB' Ψ c hH hvA hvB hA' hB' hΨ hgen hprop hnorm
  obtain ⟨hA, hB, hL, hM, -, -, -, hk, hva, -, hbB⟩ := hH
  have hA'ab : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hA'
  have hB'ab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'
  have hsnd : (snd (topS Rg) B).left ≫ B.hom = fA B := Over.w (snd (topS Rg) B)
  let Φl : A'.left ⟶ B'.left :=
    hB'.1.lift (Ψ ≫ (snd (topS Rg) B).left) A'.hom (by rw [Category.assoc, hsnd, hΨ])
  have hΦ1 : Φl ≫ φB' = Ψ ≫ (snd (topS Rg) B).left := hB'.1.lift_fst _ _ _
  have hΦ2 : Φl ≫ B'.hom = A'.hom := hB'.1.lift_snd _ _ _
  let Φ : A' ⟶ B' := Over.homMk Φl hΦ2
  have hΨΦ : Φ.left ≫ φB' ≫ θ B = Ψ := by
    show Φl ≫ φB' ≫ θ B = Ψ
    rw [← Category.assoc, hΦ1, Category.assoc, snd_θ, Category.comp_id]
  let e' : T ⟶ A'.left := η[A'].left
  have hEA : e' ≫ φA' = t ≫ eSec A := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hA'
  have hEB : (η[B'].left : T ⟶ B'.left) ≫ φB' = t ≫ eSec B := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hB'
  have hηA : e' ≫ A'.hom = 𝟙 T := Over.w η[A']
  have heB : eSec B ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hzero : e' ≫ Ψ = t ≫ eSec B ≫ θ B := by
    have hgen' := hgen.pull e'
    have hprop' := hprop.pull e'
    rw [← Category.assoc, hEA, hηA, Category.assoc] at hgen' hprop'
    refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ T T (fA B) (LPow A L k (topS Rg)) (LPow B M k (topS Rg)) mA mB bA bB _ (𝟙 T) c _ _
      (GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hB hM hk hva hbB) (LB.isLB_linComb hM _ _) (LB.isLB_linComb hL _ _) hgen' hprop'
      (proport_zero t c hvA hvB hnorm) ?_
    rw [Category.assoc, hΨ, ← Category.assoc, hηA, Category.id_comp, Category.assoc, Category.assoc, θ_comp_structure,
      heB]
    exact (Category.comp_id _).symm
  have hz : η[A'] ≫ Φ = η[B'] := by
    apply Over.OverMorphism.ext
    apply hB'.1.hom_ext
    · show e' ≫ Φl ≫ φB' = _
      rw [hΦ1, ← Category.assoc, hzero, hEB, Category.assoc, Category.assoc, θ_snd, Category.comp_id]
    · exact (Over.w _).trans (Over.w _).symm
  exact ⟨Φ, GlobalTheory.rigidity_holds T A' B' hA'ab hB'ab Φ hz, hΨΦ⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomOfProportionalGeneratingCombinationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpHom_of_proportional_generating_combinations : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  first | (exact @GlobalTheory.HomFixUniv.hom_of_proport) | (exact GlobalTheory.HomFixUniv.hom_of_proport) | (intros; apply GlobalTheory.HomFixUniv.hom_of_proport <;> assumption)
end
end
