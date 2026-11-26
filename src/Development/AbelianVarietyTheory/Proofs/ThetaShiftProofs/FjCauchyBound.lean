module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FjFlow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.FjCauchy

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open NumberField Complex Filter Topology in
theorem _root_.GlobalTheory.FjCauchy.isIsoV_embV {ξ : Fin r → E} (hξ : X.IsIso ξ) :
    X.IsIsoV (X.embV ξ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIsoV
  intro τ
  refine ⟨?_, _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero (τ : E →+* ℂ) hξ.2.2⟩
  show _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ξ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ ξ) = 0
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ.2.1, map_zero]

open NumberField Complex Filter Topology in
theorem _root_.GlobalTheory.FjCauchy.tt_pos {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) :
    0 < X.tt ξ x τ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
  exact one_div_pos.2 (mul_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ) (X.maj_pos hx τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero (τ : E →+* ℂ) hξ.2.2)))

open NumberField Complex Filter Topology in
private theorem one_add_two_mul_pos_of_le {c y h hp : ℝ} (hc : 0 < c) (h0 : 0 ≤ h) (hle : h ≤ hp)
    (hpos : 0 < 1 + 2 * c * y * hp) : 0 < 1 + 2 * c * y * h := by
  rcases le_or_gt 0 y with hy | hy
  · have : 0 ≤ 2 * c * y * h := by positivity
    linarith
  · have h1 : 0 ≤ hp - h := sub_nonneg.2 hle
    have h2 : 0 < -y := by linarith
    have : 0 ≤ 2 * c * (-y) * (hp - h) := by positivity
    nlinarith

open NumberField Complex Filter Topology in
private theorem one_add_two_mul_pos_of_inv_add_pos {c y hp : ℝ} (hc : 0 < c) (hp0 : 0 < hp)
    (hs : 0 < 1 / (c * (2 * hp)) + y) : 0 < 1 + 2 * c * y * hp := by
  have hk : 0 < c * (2 * hp) := by positivity
  have e : (1 / (c * (2 * hp)) + y) * (c * (2 * hp)) = 1 + 2 * c * y * hp := by
    rw [add_mul, one_div, inv_mul_cancel₀ hk.ne']
    ring
  rw [← e]
  exact mul_pos hs hk

open NumberField Complex Filter Topology in
theorem _root_.GlobalTheory.FjCauchy.flow_mem_dom {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 < X.tt ξ x τ + (s τ).im) :
    X.flow ξ s x ∈ X.dom := by
  have hiso := _root_.GlobalTheory.FjCauchy.isIsoV_embV X hξ
  rw [show X.flow ξ s x = X.flowV (X.embV ξ) s x from rfl]
  have hx' := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at hx' ⊢
  intro τ
  obtain ⟨hdet, hmin⟩ := hx' τ
  constructor
  · show (X.flowMatV (X.embV ξ τ) τ (s τ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0
    rw [Matrix.det_mul, _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.det_flowMat X _ τ _ (hiso τ).1, one_mul]
    exact hdet
  · intro i
    have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (X.embV ξ) τ (hiso τ).1
    have hmaj := X.maj_pos hx τ (hiso τ).2
    have hsτ := hs τ
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt at hsτ
    change 0 < 1 / (X.c τ * X.maj x τ (X.embV ξ τ)) + (s τ).im at hsτ
    have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_bounds (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) hdet (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ)
      (X.embV ξ τ) (hiso τ).1 i (Nat.lt_succ_iff.mp i.isLt)
    have hmi := hmin i
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq] at hmi ⊢
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx _ τ (hiso τ).1 s, Complex.re_mul_ofReal, ← mul_assoc]
    rw [hm0] at hmaj hsτ
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
    have hp0 : 0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 := by linarith
    exact mul_pos hmi (one_add_two_mul_pos_of_le hc hb.1 hb.2 (one_add_two_mul_pos_of_inv_add_pos hc hp0 hsτ))

open NumberField Complex Filter Topology in
theorem _root_.GlobalTheory.FjCauchy.tt_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) :
    X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + (s τ).im := by
  have hiso := _root_.GlobalTheory.FjCauchy.isIsoV_embV X hξ
  rw [show X.flow ξ s x = X.flowV (X.embV ξ) s x from rfl] at hs ⊢
  have hf : 1 + 2 * X.c τ * (s τ).im *
      _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 ≠ 0 := by
    intro h0
    have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hs τ X.p0 X.p0_le
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx _ τ (hiso τ).1 s, h0] at h1
    simp at h1
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_flow X hx (X.embV ξ) τ (hiso τ).1 s hf
  have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (X.embV ξ) τ (hiso τ).1
  have hmaj := X.maj_pos hx τ (hiso τ).2
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
  change 1 / (X.c τ * X.maj (X.flowV (X.embV ξ) s x) τ (X.embV ξ τ)) =
    1 / (X.c τ * X.maj x τ (X.embV ξ τ)) + (s τ).im
  rw [hm, hm0]
  rw [hm0] at hmaj
  generalize _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (X.embV ξ τ) X.p0 = H at hf hmaj ⊢
  have hH : H ≠ 0 := by linarith
  have hc' : X.c τ ≠ 0 := hc.ne'
  field_simp

open NumberField Complex Filter Topology in
private theorem differentiable_flow_affine_line (ξ : Fin r → E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (a b : X.Ψ → ℂ) :
    Differentiable ℂ (fun t : ℂ ↦ X.flow ξ (fun τ ↦ a τ + t * b τ) x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.flow _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.flowMat _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
  refine differentiable_pi.2 fun τ ↦ ?_
  refine differentiable_pi.2 fun i ↦ ?_
  refine differentiable_pi.2 fun j ↦ ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

open NumberField Complex Filter Topology in
theorem _root_.GlobalTheory.FjCauchy.fj_flow {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hs : X.flow ξ s x ∈ X.dom) :
    X.fj la ξ ν P (X.flow ξ s x) =
      cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ) * X.fj la ξ ν P x := by
  have hP' : X.IsSec la P ∧ ∃ C, ∀ y ∈ X.dom, X.pnorm la P y ≤ C := hP
  obtain ⟨hsec, hbdd⟩ := hP'
  have hGξ := hξ.2.1
  obtain ⟨W, hWdef⟩ : ∃ W : Set ℂ,
      W = {t | X.flow ξ (fun τ ↦ ((s τ).re : ℂ) + t * (s τ).im) x ∈ X.dom} := ⟨_, rfl⟩
  have hW : W = (fun t : ℂ ↦ fun τ : X.Ψ ↦ t.im * (s τ).im) ⁻¹' _root_.ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary X ξ x := by
    ext t
    rw [hWdef, Set.mem_setOf_eq, Set.mem_preimage, _root_.ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.flow_mem_dom_iff X hGξ x hx]
    have him : (fun τ ↦ (((s τ).re : ℂ) + t * (s τ).im).im) = fun τ ↦ t.im * (s τ).im := by
      funext τ
      simp
    rw [him]
  have hlin : IsLinearMap ℝ (fun t : ℂ ↦ fun τ : X.Ψ ↦ t.im * (s τ).im) :=
    ⟨fun u v ↦ by funext τ; simp [add_mul], fun c u ↦ by funext τ; simp [mul_assoc]⟩
  have hcont : Continuous (fun t : ℂ ↦ fun τ : X.Ψ ↦ t.im * (s τ).im) := by fun_prop
  obtain ⟨hopen, hconv⟩ := _root_.ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns.admissibleImaginary_open_convex X (ξ := ξ) x hx
  have hWo : IsOpen W := hW ▸ hopen.preimage hcont
  have hWc : IsPreconnected W := hW ▸ (hconv.is_linear_preimage hlin).isPreconnected
  have hreal : ∀ a : ℝ, (fun τ ↦ ((s τ).re : ℂ) + (a : ℂ) * (s τ).im) =
      fun τ ↦ (((s τ).re + a * (s τ).im : ℝ) : ℂ) := by
    intro a
    funext τ
    push_cast
    ring
  have h0W : (0 : ℂ) ∈ W := by
    rw [hWdef, Set.mem_setOf_eq, show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, hreal]
    exact (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.flow_real X hξ hx _ la).1
  have hline : ∀ τ, ((s τ).re : ℂ) + I * (s τ).im = s τ := by
    intro τ
    rw [mul_comm]
    exact Complex.re_add_im (s τ)
  have hIW : I ∈ W := by
    rw [hWdef, Set.mem_setOf_eq]
    simp only [hline]
    exact hs
  obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = fun t ↦
      X.fj la ξ ν P (X.flow ξ (fun τ ↦ ((s τ).re : ℂ) + t * (s τ).im) x) -
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * (((s τ).re : ℂ) + t * (s τ).im)) *
          X.fj la ξ ν P x := ⟨_, rfl⟩
  have hgd : DifferentiableOn ℂ g W := by
    rw [hg]
    apply DifferentiableOn.sub
    · refine (_root_.ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP hξ ν).comp
        (differentiable_flow_affine_line X ξ x _ _).differentiableOn ?_
      intro t ht
      rw [hWdef] at ht
      exact ht
    · apply DifferentiableOn.mul_const
      apply Differentiable.differentiableOn
      fun_prop
  have hg0 : ∀ a : ℝ, g a = 0 := by
    intro a
    have h := _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hsec hbdd x hx
      (fun τ ↦ (s τ).re + a * (s τ).im)
    push_cast at h
    rw [hg]
    simp only
    rw [h, sub_self]
  have hto : Tendsto (fun a : ℝ ↦ (a : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simpa using ha
  have hfreq : ∃ᶠ t in 𝓝[≠] (0 : ℂ), g t = 0 := hto.frequently (Frequently.of_forall hg0)
  have hgI := (hgd.analyticOnNhd hWo).eqOn_zero_of_preconnected_of_frequently_eq_zero
    hWc h0W hfreq hIW
  rw [hg] at hgI
  simp only [hline, Pi.zero_apply, sub_eq_zero] at hgI
  exact hgI

end GlobalTheory.FjCauchy

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqOfDominantGeometricPointsOfUnramified
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace GlobalTheory

theorem exists_point_over_dominant_geometric_point {U S : Scheme.{u}} (g : U ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] [Nonempty U] {F : Type u} [Field F]
    [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t] :
    ∃ j : Spec (.of F) ⟶ U, j ≫ g = t := by
  obtain ⟨z, u, hu⟩ := t.denseRange.exists_mem_open g.isOpenMap.isOpen_range
    (Set.range_nonempty _)
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := t) u z hu
  have : JacobsonSpace ↥(pullback g t) := LocallyOfFiniteType.jacobsonSpace (pullback.snd g t)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback g t)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨pointOfClosedPoint (pullback.snd g t) c hc ≫ pullback.fst g t, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem eq_of_dominant_geometric_points_of_unramified {X S T : Scheme.{u}} (f : X ⟶ S)
    [FormallyUnramified f] [LocallyOfFiniteType f] [IsSeparated f] (g : T ⟶ S)
    [UniversallyOpen g] [LocallyOfFiniteType g] {a b : T ⟶ X} (ha : a ≫ f = g) (hb : b ≫ f = g)
    {F : Type u} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (h : ∀ j : Spec (.of F) ⟶ T, j ≫ g = t → j ≫ a = j ≫ b) : a = b := by
  have hab : a ≫ f = b ≫ f := ha.trans hb.symm
  have := isClosedImmersion_equalizer_ι_of_isSeparated f hab
  refine eq_of_range_equalizer_ι_eq_univ f hab ?_
  by_contra hne
  let U : T.Opens := ⟨(Set.range (equalizer.ι a b))ᶜ,
    (equalizer.ι a b).isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨y, hy⟩ := Set.nonempty_compl.mpr hne
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  obtain ⟨j, hj⟩ := exists_point_over_dominant_geometric_point (U.ι ≫ g) t
  have h1 := range_subset_range_equalizer_ι (j ≫ U.ι) (h _ (by simpa using hj))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have h2 : (j ≫ U.ι) p ∈ U := by
    rw [Scheme.Hom.comp_apply]
    exact (j p).2
  exact h2 (h1 ⟨_, rfl⟩)

theorem fix_torsion_of_fix_geometric_of_etale {S : Scheme.{0}} (A : Over S) [GrpObj A] (M : ℕ)
    [Etale (mulA A M).left] [IsSeparated (mulA A M).left]
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : A ⟶ A) [IsMonHom s]
    (hs : ∀ x : Over.mk t ⟶ A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ A) (hx : x ^ M = 1) : x ≫ s = x := by
  have hmul : ∀ {Z : Over S} (y : Z ⟶ A), y ≫ mulA A M = y ^ M := fun y => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have hone : ∀ {Z : Over S}, (1 : Z ⟶ A).left = Z.hom ≫ η[A].left := fun {Z} => by
    rw [Hom.one_def, Over.comp_left]; rfl
  let K : Over S := Over.mk (pullback.snd (mulA A M).left η[A].left)
  have hη : η[A].left ≫ A.hom = 𝟙 S := Over.w η[A]
  let i : K ⟶ A := Over.homMk (pullback.fst (mulA A M).left η[A].left) (by
    change pullback.fst (mulA A M).left η[A].left ≫ A.hom = pullback.snd (mulA A M).left η[A].left
    rw [← Over.w (mulA A M), pullback.condition_assoc]
    erw [hη]
    exact Category.comp_id _)
  have hi : i ^ M = 1 := by
    rw [← hmul]
    apply Over.OverMorphism.ext
    rw [hone]
    exact pullback.condition
  have hlift : ∀ {Z : Over S} (y : Z ⟶ A), y ^ M = 1 → ∃ l : Z ⟶ K, l ≫ i = y := by
    intro Z y hy
    have e : y.left ≫ (mulA A M).left = Z.hom ≫ η[A].left := by
      rw [← Over.comp_left, hmul, hy, hone]
    exact ⟨Over.homMk (pullback.lift _ _ e) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  have hmono : ∀ {Z : Over S} (l l' : Z ⟶ K), l ≫ i = l' ≫ i → l = l' := by
    intro Z l l' e
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congr(($e).left)
    · exact (Over.w l).trans (Over.w l').symm
  obtain ⟨σ, hσ⟩ := hlift (i ≫ s) (by rw [← MonObj.pow_comp, hi, MonObj.one_comp])
  have hEt : Etale K.hom := inferInstanceAs (Etale (pullback.snd (mulA A M).left η[A].left))
  have hSep : IsSeparated K.hom :=
    inferInstanceAs (IsSeparated (pullback.snd (mulA A M).left η[A].left))
  have key : σ = 𝟙 K := by
    apply Over.OverMorphism.ext
    refine eq_of_dominant_geometric_points_of_unramified K.hom K.hom (Over.w σ) (Over.w (𝟙 K)) t ?_
    intro j hj
    let j' : Over.mk t ⟶ K := Over.homMk j hj
    have : j' ≫ σ = j' ≫ 𝟙 K := by
      apply hmono
      rw [Category.assoc, hσ, Category.comp_id, ← Category.assoc]
      exact hs _ (by rw [← MonObj.comp_pow, hi, MonObj.comp_one])
    exact congr(($this).left)
  obtain ⟨l, rfl⟩ := hlift x hx
  rw [Category.assoc, ← hσ, key, Category.id_comp]

theorem fix_torsion_of_fix_geometric_of_isDominant (hmul : MulNSt) {S : Scheme.{0}}
    [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (hM : 1 ≤ M) (hMu : IsUnit (M : Γ(S, ⊤)))
    {F : Type} [Field F] [IsAlgClosed F] (t : Spec (.of F) ⟶ S) [IsDominant t]
    (s : P.A ⟶ P.A) (hsm : IsMonHom s)
    (hs : ∀ x : Over.mk t ⟶ P.A, x ^ M = 1 → x ≫ s = x)
    (T : Over S) (x : T ⟶ P.A) (hx : x ^ M = 1) : x ≫ s = x := by
  obtain ⟨hfin, -, -, het, -⟩ := hmul S P M hM
  have := het hMu
  exact fix_torsion_of_fix_geometric_of_etale P.A M t s hs T x hx

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqSumRingHom
namespace GlobalTheory.TraceRealPartConjugateSum

open NumberField

theorem trace_eq_sum_ringHom {E : Type} [Field E] [NumberField E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ τ : E →+* ℂ, τ x := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := x)
  rw [eq_ratCast] at h
  rw [h]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ => rfl

theorem sum_re_add_conj {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : E) :
    ∑ τ : ↥(ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X),
      Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) =
      (↑((Algebra.trace ℚ E : E → ℚ) x) : ℝ) := by
  classical
  set Ψ := ReciprocityTheory.ChartRestriction.G.FD.Data.Ψ X with hΨ
  have hconj : ∀ τ : E →+* ℂ,
      τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = τ x + (ComplexEmbedding.conjugate τ) x := by
    intro τ
    rw [map_add (f := _), ComplexEmbedding.conjugate_coe_eq, ReciprocityTheory.ChartRestriction.G.FD.cc,
      IsCMField.complexEmbedding_complexConj]
  have himg : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext τ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      refine ⟨ComplexEmbedding.conjugate τ, ?_, ComplexEmbedding.involutive_conjugate E τ⟩
      rw [X.cmType, ComplexEmbedding.involutive_conjugate E τ]
      exact h
    · rintro ⟨σ, hσ, rfl⟩
      exact (X.cmType σ).1 hσ
  have hsum : ∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x) = ∑ τ : E →+* ℂ, τ x := by
    rw [← Finset.sum_add_sum_compl Ψ (fun τ : E →+* ℂ => τ x), himg,
      Finset.sum_image (fun a _ b _ h => (ComplexEmbedding.involutive_conjugate E).injective h),
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun τ _ => hconj τ
  calc ∑ τ : ↥Ψ, Complex.re (((↑τ : E →+* ℂ) : E → ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))
      = Complex.re (∑ τ : ↥Ψ, (↑τ : E →+* ℂ) (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := (Complex.re_sum _ _).symm
    _ = Complex.re (∑ τ ∈ Ψ, τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x)) := by
      rw [Finset.sum_coe_sort Ψ (fun τ : E →+* ℂ => τ (x + ReciprocityTheory.ChartRestriction.G.FD.cc x))]
    _ = _ := by
      rw [hsum, ← trace_eq_sum_ringHom x]
      simp

end GlobalTheory.TraceRealPartConjugateSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoords
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.HermExpo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem sum_re_eq_trace (X : Data E r) (x : E) :
    ∑ τ : X.Ψ, (τ.1 (x + cc x)).re = ((Algebra.trace ℚ E x : ℚ) : ℝ) := by
  first
  | exact @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj
  | (apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceRealPartConjugateSum.sum_re_add_conj ..)

theorem kappa_ne (X : Data E r) : X.κ0 ≠ 0 := by
  have := X.ξ0_ne
  rcases X.κ0_xi with h | h <;> rw [h] <;> simpa using this

theorem exists_trace_repr (f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ) :
    ∃ c : Matrix (Fin ρ) (Fin ρ) E, ∀ β,
      f β = Algebra.trace ℚ E (∑ a, ∑ b, c a b * β a b) := by
  have h : ∀ g : E →ₗ[ℚ] ℚ, ∃ c : E, ∀ y, g y = Algebra.trace ℚ E (c * y) := by
    intro g
    refine ⟨((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm g, fun y => ?_⟩
    rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  choose c hc using fun a b : Fin ρ => h (f ∘ₗ Matrix.singleLinearMap ℚ a b)
  refine ⟨Matrix.of c, fun β => ?_⟩
  conv_lhs => rw [Matrix.matrix_eq_sum_single β]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Matrix.of_apply, ← hc]
  rfl

theorem exists_herm_phase (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ)
    (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (m : Fin (nZ X ρ) → ℤ) :
    ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  have hli : LinearIndependent ℚ (zBas X cu) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.1
  obtain ⟨f, hf⟩ : ∃ f : Matrix (Fin ρ) (Fin ρ) E →ₗ[ℚ] ℚ, ∀ k, f (zBas X cu k) = m k := by
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective
      (Finsupp.linearCombination ℚ (zBas X cu)) (LinearMap.ker_eq_bot.2 hli)
    refine ⟨Finsupp.linearCombination ℚ (fun k => (m k : ℚ)) ∘ₗ g, fun k => ?_⟩
    have h1 := LinearMap.congr_fun hg (Finsupp.single k 1)
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] at h1
    simp [h1]
  obtain ⟨c, hc⟩ := exists_trace_repr f
  have hκ : X.κ0 / 2 ≠ 0 := div_ne_zero (kappa_ne X) two_ne_zero
  have hκc : cc (X.κ0 / 2) = -(X.κ0 / 2) := by
    have := maxCuspsA_kappa_cc X
    unfold cc at this ⊢
    rw [map_div₀, this, map_ofNat, neg_div]
  have hcc : ∀ y : E, cc (cc y) = y := fun y => IsCMField.complexConj_apply_apply E y
  have hmul : ∀ y z : E, cc (y * z) = cc y * cc z := fun y z => map_mul _ y z
  have hadd : ∀ y z : E, cc (y + z) = cc y + cc z := fun y z => map_add _ y z
  have hsub : ∀ y z : E, cc (y - z) = cc y - cc z := fun y z => map_sub _ y z
  refine ⟨Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a)), fun a b => ?_, fun k => ?_⟩
  · simp only [Matrix.of_apply, hmul, hsub, hκc, hcc]
    ring
  · have hs := zBas_skew X cu ⟨_, hb⟩ k
    have hx : Matrix.trace ((Matrix.of fun a b => (X.κ0 / 2) * (c a b - cc (c b a))).transpose *
        zBas X cu k) / (X.κ0 / 2) =
        (∑ a, ∑ b, c a b * zBas X cu k a b) + cc (∑ a, ∑ b, c a b * zBas X cu k a b) := by
      have h1 : cc (∑ a, ∑ b, c a b * zBas X cu k a b) =
          ∑ a, ∑ b, -(cc (c b a) * zBas X cu k a b) := by
        rw [Finset.sum_comm]
        unfold cc
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show IsCMField.complexConj E (zBas X cu k b a) = cc (zBas X cu k b a) from rfl, hs,
          mul_neg]
      rw [h1, div_eq_iff hκ, ← Finset.sum_add_distrib]
      simp only [← Finset.sum_add_distrib, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    unfold phZ prE
    rw [hx, sum_re_eq_trace, ← hc, hf]
    simp

end GlobalTheory.HermExpo

theorem GlobalTheory.exists_isHermE_phZ_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k :=
  GlobalTheory.HermExpo.exists_herm_phase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HermitianMatrixRealizesCuspCoordsStatement
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_matrix_realizes_cusp_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  first | exact @GlobalTheory.exists_isHermE_phZ_eq | exact GlobalTheory.exists_isHermE_phZ_eq | (intros; apply GlobalTheory.exists_isHermE_phZ_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusAction
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusAction
set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.CuspFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem herm_comb_eq_zero (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  have h : herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) =
      ∑ a, ∑ b, η a * cc (η b) * herm X.Gm (cu.e a) (cu.e b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, maxCuspsA_vec_apply, cc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    calc ∑ k, ∑ l, ∑ b, ∑ a, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l))
        = ∑ k, ∑ b, ∑ a, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ b, ∑ a, ∑ k, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [h]
  simp [cu.iso]

theorem exists_int_coords (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) (a : E) (ha : cc a = a)
    (hai : IsIntegral ℤ a) :
    ∃ c : Fin (nZ X ρ) → ℤ, ∑ k, c k • zBas X cu k = ((X.m : E) * a * X.κ0) • mcMη η := by
  obtain ⟨γ, hγ, hγe⟩ := X.transv _ hη (herm_comb_eq_zero X cu η) a ha hai
  have hmem : ((X.m : E) * a * X.κ0) • mcMη η ∈ zGam X cu := by
    refine ⟨fun i j => ?_, γ, hγ, by rw [hγe, maxCuspsA_transv]⟩
    have hk := maxCuspsA_kappa_cc X
    simp only [cc] at hk ha
    simp only [mcMη, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, cc, map_mul, map_natCast,
      hk, ha, IsCMField.complexConj_apply_apply]
    ring
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((hb.2 _).mp hmem)

theorem exists_linear (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) :
    ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ),
      (∀ (s : X.Ψ → ℝ) (τ : X.Ψ) (a b : Fin ρ), ∑ k, (L s k : ℂ) * τ.1 (zBas X cu k a b) =
        τ.1 X.κ0 * (s τ : ℂ) * (τ.1 (η a) * conj (τ.1 (η b)))) ∧
      ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  obtain ⟨ω, hω⟩ := FlowMeanContinuity.exists_basis X 0
  have hωp : ∀ j, ω j ∈ X.periods 0 := fun j => by
    have : ω j ∈ RealEmbeddingCharacters.perL X 0 := hω ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose a ha hai hae using fun j => (RealEmbeddingCharacters.mem_periods_iff X 0 _).mp (hωp j)
  choose c hc using fun j => exists_int_coords X cu hb η hη (a j) (ha j) (hai j)
  set n0 : ℕ := X.chiOrd 0 with hn0
  have hn0pos : (n0 : ℝ) ≠ 0 := by
    have := RealEmbeddingCharacters.chiOrd_pos X 0
    positivity
  let L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ) := ω.constr ℝ fun j k => (n0 : ℝ) * (c j k : ℝ)
  have hL : ∀ j k, L (ω j) k = (n0 : ℝ) * (c j k : ℝ) := fun j k => by
    simp only [L, Module.Basis.constr_basis]
  refine ⟨L, fun s τ i i' => ?_, fun la p hp k => ?_⟩
  · have hj : ∀ j, ∑ k, (L (ω j) k : ℂ) * τ.1 (zBas X cu k i i') =
        τ.1 X.κ0 * (ω j τ : ℂ) * (τ.1 (η i) * conj (τ.1 (η i'))) := by
      intro j
      have h1 := congrArg (fun M : Matrix (Fin ρ) (Fin ρ) E => τ.1 (M i i')) (hc j)
      simp only [Matrix.sum_apply, Matrix.smul_apply] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, mcMη, Matrix.of_apply,
        smul_eq_mul, zsmul_eq_mul, map_mul, map_intCast, map_natCast,
        Formalism.L2.Pj.FJ.emb_cc'] at h1
      have h2 : (ω j τ : ℂ) = (X.m : ℂ) * (n0 : ℂ) * τ.1 (a j) := by
        rw [hae j, RealEmbeddingCharacters.emb_real (ha j)]
        simp only [RealEmbeddingCharacters.per]
        push_cast
        rfl
      simp only [hL]
      push_cast
      simp only [mul_assoc (n0 : ℂ)]
      rw [← Finset.mul_sum, h1, h2]
      ring
    have hs : s = ∑ j, ω.repr s j • ω j := (ω.sum_repr s).symm
    generalize ω.repr s = t at hs
    subst hs
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc ((t j : ℝ) : ℂ)]
    rw [← Finset.mul_sum, hj]
    ring
  · obtain ⟨b, hb1, hb2, rfl⟩ := (RealEmbeddingCharacters.mem_periods_iff X la p).mp hp
    have h0 : RealEmbeddingCharacters.per X 0 b ∈ Submodule.span ℤ (Set.range ω) := by
      rw [hω]
      exact (RealEmbeddingCharacters.mem_periods_iff X 0 _).mpr ⟨b, hb1, hb2, rfl⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h0
    have h1 : RealEmbeddingCharacters.per X la b =
        ((X.chiOrd la : ℝ) / (n0 : ℝ)) • RealEmbeddingCharacters.per X 0 b := by
      funext τ
      simp only [RealEmbeddingCharacters.per, Pi.smul_apply, smul_eq_mul, ← hn0]
      push_cast
      field_simp
    refine ⟨X.chiOrd la * ∑ j, d j * c j k, ?_⟩
    rw [h1, ← hd]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, map_zsmul, Pi.smul_apply, Finset.sum_apply, hL]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

theorem flow_eq_zAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  intro E _ _ _ r ρ X cu hb η hη
  obtain ⟨L, hL, hZ⟩ := exists_linear X cu hb η hη
  refine ⟨L, fun s x => ?_, fun χ _ s => ?_, hZ⟩
  · funext τ
    show X.flowMat (∑ a, η a • cu.e a) τ (s τ : ℂ) * mat x τ =
      zMatC X cu.e τ.1 (∑ k, (L s k : ℂ) • (zBas X cu k).map τ.1) * mat x τ
    rw [maxCuspsA_flowMat, ← TransvectionPeriodicity.emb_kappa]
    congr 2
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mcMηc,
      Matrix.of_apply]
    exact (hL s τ a b).symm
  · simp only [phZ, prE, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hκ : τ.1 X.κ0 ≠ 0 := fun h => by
      have := X.κ0_sign τ
      rw [h] at this
      simp at this
    have key : ∑ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
        2 * (τ.1 (hq χ η) * (s τ : ℂ)) := by
      have e1 : ∀ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
          ∑ b, ∑ a, 2 / τ.1 X.κ0 * τ.1 (χ a b) * ((L s k : ℂ) * τ.1 (zBas X cu k a b)) := by
        intro k
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
          map_div₀, map_sum, map_mul, map_ofNat, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        field_simp
      simp only [e1]
      rw [Finset.sum_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hq, map_sum, map_mul, Formalism.L2.Pj.FJ.emb_cc', Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun a b => 2 * (τ.1 (η a) * τ.1 (χ a b) * conj (τ.1 (η b)) * (s τ : ℂ)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum, hL]
      field_simp
    have h := congrArg Complex.re key
    simpa [Complex.re_sum] using h

end GlobalTheory.CuspFlow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CuspFlowEqTorusActionStatement
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFlow_eq_torusAction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  first | exact @GlobalTheory.CuspFlow.flow_eq_zAct | exact GlobalTheory.CuspFlow.flow_eq_zAct | (intros; apply GlobalTheory.CuspFlow.flow_eq_zAct <;> assumption)
end
end
