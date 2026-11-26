module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMetricOfIsOrtho
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnifTangent

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem eq_of_values {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {x x' : Sp ℂ ⟶ X} (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : ∀ f, valAt' x U f = valAt' x' U f) : x = x' := by
  refine (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x h).symm.trans
    (Eq.trans ?_ (AffinePointValues.specMap_appLE_fromSpec hU (R := CommRingCat.of ℂ) x' h'))
  congr 2
  ext1
  refine RingHom.ext fun f => ?_
  have := e f
  rw [valAt', valAt', dite_eq_left h, dite_eq_left h'] at this
  exact this

theorem fderiv_eq_zero_of_origin {w : Fin g → ℂ}
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0)
    (z : Fin g → ℂ) (U : A.left.Opens) (f : Γ(A.left, U)) (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ U) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U f) z w = 0 := by
  let τ : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A
  have hτ : ∀ v, u.ex v ≫ τ = u.ex (z + v) := fun v => by
    rw [u.ex_add, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (τ.left ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Over.comp_left, hτ, add_zero]
    exact h
  have e : (fun v => valAt' (u.ex v).left (τ.left ⁻¹ᵁ U) ((τ.left.app U).hom f)) =
      fun v => valAt' (u.ex (z + v)).left U f := funext fun v => by
    rw [valAt'_comp, ← Over.comp_left, hτ]
  have := hw _ ((τ.left.app U).hom f) h0
  rw [e, fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), add_zero] at this
  exact this

theorem eq_zero_of_fderiv_eq_zero (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0) : w = 0 := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := A.left)
    (x := (u.ex 0).left (default : PrimeSpectrum ℂ)) (U := ⊤) trivial
  have h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := (top_le_preimage_iff_mem _ _).2 hx
  haveI := u.discrete
  obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (isOpen_discrete ({0} : Set u.Λ))
  have hO0 : (0 : Fin g → ℂ) ∈ O := by
    have : (0 : u.Λ) ∈ Subtype.val ⁻¹' O := hOe ▸ rfl
    exact this
  have hc : Continuous fun t : ℂ => t • w := by fun_prop
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 ((((u.hol U 0).1).inter hO).preimage hc) 0
    (by simpa only [Set.mem_preimage, zero_smul] using ⟨h0, hO0⟩)
  have ht : ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hd : ∀ f, ∀ t ∈ Metric.ball (0 : ℂ) ε, HasDerivAt (fun t : ℂ => valAt' (u.ex (t • w)).left U f) 0 t := by
    intro f t ht
    have h1 := ((u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds (hB ht).1)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t ((hasDerivAt_id t).smul_const w)
    rw [one_smul, fderiv_eq_zero_of_origin u hw _ U f (hB ht).1] at h2
    exact h2
  have he : u.ex (((ε / 2 : ℝ) : ℂ) • w) = u.ex ((0 : ℂ) • w) := by
    refine Over.OverMorphism.ext (eq_of_values hU (hB ht).1 (hB (Metric.mem_ball_self hε)).1 fun f => ?_)
    exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) ε).isPreconnected
      (fun t ht => (hd f t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd f t ht).deriv) ht
      (Metric.mem_ball_self hε)
  rw [zero_smul, (u.ker 0).2 (zero_mem _), u.ker] at he
  have h3 : (⟨_, he⟩ : u.Λ) ∈ ({0} : Set u.Λ) := hOe ▸ (hB ht).2
  exact (smul_eq_zero.1 (congrArg Subtype.val h3)).resolve_left (Complex.ofReal_ne_zero.2 (by positivity))

theorem tangent_bijection (hs : SmoothOfRelativeDimension g A.hom) :
    (∀ v : epsR ℂ ⟶ A, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v : epsR ℂ ⟶ A, IsTangent v ∧ u.IsDiff w v :=
  TangentOrigin.tangent_bijection_of_values valAt'_rules A L g u
    (exists_coord_adapted (HolChart.exists_holomorphic_chart valAt'_rules existsUnique_point_of_ringHom
      exists_holomorphic_section_of_etale) A L g u hs (eq_zero_of_fderiv_eq_zero u))

end GlobalTheory.UnifTangent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPointResidueNonzero
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.PullbackFinitePoint


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔ (f.residueFieldMap x).hom.Finite := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  unfold Scheme.Hom.residueDegree RingHom.Finite
  constructor
  · intro h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  · intro h
    exact Module.finrank_pos.ne'

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private theorem residueFieldMap_surjective_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : Function.Surjective (f.residueFieldMap x) := by
  intro z
  obtain ⟨s, rfl⟩ := X.residue_surjective x z
  obtain ⟨t, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨Y.residue (f x) t, ?_⟩
  rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_of_surjectiveOnStalks {X Y : Scheme.{0}} (f : X ⟶ Y)
    [SurjectiveOnStalks f] (x : X) : f.residueDegree x ≠ 0 :=
  (_root_.GlobalTheory.PullbackFinitePoint.residueDegree_ne_zero_iff_finite f x).2
    (RingHom.Finite.of_surjective _ (residueFieldMap_surjective_of_surjectiveOnStalks f x))

end GlobalTheory.PullbackFinitePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem transDet_trans_chart (c c' c'' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) (hy'' : y ∈ c''.e.source) :
    ChartGlue.transDet c.e c''.e y =
      ChartGlue.transDet c.e c'.e y * ChartGlue.transDet c'.e c''.e y := by
  have ho := ChartGlue.isOpen_over c.e (c'.e.open_source.inter c''.e.open_source)
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' (c'.e.source ∩ c''.e.source) :=
    ChartGlue.mem_over c.e hy ⟨hy', hy''⟩
  have e : c''.e ∘ c.e.symm =ᶠ[𝓝 (c.e y)] (c''.e ∘ c'.e.symm) ∘ (c'.e ∘ c.e.symm) :=
    eventually_of_mem (ho.mem_nhds hm) fun w hw => by
      simp only [Function.comp_apply, c'.e.left_inv hw.2.1]
  have hf : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    (c.holo_trans c').differentiableAt
      ((ChartGlue.isOpen_over c.e c'.e.open_source).mem_nhds (ChartGlue.mem_over c.e hy hy'))
  have hfy : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := by simp [c.e.left_inv hy]
  have hg : DifferentiableAt ℂ (c''.e ∘ c'.e.symm) ((c'.e ∘ c.e.symm) (c.e y)) := by
    rw [hfy]
    exact (c'.holo_trans c'').differentiableAt
      ((ChartGlue.isOpen_over c'.e c''.e.open_source).mem_nhds (ChartGlue.mem_over c'.e hy' hy''))
  rw [ChartGlue.transDet, e.fderiv_eq, fderiv_comp _ hg hf, hfy, ChartGlue.transDet,
    ChartGlue.transDet]
  simp only [ContinuousLinearMap.det]
  exact (LinearMap.det_comp _ _).trans (mul_comm _ _)

theorem transDet_chart_ne_zero (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ChartGlue.transDet c.e c'.e y ≠ 0 := by
  intro h
  have := transDet_trans_chart c c' c hy hy' hy
  rw [c.transDet_self hy, h, zero_mul] at this
  exact one_ne_zero this

theorem continuousAt_transDet_chart (c c' : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) : ContinuousAt (ChartGlue.transDet c.e c'.e) y := by
  have hW : y ∈ ptsIn p σ (c.U ⊓ c'.U) :=
    mem_ptsIn_inf.2 ⟨c.source_subset hy, c'.source_subset hy'⟩
  have h1 : ContinuousAt (ev p σ _ (c.isFrame.ratio c'.isFrame).val) y :=
    (continuousOn_ev _).continuousAt ((isOpen_ptsIn _).mem_nhds hW)
  refine h1.congr ?_
  filter_upwards [(c.e.open_source.inter c'.e.open_source).mem_nhds ⟨hy, hy'⟩] with z hz
  exact c.ev_ratio c' hz.1 hz.2

end GlobalTheory.CurveDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidTranslate

open GlobalTheory.CoordToExt GlobalTheory.PolTranslate

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem transl_transl_inv (t : 𝟙_ (Over S) ⟶ A) : transl t ≫ transl t⁻¹ = 𝟙 A := by
  rw [GlobalTheory.PolTranslate.comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, _root_.mul_inv_cancel,
    MonObj.comp_one, _root_.mul_one]

theorem transl_inv_transl (t : 𝟙_ (Over S) ⟶ A) : transl t⁻¹ ≫ transl t = 𝟙 A := by
  rw [GlobalTheory.PolTranslate.comp_transl, transl, _root_.mul_assoc, ← MonObj.comp_mul, _root_.inv_mul_cancel,
    MonObj.comp_one, _root_.mul_one]

instance isIso_transl_left (t : 𝟙_ (Over S) ⟶ A) : IsIso (transl t).left :=
  ⟨⟨(transl t⁻¹).left, congrArg (fun q => q.left) (transl_transl_inv t),
    congrArg (fun q => q.left) (transl_inv_transl t)⟩⟩

theorem relAmple_rigTransl_of_section [IsAffine S] [IsProper A.hom] {L : LB A.left} (t : 𝟙_ (Over S) ⟶ A)
    (hL : L.IsLB) (h : Out.RelAmple A L) : Out.RelAmple A (rigTransl L t) := by
  have hL' : (rigTransl L t).IsLB := DVR.linComb_isLB _ hL _ _
  refine AmpleLocal.relAmple_of_locally S A _ hL' inferInstance inferInstance fun s => ?_
  let t₀ : S ⟶ A.left := t.left
  obtain ⟨i, hi⟩ := exists_chart hL (t₀ s)
  let U : S.Opens := t₀ ⁻¹ᵁ L.U i
  refine ⟨U, hi, ?_⟩
  have hp : IsPullback (transl t).left A.hom A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  have H := (isPullback_morphismRestrict A.hom U).flip.paste_horiz hp
  have k : (toUnit A ≫ t).left = A.hom ≫ t₀ := rfl
  obtain ⟨w, hw⟩ := lbIso_diff_pull hL (transl t).left (toUnit A ≫ t).left (A.hom ⁻¹ᵁ U).ι i fun z => by
    rw [k]; exact z.2
  exact relAmple_pull (A' := Over.mk (A.hom ∣_ U)) H hL (pull_isLB hL' _) ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) h

theorem relAmple_rigTransl_point : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L →
      Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro K _ B _ hB L hL a h
  have := hB.proper
  exact relAmple_rigTransl_of_section a hL h

end GlobalTheory.RigidTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleRigidTranslateLineBundleRationalPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_rigidTranslateLineBundle_rationalPoint : ∀ (K : Type) [Field K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), L.IsLB → ∀ a : 𝟙_ (Over (Sp K)) ⟶ B, Out.RelAmple B L → Out.RelAmple B (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.relAmple_rigTransl_point | exact GlobalTheory.RigidTranslate.relAmple_rigTransl_point | (intros; apply GlobalTheory.RigidTranslate.relAmple_rigTransl_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

noncomputable section

namespace GlobalTheory.VacLn.TrNondeg

theorem trace_pi' {R : Type} [Field R] {ι : Type} [Fintype ι]
    {E : ι → Type} [∀ c, CommRing (E c)] [∀ c, Algebra R (E c)] [∀ c, Module.Finite R (E c)]
    (x : ∀ c, E c) : Algebra.trace R (∀ c, E c) x = ∑ c, Algebra.trace R (E c) (x c) := by
  classical
  let b : ∀ c, Module.Basis (Fin (Module.finrank R (E c))) R (E c) := fun c => Module.finBasis R (E c)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.trace_eq_matrix_trace (b c), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

def conjM {F : Type} [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    mixedEmbedding.mixedSpace F :=
  (z.1, fun w => starRingEnd ℂ (z.2 w))

theorem trace_conjM_mul {F : Type} [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (conjM z * z) =
      ∑ w, z.1 w ^ 2 + ∑ w, 2 * Complex.normSq (z.2 w) := by
  rw [Algebra.trace_prod_apply, trace_pi', trace_pi']
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [conjM, Algebra.trace_self_apply, sq]
  · refine Finset.sum_congr rfl fun w _ => ?_
    simp [conjM, Algebra.trace_complex_apply, Complex.normSq_apply, Complex.mul_re]

theorem eq_zero_of_trace_conjM_mul {F : Type} [Field F] [NumberField F]
    (z : mixedEmbedding.mixedSpace F)
    (h : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (conjM z * z) = 0) : z = 0 := by
  rw [trace_conjM_mul] at h
  have h1 : 0 ≤ ∑ w, z.1 w ^ 2 := Finset.sum_nonneg fun w _ => sq_nonneg _
  have h2 : 0 ≤ ∑ w, 2 * Complex.normSq (z.2 w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  have e1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sq_nonneg (z.1 w)).1 (by linarith)
  have e2 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
    mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Complex.normSq_nonneg (z.2 w))).1 (by linarith)
  ext w
  · simpa using e1 w (Finset.mem_univ _)
  · have := e2 w (Finset.mem_univ _)
    have : Complex.normSq (z.2 w) = 0 := by linarith
    simpa using Complex.normSq_eq_zero.1 this

end GlobalTheory.VacLn.TrNondeg

namespace GlobalTheory.VacLn

theorem trPair_nondeg : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F),
    (∀ x, trPair F κ x y = 0) → y = 0 := by
  intro F _ _ κ _ y h
  have h0 := h (fun i => TrNondeg.conjM (y i))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [trPair_apply, map_sum] at h0
  have hnn : ∀ i, 0 ≤ Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (TrNondeg.conjM (y i) * y i) := by
    intro i
    rw [TrNondeg.trace_conjM_mul]
    exact add_nonneg (Finset.sum_nonneg fun w _ => sq_nonneg _)
      (Finset.sum_nonneg fun w _ => mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have e := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i).1 h0
  funext i
  exact TrNondeg.eq_zero_of_trace_conjM_mul _ (e i (Finset.mem_univ _))

end GlobalTheory.VacLn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerateStatement
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (y : κ → mixedEmbedding.mixedSpace F),
    (∀ x, trPair F κ x y = 0) → y = 0 := by
  first | exact @GlobalTheory.VacLn.trPair_nondeg | exact GlobalTheory.VacLn.trPair_nondeg | (intros; apply GlobalTheory.VacLn.trPair_nondeg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsIdealSpMapClosedPoint
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing GlobalTheory.Vanishing.H0 GlobalTheory.HermTools GlobalTheory.HilbertSamuel
open GlobalTheory.AllWt (Psi secZ exOf wtOf cuspOn latOn normOn petOn GoodOn suppOn LiesOn LiesOff)
open GlobalTheory.FlagMod (FlagCover FlagModel Frames frX ev)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.CompHt (hodgeWt uPrime genVal)

open GlobalTheory.Adelic (ptOf le_iff_ptOf_mem ptOf_comp resPt ptOf_resPt valR_ne_zero_iff LinSys)
open GlobalTheory.FlatLine (idem evR_idem idem_mem_suppOn)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Generic

variable {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c)

theorem asIdeal_spMap_closedPoint {A K : Type} [CommRing A] [Field K] (φ : A →+* K) :
    ((spMap φ (IsLocalRing.closedPoint K) : Sp A) : PrimeSpectrum A).asIdeal = RingHom.ker φ := by
  show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

theorem specializes_ptY_genFr (h : GenFrEx Xo c) {L : Type} [Field L] [Algebra c.F L] (Q : FrPt Xo c L)
    (hQ : LiesOn Z Q) : ptOf (X.ptY (genFr h Z)) ⤳ ptOf (X.ptY Q) := by
  obtain ⟨C, ψ, z, t', hz, hb⟩ := (Reg.evLaws_genFr_atlas E H Dw l Xo c).2.2.2 h L Q
  have hsp : ptOf (X.ptY (genFr h C.Z)) ⤳ ptOf (X.ptY Q) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [X.ptY_frBor C.bor, ← X.ptY_frMap C.gen, ← X.ptY_frBor hb, ← X.ptY_frMap hz, ptOf_comp, ptOf_comp]
    refine Specializes.map ?_ (X.ptY C.y).continuous
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    show ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal ≤
      ((spMap _ (IsLocalRing.closedPoint _) : Sp C.R) : PrimeSpectrum C.R).asIdeal
    rw [asIdeal_spMap_closedPoint, asIdeal_spMap_closedPoint]
    refine le_of_eq_of_le ((RingHom.injective_iff_ker_eq_bot _).1 ?_) bot_le
    exact Subtype.val_injective
  have hZ : C.Z = Z := by
    have h1 : ptOf (X.ptY Q) ∈ X.π ⁻¹ᵁ barComp Y Z := (le_iff_ptOf_mem _ _).1 ((ptY_le_iff X Z Q).2 hQ)
    have h2 := hsp.mem_open (Opens.isOpen _) h1
    have hl : LiesOn Z (genFr h C.Z) := (ptY_le_iff X Z _).1 ((le_iff_ptOf_mem _ _).2 h2)
    by_contra hne
    have h3 := GlobalTheory.AllWt.evC_eq_zero h hne (idem_mem_suppOn Z)
    rw [evC, evR_idem hl (GlobalTheory.FlagTan.fromTest_of_isLocalRing _)] at h3
    exact one_ne_zero h3
  exact hZ ▸ hsp

variable {X Z} (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

theorem exists_lift_genFr (h : GenFrEx Xo c) :
    ∃ z : Sp (Om Z) ⟶ M.X, z ≫ toFlag M = X.ptY (genFr h Z) ∧ ⊤ ≤ z ⁻¹ᵁ M.off := by
  have h1 : ⊤ ≤ X.ptY (genFr h Z) ⁻¹ᵁ (X.π ⁻¹ᵁ barComp Y Z) := (ptY_le_iff X Z _).2 (GlobalTheory.AllWt.liesOn_genFr h Z)
  have hr : Set.range (X.ptY (genFr h Z)) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩; exact ⟨⟨_, h1 (Set.mem_univ s)⟩, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY (genFr h Z) := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have hU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := fun s _ => by
    show (w ≫ inc₀ X Z) s ∈ flagOpen X
    rw [hw, ← X.pt_inc]
    exact (top_le_inc X) (Set.mem_univ _)
  obtain ⟨z, hz, -⟩ := M.existsUnique_lift w hU
  refine ⟨z, by rw [toFlag, ← Category.assoc, hz, hw], fun s _ => ?_⟩
  rw [M.off_eq]
  show (z ≫ M.σ) s ∈ U₀ X Z
  rw [hz]
  exact hU (Set.mem_univ s)

theorem isGenericPoint_of_lift (h : GenFrEx Xo c) {z : Sp (Om Z) ⟶ M.X} (hz : z ≫ toFlag M = X.ptY (genFr h Z))
    (hO : ⊤ ≤ z ⁻¹ᵁ M.off) : IsGenericPoint (ptOf z) Set.univ := by
  refine Set.eq_univ_of_univ_subset ?_
  rw [← M.dense.closure_eq]
  refine closure_minimal (fun y hy => ?_) isClosed_closure
  refine specializes_iff_mem_closure.1 ?_
  have hy' : y ∈ M.opn := hy
  have hyU : M.σ y ∈ U₀ X Z := hy'
  have hF : toFlag M y ∈ flagOpen X := hyU
  have hY : toFlag M y ∈ X.π ⁻¹ᵁ barComp Y Z := (M.σ y).2
  have hO' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ flagOpen X := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hF
  obtain ⟨_, hch⟩ := exists_chartFr _ hO'
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (toFlag M y)))
  have hk' : ⊤ ≤ (resPt y ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    refine (le_iff_ptOf_mem _ _).2 ?_
    rw [ptOf_comp, ptOf_resPt]
    exact hk
  obtain ⟨Q, hQ⟩ := hch k hk'
  have e : resPt y ≫ toFlag M = X.ptY Q := FlagCover.eq_ptY hQ.lies
  have hQZ : LiesOn Z Q := by
    refine (ptY_le_iff X Z Q).1 ((le_iff_ptOf_mem _ _).2 ?_)
    rw [← e, ptOf_comp, ptOf_resPt]
    exact hY
  have sp := specializes_ptY_genFr X Z h Q hQZ
  rw [← hz, ← e, ptOf_comp, ptOf_comp, ptOf_resPt] at sp
  have : IsOpenImmersion (M.opn.ι ≫ M.σ) := by
    rw [← morphismRestrict_ι]
    have := M.iso
    infer_instance
  have hg : IsOpenImmersion (M.opn.ι ≫ toFlag M) := by
    rw [toFlag, ← Category.assoc]
    infer_instance
  have hz' : ptOf z ∈ M.opn := by
    have := (le_iff_ptOf_mem _ _).1 hO
    rwa [M.off_eq] at this
  have sp' : (⟨ptOf z, hz'⟩ : M.opn) ⤳ ⟨y, hy'⟩ :=
    (M.opn.ι ≫ toFlag M).isOpenEmbedding.isInducing.specializes_iff.1 sp
  exact sp'.map continuous_subtype_val

end Generic

section Coords

variable {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c} {r : ℕ}
  {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}

theorem val_restr' {k : Type} [CommRing k] {T : Scheme.{0}} {p : T ⟶ Sp k} {B : LB T} {O O' : T.Opens} (h : O' ≤ O)
    {A : Type} [CommRing A] (x : Sp A ⟶ T) (i : B.ι) (hO : ⊤ ≤ x ⁻¹ᵁ O) (hO' : ⊤ ≤ x ⁻¹ᵁ O') (hi : ⊤ ≤ x ⁻¹ᵁ B.U i)
    (f : H0 p B O) : H0.val x i hO' hi (restr h f) = H0.val x i hO hi f :=
  evalPt_res x (inf_le_inf_right _ h) (GlobalTheory.FlagMod.le_preimage_inf hO hi) (GlobalTheory.FlagMod.le_preimage_inf hO' hi) _

theorem valR_eq_evalPt {A : Type} [CommRing A] {T : Scheme.{0}} (x : Sp A ⟶ T) (O : T.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (f : Γ(T, O)) : valR x O f = evalPt x O h f := dif_pos h

theorem chartFr_congr {S : Type} [CommRing S] [Algebra c.F S] {k : X.F.J} {z z' : Sp S ⟶ X.YY} (e : z = z')
    {hz : ⊤ ≤ z ⁻¹ᵁ X.F.U k} {hz' : ⊤ ≤ z' ⁻¹ᵁ X.F.U k} {Q : FrPt Xo c S} (h : X.F.ChartFr k z hz Q) :
    X.F.ChartFr k z' hz' Q := by
  subst e; exact h

theorem exists_chart_val (h : GenFrEx Xo c) {P : WtPar Dw} (R : Choice X Z U P) (hfree : FreeOnOpen X Z U P.u₁)
    {z : Sp (Om Z) ⟶ R.X} (hz : z ≫ toFlag R.toModif = X.ptY (genFr h Z)) (hO : ⊤ ≤ z ⁻¹ᵁ R.off) :
    ∃ (i : R.L.ι) (a : Om Z), ptOf z ∈ R.L.U i ∧ a ≠ 0 ∧ ∀ (g : Cusp Z U P.u₁) (w : space X Z U P.u₁),
      restr le_top w.1 = cuspSec X Z U P.u₁ g →
      valR z (R.L.U i) ((toSec (R.Δ₁.lift w)).f i) = a * genVal Z g.1 := by
  classical
  have e₁ : (z ≫ R.σ) ≫ inc₀ X Z = X.pt (genFr h Z) ≫ X.inc := by
    rw [Category.assoc, X.pt_inc]; exact hz
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (X.F.cover.ge (Set.mem_univ (ptOf ((z ≫ R.σ) ≫ inc₀ X Z))))
  have hk₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ X.F.U k := (le_iff_ptOf_mem _ _).2 hk
  have hk₁ : ⊤ ≤ (X.pt (genFr h Z) ≫ X.inc) ⁻¹ᵁ X.F.U k := e₁ ▸ hk₂
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor (genFr h Z) k hk₁
  have hQ₂ : X.F.ChartFr k ((z ≫ R.σ) ≫ inc₀ X Z) hk₂ Q := chartFr_congr e₁.symm hQ
  have hU : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ U₀ X Z := by
    intro s _
    have := hO (Set.mem_univ s)
    rw [R.off_eq] at this
    exact this
  have hO₂ : ⊤ ≤ ((z ≫ R.σ) ≫ inc₀ X Z) ⁻¹ᵁ flagOpen X := hU
  obtain ⟨n, hn⟩ := exists_chart R.Δ₁.isLB (ptOf z)
  have hz' : ptOf z ∈ R.off := (le_iff_ptOf_mem _ _).1 hO
  have hm : ptOf z ∈ ((L₀ X Z P.u₁).pull R.σ).U (flagIdx R.toModif P.u₁ k) := (R.com.mem _ _ _).2 hk
  have hi : ptOf z ∈ R.L.U (flagIdx R.toModif P.u₁ k, n) := ⟨hm, hn⟩
  have hτ : valR z _ (R.Δ₁.t.f n) ≠ 0 := (valR_ne_zero_iff z hn _).2
    ((mem_nonzeroLocus_iff_basicOpen R.Δ₁.t hn).1 ((R.Δ₁.mem_nonzeroLocus _).2 (R.notMem_support hfree _ hz')))
  obtain ⟨T, hT0, hT⟩ : ∃ T : Om Z, T ≠ 0 ∧ ∀ f : secZ Xo c (exOf Dw P.u₁ 0),
      evR Xo c f.1 (genFr h Z) = T * H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂ (secOf X _ f) :=
    ⟨_, Units.ne_zero _, fun f => evR_eq_val_secOf f hO₂ hQ₂ ht⟩
  refine ⟨(flagIdx R.toModif P.u₁ k, n), (valR z _ (R.Δ₁.t.f n) * T)⁻¹, hi, inv_ne_zero (mul_ne_zero hτ hT0),
    fun g w hw => ?_⟩
  have hTop : ⊤ ≤ z ⁻¹ᵁ (⊤ : R.X.Opens) := fun _ _ => trivial
  have hTop' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (⊤ : (Y₀ X Z).Opens) := fun _ _ => trivial
  have hi' := (le_iff_ptOf_mem z _).2 hi
  have hm' := (le_iff_ptOf_mem z _).2 hm
  have hn' := (le_iff_ptOf_mem z _).2 hn
  have hm'' : ⊤ ≤ (z ≫ R.σ) ⁻¹ᵁ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := by
    have hm₀ : R.σ (ptOf z) ∈ (L₀ X Z P.u₁).U (flagIdx R.toModif P.u₁ k PUnit.unit) := mem_pull.1 hm
    exact (le_iff_ptOf_mem _ _).2 hm₀
  have v₁ : valR z (R.L.U (flagIdx R.toModif P.u₁ k, n)) ((toSec (R.Δ₁.lift w)).f (flagIdx R.toModif P.u₁ k, n)) =
      H0.val z _ hTop hi' (R.Δ₁.lift w) := by
    have := H0.val_ofSec (p := R.str) z (flagIdx R.toModif P.u₁ k, n) hTop hi' (toSec (R.Δ₁.lift w))
    rw [ofSec_toSec] at this
    rw [this, valR_eq_evalPt z _ hi']
  have v₂ := (divChart (LB.isLB_pull (isLB_L₀ X Z P.u₁) R.σ) R.Δ₁.isLB).val_mul (ofSec R.str ⊤ R.Δ₁.t) (R.Δ₁.lift w)
    (flagIdx R.toModif P.u₁ k, n) z hTop hn' hi' hm'
  have v₃ : H0.val z _ hTop hm' (H0.pull R.σ le_top w.1) = H0.val (z ≫ R.σ) _ hTop' hm'' w.1 :=
    H0.val_pull R.σ le_top z _ hTop hm' hTop' hm'' w.1
  have v₄ := val_restr' (p := str₀ X Z) (le_top : U₀ X Z ≤ ⊤) (z ≫ R.σ) _ hTop' hU hm'' w.1
  have v₅ : H0.val (z ≫ R.σ) _ hU hm'' (cuspSec X Z U P.u₁ g) = H0.val (B := X.LL (exOf Dw P.u₁ 0)) ((z ≫ R.σ) ≫ inc₀ X Z) k hO₂ hk₂
      (secOf X _ ⟨g.1, cusp_le_secZ Z U _ g.2⟩) :=
    H0.val_pull (inc₀ X Z) le_rfl (z ≫ R.σ) _ hU hm'' hO₂ hk₂ _
  have v₆ : genVal Z g.1 = evR Xo c g.1 (genFr h Z) := rfl
  have v₇ : H0.val z _ hTop hn' (ofSec R.str ⊤ R.Δ₁.t) = valR z _ (R.Δ₁.t.f n) := by
    rw [H0.val_ofSec, valR_eq_evalPt z _ hn']
  have v₈ := hT ⟨g.1, cusp_le_secZ Z U _ g.2⟩
  rw [v₁, v₆, v₈, ← v₅, ← hw, v₄, ← v₃, ← R.Δ₁.incl_lift w]
  have v₉ : H0.val z _ hTop hm' (R.Δ₁.incl ⊤ (R.Δ₁.lift w)) = valR z _ (R.Δ₁.t.f n) * H0.val z _ hTop hi' (R.Δ₁.lift w) :=
    v₂.trans (congrArg (· * _) v₇)
  rw [v₉]
  field_simp

end Coords

theorem compPresents_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), GlobalTheory.CompHt.CompPresents U x V dict Z (GlobalTheory.AllWt.wtOf Dw P.u₁ 0) (h.data f₁ f₂ th k).toHermSys := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k
  have hG : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  refine ⟨(dimFlag_eq Dw).symm, f₁.b, f₁.isFrame, ?_⟩
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr R.toModif hG
  have hgen := isGenericPoint_of_lift R.toModif hG hz hO
  have hV := (R.isAlgebraicData R.Δ₁ h.ext₁.equiv f₁ (dense_U₀ X Z) h.conn h.one_le k.abelian₂).variety
  have : IsIntegral (h.data f₁ f₂ th k).toHermSys.toLinSys.Y := hV.isIntegral
  have hstr : z ≫ (h.data f₁ f₂ th k).toHermSys.toLinSys.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag R.toModif ≫ flagStr X) = _
    rw [← Category.assoc, hz, ptY_str]
  obtain ⟨i, a, hi, ha, hv⟩ := exists_chart_val hG R h.free₁ hz hO
  obtain ⟨b, hb, hb', -⟩ := (h.data f₁ f₂ th k).toHermSys.toLinSys.exists_frame_change z i hi
  refine GlobalTheory.CompHt.imageIdeal_eq_coneIdeal_of_generic c.F (Om Z) _ ⟨z, hstr⟩ hgen (b⁻¹ * a) _
    (mul_ne_zero (inv_ne_zero hb) ha) (funext fun j => ?_)
  have e₁ := hb' ((h.data f₁ f₂ th k).toHermSys.toLinSys.b j)
  have e₂ := hv (f₁.b j) (h.ext₁.equiv (f₁.b j)) (h.ext₁.restr_equiv _)
  have e₃ := e₁.symm.trans e₂
  show (h.data f₁ f₂ th k).toHermSys.toLinSys.val z _ = (b⁻¹ * a) * genVal Z (f₁.b j).1
  rw [mul_assoc, ← e₃, inv_mul_cancel_left₀ hb]

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open Matrix
namespace GlobalTheory.AdelMatLatRight


open NumberField IsDedekindDomain in
open Matrix in
theorem _root_.GlobalTheory.AdelMatLatRight.transpose_mem_latAtV {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (w : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) :
    ∀ γ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y w, γᵀ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Y X w := by
  intro γ hγ
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV at hγ ⊢
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hai, x, hx, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    rw [transpose_smul]
    congr 1
    ext i j
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, vecMulVec_apply, mul_comm]
  | zero => simpa using zero_mem _
  | add u v _ _ hu hv => simpa [transpose_add] using add_mem hu hv
  | neg u _ hu => simpa [transpose_neg] using neg_mem hu

theorem almost_all_stable_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), Y.L.IsFullLattice E → ∀ N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  refine (GlobalTheory.AdelMatLat.almost_all_stable F E d n Y X hY N).subset fun w hw h => hw fun γ hγ => ?_
  have h1 := transpose_mem_latAtV Y X w _ (h _ (transpose_mem_latAtV X Y w γ hγ))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h1

end GlobalTheory.AdelMatLatRight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRightStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stable_almost_all_places_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ) (X : Spc F E n)
    (Y : Spc F E d), Y.L.IsFullLattice E → ∀ N : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, γ * Matrix.transpose N ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hY N
  first
  | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right F E n d X Y hY N
  | exact GlobalTheory.AdelMatLatRight.almost_all_stable_right F E n d X Y hY.toIsLattice N
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.La1sqEqOfUnXEq
noncomputable section

namespace GlobalTheory.CuspUnif

section Decay

open NumberField ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_decay (X : Data E r) (hr : 0 < r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {C c : ℝ} (hc : 0 < c) (h : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ C * Real.exp (-c / X.firstMinimumSq x)) : P ∈ X.SS la := by
  have := GlobalTheory.ModeDecay.nonempty_cmType X
  set f : ℝ := (Fintype.card X.Ψ : ℝ) with hf
  have hf0 : 0 < f := Nat.cast_pos.2 Fintype.card_pos
  have hπ := Real.pi_pos
  refine ⟨hP, fun ξ hξ x hx => GlobalTheory.ModeDecay.fj_eq_zero_of_decay GlobalTheory.fj_norm_mul_exp_le_sup_flow
    ReciprocityTheory.ChartRestriction.G.AR.Inst.la1GGStatement_firstMinimum r X la P (c / (8 * Real.pi * f)) hP.1
    ⟨Real.sqrt |C|, 0, le_rfl, fun y hy η hη h2 => ?_⟩ ξ hξ 0 (by simpa using by positivity) x hx⟩
  set t := ⨅ τ, X.tt η y τ with ht
  have ht2 : 2 ≤ t := le_ciInf h2
  have ht' : 0 < t := by linarith
  have hpos : ∀ v : Fin r → E, v ≠ 0 → ∀ τ, 0 < X.c τ * X.maj y τ (Data.emb τ.1 v) := fun v hv τ =>
    mul_pos (TwoSidedBoostBounds.c_pos X τ) (X.maj_pos hy τ (emb_ne_zero τ.1 hv))
  have hle : ∀ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) ≤ 1 / t := fun τ =>
    (le_one_div ht' (hpos η hη.2.2 τ)).1 (ciInf_le (f := fun τ => X.tt η y τ) (Finite.bddBelow_range _) τ)
  have hla : X.firstMinimumSq y ≤ f / t :=
    calc X.firstMinimumSq y ≤ ∑ τ, X.c τ * X.maj y τ (Data.emb τ.1 η) := by
          refine csInf_le ⟨0, ?_⟩ ⟨η, hη.1, hη.2.2, rfl⟩
          rintro _ ⟨v, -, hv, rfl⟩
          exact Finset.sum_nonneg fun τ _ => (hpos v hv τ).le
      _ ≤ ∑ _τ : X.Ψ, 1 / t := Finset.sum_le_sum fun τ _ => hle τ
      _ = f / t := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  have hla0 : 0 < X.firstMinimumSq y := Real.sqrt_pos.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.la1_pos_of_mem_dom X hr hy)
  have hexp : Real.exp (-c / X.firstMinimumSq y) ≤ Real.exp (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have : c / (f / t) ≤ c / X.firstMinimumSq y := div_le_div_of_nonneg_left hc.le hla0 hla
    have e1 : ((2 : ℕ) : ℝ) * (-4 * Real.pi * (c / (8 * Real.pi * f)) * t) = -(c / (f / t)) := by
      push_cast
      field_simp
      norm_num
    rw [e1, neg_div]
    linarith
  rw [Real.rpow_zero, mul_one]
  refine (Real.le_sqrt_of_sq_le ((h y hy).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
    (mul_le_mul_of_nonneg_left hexp (abs_nonneg C))))).trans_eq ?_
  rw [Real.sqrt_mul (abs_nonneg C), Real.sqrt_sq (Real.exp_pos _).le]

end Decay

section Unif

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT GlobalTheory.OrthoMetric GlobalTheory.SupFull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

end Unif

end GlobalTheory.CuspUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundle
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)

namespace GlobalTheory.RigidTranslate

open GlobalTheory.PolTranslate ReciprocityTheory.ChartRestriction.G.DVR

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem toUnit_inv_mul_self (a : 𝟙_ (Over S) ⟶ A) (T : Over S) :
    (toUnit T ≫ a⁻¹) * (toUnit T ≫ a) = 1 := by
  rw [← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one]

theorem transl_inv_comp_transl (a : 𝟙_ (Over S) ⟶ A) : transl a⁻¹ ≫ transl a = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]

theorem kTriv_pull_transl (x : 𝟙_ (Over S) ⟶ A) {L : LB A.left} (hL : L.IsLB) (h : Out.KTriv A L) :
    Out.KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x⁻¹).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x⁻¹))) V
  have k₂ : T ◁ transl x⁻¹ ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_inv_comp_transl, Category.comp_id]
  have k₃ : T ◁ transl x⁻¹ ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_inv_mul_self, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

end

theorem kTriv_rigTransl_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  intro S A _ L hL a h R _ s y hy
  refine kTriv_pull_transl a hL h R s y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, gen_of_lbIso (pull_isLB (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) _)
    (pull_isLB (DVR.linComb_isLB _ (pull_isLB hL _) _ _) _)
    (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_diff_diff hL _ _ _ _ ?_)) c hc⟩
  rw [comp_const, comp_const]

end GlobalTheory.RigidTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTrivialRigidTranslateLineBundleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open MonoidalCategory CartesianMonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic (Pic cls lam)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrivial_rigidTranslateLineBundle : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ a : 𝟙_ (Over S) ⟶ A, Out.KTriv A L → Out.KTriv A (GlobalTheory.RigidTranslate.rigTransl L a) := by
  first | exact @GlobalTheory.RigidTranslate.kTriv_rigTransl_any | exact GlobalTheory.RigidTranslate.kTriv_rigTransl_any | (intros; apply GlobalTheory.RigidTranslate.kTriv_rigTransl_any <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLanglandsGaloisCompatStatement
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_galois_compat : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (B : ValuationSubring Ω) (h : IsPlaceOver B w)
      (rc : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E) → GlobalTheory.WeilDeligne.WD h), GlobalTheory.LocLanglands.IsRec h rc →
    ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    ∀ t : ℝ, GlobalTheory.WeilDeligne.wdOf h hl ι r = (rc (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw t →
    ∀ g : G E Ω, IsFrob (F := E) B (normV w) g →
      (r (g ^ (-1 : ℤ))).val.charpoly = (S.map fun z : ℂˣ =>
        Polynomial.X - Polynomial.C (ι.symm ((z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ ((-t : ℝ) : ℂ)))).prod := by
  first | exact @GlobalTheory.GeomFrobChar.charpoly_geomFrob | exact GlobalTheory.GeomFrobChar.charpoly_geomFrob | (intros; apply GlobalTheory.GeomFrobChar.charpoly_geomFrob <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroup
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.UnitMinorStable

theorem mul_mem_unitMinorSet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  intro k _ _ _ _ n d E Y hE hY
  obtain ⟨hYi, f, hf⟩ := hY
  have hEi := ((GlobalTheory.SplitFlip.mem_KO_iff E).1 hE).1
  refine ⟨fun i j => ?_, f, ?_⟩
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hEi i l) (hYi l j)
  · have hsub : (E.val * Y).submatrix id f = E.val * Y.submatrix id f := by
      ext i j; rfl
    have hdet := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hE
    have hg : ((GlobalTheory.SplitFlip.gdet E : kˣ) : k) = E.val.det := rfl
    rw [hsub, Matrix.det_mul, map_mul, hf, mul_one, ← hg, hdet]

end GlobalTheory.UnitMinorStable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroupStatement
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_minor_stable_integral_group : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  first | exact @GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet | exact GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet | (intros; apply GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffEqMapDomain
noncomputable section

open Formalism.BasicNotions

namespace GlobalTheory.GoodIdemTie

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters.factPrime

theorem idemTie_of_tameTie (hG : GlobalTheory.Published.GreenCuspidal) (D : D7) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hT : GlobalTheory.DimPartsCompare.TameTie D om) : GlobalTheory.DimPartsCompare.IdemTie D om :=
  hT.idemTie hG.green

end GlobalTheory.GoodIdemTie

end
end
