module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPair
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftGrow

theorem reduction_unif {D : D7} {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) :
    ∃ M : ℕ, ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) →
      ∃ (S : Finset (GA D V)) (C : ℝ), 0 ≤ C ∧ ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧
        γ * g = x * a * k ∧ 1 + normInf θ V a ≤ C * (height θ V g : ℝ) ^ M := by
  obtain ⟨d, C, M, hd, h⟩ := GlobalTheory.T.unitary_reduction_polynomial_height_bound D θ V hθ
    (GlobalTheory.T.orthogonalFrame_of_anisotropicFiniteLengths _ (GlobalTheory.T.anisotropicFiniteLengths_of_shortLatticeVector _ (GlobalTheory.T.shortLatticeVectorBoundedSize_of_orthogonalFrame _ (GlobalTheory.T.orthogonalAnisotropicFrame_bounded_CM _)))) (GlobalTheory.T.unitaryLatticeDenominatorHeightBound_proof D θ V)
  refine ⟨M + 1, fun U hU => ?_⟩
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_finite_cosets_adelicUnitary_bounded_denominator D V U hU d hd
  obtain ⟨hm, C', hC'⟩ := GlobalTheory.T.normInf_submultiplicative_le_adelicHeight D θ V
  obtain ⟨-, -, -, r4, r5, r6, r7, r8⟩ := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  refine ⟨S, 1 + |C * C'|, by positivity, fun g => ?_⟩
  obtain ⟨γ, hγ, h1, h2⟩ := h g
  obtain ⟨k, hk, a, ha, e⟩ := r7 (γ * g)
  have e' : (γ * g)⁻¹ = k⁻¹ * a⁻¹ := by rw [e, ← r6 a ha k hk, _root_.mul_inv_rev]
  obtain ⟨x, hx, h3, h4⟩ := hS k hk fun i j => by
    have := h1 i j
    rwa [e', e, r8 _ _ ha, r8 _ _ (inv_mem ha)] at this
  refine ⟨γ, hγ, x, hx, a, ha, _, h3, h4, ?_, ?_⟩
  · rw [mul_assoc, r6 a ha _ h4, e, ← mul_assoc, mul_inv_cancel_left]
  · have h5 : normInf θ V a = normInf θ V (γ * g) := by
      unfold normInf
      rw [e', e]
      simp only [r4, r5 k hk, r5 _ (inv_mem hk), one_mul]
    have h6 : normInf θ V a ≤ C * C' * (height θ V g : ℝ) ^ (M + 1) := by
      rw [h5]
      refine (hm γ g).trans ((mul_le_mul h2 (hC' g) (GlobalTheory.SmoothForms.normInf_nonneg g)
        ((GlobalTheory.SmoothForms.normInf_nonneg γ).trans h2)).trans_eq ?_)
      ring
    have h7 : (1 : ℝ) ≤ (height θ V g : ℝ) ^ (M + 1) :=
      one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g)
    rw [add_mul, one_mul]
    exact add_le_add h7 (h6.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h7)))

theorem growth_pair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  intro D θ hθ V W N
  obtain ⟨M, hM⟩ := reduction_unif hθ V
  obtain ⟨M', hM'⟩ := reduction_unif hθ W
  refine ⟨(M + M') * N, ?_⟩
  rintro K hL ⟨U, U', hU, hU', hR⟩ hG
  obtain ⟨S, A, hA, hS⟩ := hM U hU
  obtain ⟨S', A', hA', hS'⟩ := hM' U' hU'
  choose C hC using hG
  refine ⟨(∑ p ∈ S ×ˢ S', |C p.1 p.2|) * (A * A') ^ N, fun g h => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk2, e, hb⟩ := hS g
  obtain ⟨δ, hδ, y, hy, b, hb', k', hk', hk2', e', hb2⟩ := hS' h
  have g1 : (1 : ℝ) ≤ (height θ V g : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ V g
  have h1 : (1 : ℝ) ≤ (height θ W h : ℝ) := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ W h
  have na : 0 ≤ 1 + normInf θ V a := add_nonneg zero_le_one (GlobalTheory.SmoothForms.normInf_nonneg a)
  have nb : 0 ≤ 1 + normInf θ W b := add_nonneg zero_le_one (GlobalTheory.SmoothForms.normInf_nonneg b)
  have key : (1 + normInf θ V a) * (1 + normInf θ W b) ≤
      A * A' * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ (M + M') := by
    have p1 : (height θ V g : ℝ) ^ M ≤ (height θ V g : ℝ) ^ (M + M') := pow_le_pow_right₀ g1 (Nat.le_add_right _ _)
    have p2 : (height θ W h : ℝ) ^ M' ≤ (height θ W h : ℝ) ^ (M + M') := pow_le_pow_right₀ h1 (Nat.le_add_left _ _)
    have q1 := hb.trans (mul_le_mul_of_nonneg_left p1 hA)
    have q2 := hb2.trans (mul_le_mul_of_nonneg_left p2 hA')
    refine (mul_le_mul q1 q2 nb (na.trans q1)).trans_eq ?_
    rw [mul_pow]; ring
  rw [← hL γ hγ δ hδ g h, e, e', hR k hk hk2 k' hk' hk2', pow_mul, mul_assoc, ← mul_pow]
  refine (hC x y a ha b hb').trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun p : GA D V × GA D W => |C p.1 p.2|) (fun _ _ => abs_nonneg _)
      (Finset.mk_mem_product hx hy)))
    (pow_le_pow_left₀ (mul_nonneg na nb) key N) (pow_nonneg (mul_nonneg na nb) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

end GlobalTheory.Mem.LiftGrow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicHeightGrowthOfCosetGrowthUnitaryPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHeight_growth_of_cosetGrowth_unitaryPair : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (N : ℕ), ∃ N' : ℕ, ∀ K : GA D V → GA D W → ℂ, (∀ γ ∈ GQ V, ∀ δ ∈ GQ W, ∀ g h, K (γ * g) (δ * h) = K g h) → (∃ (U : Subgroup (GA D V)) (U' : Subgroup (GA D W)), IsOpen (U : Set (GA D V)) ∧ IsOpen (U' : Set (GA D W)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ k' ∈ U', k' ∈ GfC W → ∀ g h, K (g * k) (h * k') = K g h) → (∀ x y, ∃ C : ℝ, ∀ a ∈ GinfC V, ∀ b ∈ GinfC W, ‖K (x * a) (y * b)‖ ≤ C * ((1 + normInf θ V a) * (1 + normInf θ W b)) ^ N) → ∃ C : ℝ, ∀ g h, ‖K g h‖ ≤ C * ((height θ V g : ℝ) * (height θ W h : ℝ)) ^ N' := by
  first | exact @GlobalTheory.Mem.LiftGrow.growth_pair | exact GlobalTheory.Mem.LiftGrow.growth_pair | (intros; apply GlobalTheory.Mem.LiftGrow.growth_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGL
open NumberField IsDedekindDomain Matrix
open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.IwasawaFinAd

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def coordV (v : HeightOneSpectrum (𝓞 F)) : FiniteAdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def locM (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  RingHom.mapMatrix (coordV v) M

def locGL (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) →* GL (Fin n) (v.adicCompletion F) :=
  Units.map (RingHom.mapMatrix (coordV v)).toMonoidHom

theorem locM_mul (v : HeightOneSpectrum (𝓞 F)) (M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    locM v (M * N) = locM v M * locM v N := map_mul _ _ _

theorem locM_one (v : HeightOneSpectrum (𝓞 F)) :
    locM v (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) = 1 := map_one _

theorem matrix_ext_loc {M N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)}
    (h : ∀ v, locM v M = locM v N) : M = N := by
  refine Matrix.ext fun i j => FiniteAdeleRing.ext F fun v => ?_
  exact congrFun (congrFun (h v) i) j

theorem gl_ext_loc {g h : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)} (e : ∀ v, locGL v g = locGL v h) :
    g = h :=
  Units.ext (matrix_ext_loc fun v => congrArg Units.val (e v))

def IntAt (v : HeightOneSpectrum (𝓞 F)) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers F

theorem intAt_one (v : HeightOneSpectrum (𝓞 F)) : IntAt v (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (v.adicCompletionIntegers F).one_mem
  · exact (v.adicCompletionIntegers F).zero_mem

def glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    (⟨fun v => x v i j, hx.mono fun v h => h i j⟩ :
      Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

theorem locM_glueM (x : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v)) (v : HeightOneSpectrum (𝓞 F)) :
    locM v (glueM x hx) = x v := by
  ext i j
  rfl

def glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) :
    GL (Fin n) (FiniteAdeleRing (𝓞 F) F) where
  val := glueM (fun v => (x v).val) (hx.mono fun _ h => h.1)
  inv := glueM (fun v => (x v)⁻¹.val) (hx.mono fun _ h => h.2)
  val_inv := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.mul_inv (x v)
  inv_val := matrix_ext_loc fun v => by
    rw [locM_mul, locM_glueM, locM_glueM, locM_one]; exact Units.inv_mul (x v)

theorem locGL_glueGL (x : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (v.adicCompletion F))
    (hx : ∀ᶠ v in Filter.cofinite, IntAt v (x v).val ∧ IntAt v (x v)⁻¹.val) (v : HeightOneSpectrum (𝓞 F)) :
    locGL v (glueGL x hx) = x v :=
  Units.ext (locM_glueM _ (hx.mono fun _ h => h.1) v)

theorem eventually_intAt (M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ v in Filter.cofinite, IntAt v (locM v M) := by
  unfold IntAt
  rw [Filter.eventually_all]
  intro i
  rw [Filter.eventually_all]
  intro j
  exact (M i j).2

theorem upper_eq_uni_mul_diag {K : Type} [Field K] (b : GL (Fin n) K) (hb : b.val.BlockTriangular id) :
    ∃ u t : GL (Fin n) K, PIW.ClassFinD.IsUpperUni u.val ∧ PIW.ClassFinD.IsDiagM t.val ∧ b = u * t := by
  have hdet0 : b.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
  have hne : ∀ i, b.val i i ≠ 0 := by
    intro i h
    apply hdet0
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h
  let t : GL (Fin n) K :=
    ⟨diagonal (fun i => b.val i i), diagonal (fun i => (b.val i i)⁻¹),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact mul_inv_cancel₀ (hne i),
      by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact inv_mul_cancel₀ (hne i)⟩
  have hU : ∀ i j, (b * t⁻¹).val i j = b.val i j * (b.val j j)⁻¹ := by
    intro i j
    change (b.val * diagonal (fun i => (b.val i i)⁻¹)) i j = _
    rw [mul_diagonal]
  refine ⟨b * t⁻¹, t, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_, by group⟩
  · rw [hU, hb hij, zero_mul]
  · rw [hU, mul_inv_cancel₀ (hne i)]
  · exact diagonal_apply_ne _ hij

theorem isUpperUni_one {K : Type} [CommRing K] : PIW.ClassFinD.IsUpperUni (1 : Matrix (Fin n) (Fin n) K) :=
  ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩

theorem isDiagM_one {K : Type} [CommRing K] : PIW.ClassFinD.IsDiagM (1 : Matrix (Fin n) (Fin n) K) :=
  fun i j hij => Matrix.one_apply_ne hij

theorem intAt_of_glint (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin n) (v.adicCompletion F))
    (hk : k ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v)) : IntAt v k.val ∧ IntAt v k⁻¹.val := by
  obtain ⟨K, rfl⟩ := hk
  refine ⟨fun i j => (K.val i j).2, fun i j => ?_⟩
  rw [← map_inv]
  exact ((K⁻¹).val i j).2

end GlobalTheory.IwasawaFinAd

namespace GlobalTheory.IwasawaFinAd

open PIW.ClassFinD

theorem iwasawaAf : PIW.ClassFinD.IwasawaAf := by
  classical
  intro F _ _ n g
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    IntAt v (locGL v g).val ∧ IntAt v (locGL v g)⁻¹.val
  have hgood : ∀ᶠ v in Filter.cofinite, good v := by
    refine (eventually_intAt g.val).and ((eventually_intAt (g⁻¹).val).mono fun v h => ?_)
    rw [← map_inv]
    exact h
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ u t k : GL (Fin n) (v.adicCompletion F),
      IsUpperUni u.val ∧ IsDiagM t.val ∧ IntAt v k.val ∧ IntAt v k⁻¹.val ∧ locGL v g = u * t * k ∧
      (good v → u = 1 ∧ t = 1 ∧ k = locGL v g) := by
    intro v
    by_cases hv : good v
    · exact ⟨1, 1, locGL v g, isUpperUni_one, isDiagM_one, hv.1, hv.2, by rw [one_mul, one_mul],
        fun _ => ⟨rfl, rfl, rfl⟩⟩
    · obtain ⟨b, k, hb, hk, hbk⟩ := Formalism.UG.P.spherical_iwasawa F v (locGL v g)
      obtain ⟨u, t, hu, ht, rfl⟩ := upper_eq_uni_mul_diag b hb
      obtain ⟨hk1, hk2⟩ := intAt_of_glint v k hk
      exact ⟨u, t, k, hu, ht, hk1, hk2, hbk, fun h => absurd h hv⟩
  choose uL tL kL huL htL hkL hkL' hgL hgoodL using hloc
  have hu : ∀ᶠ v in Filter.cofinite, IntAt v (uL v).val ∧ IntAt v (uL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have ht : ∀ᶠ v in Filter.cofinite, IntAt v (tL v).val ∧ IntAt v (tL v)⁻¹.val :=
    hgood.mono fun v hv => by
      rw [(hgoodL v hv).2.1, inv_one]
      exact ⟨intAt_one v, intAt_one v⟩
  have hk : ∀ᶠ v in Filter.cofinite, IntAt v (kL v).val ∧ IntAt v (kL v)⁻¹.val :=
    Filter.Eventually.of_forall fun v => ⟨hkL v, hkL' v⟩
  refine ⟨glueGL uL hu, glueGL tL ht, glueGL kL hk, ⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hij => ?_,
    ⟨fun i j v => hkL v i j, fun i j v => hkL' v i j⟩, ?_⟩
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i j) = coordV v 0
    rw [map_zero]
    exact (huL v).1 i j hij
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL uL hu).val i i) = coordV v 1
    rw [map_one]
    exact (huL v).2 i
  · refine FiniteAdeleRing.ext F fun v => ?_
    change coordV v ((glueGL tL ht).val i j) = coordV v 0
    rw [map_zero]
    exact htL v i j hij
  · refine gl_ext_loc fun v => ?_
    rw [map_mul, map_mul, locGL_glueGL, locGL_glueGL, locGL_glueGL]
    exact hgL v

end GlobalTheory.IwasawaFinAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFiniteAdelesGLStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaDecomposition_finiteAdeles_GL : PIW.ClassFinD.IwasawaAf := by
  first | exact @GlobalTheory.IwasawaFinAd.iwasawaAf | exact GlobalTheory.IwasawaFinAd.iwasawaAf | (intros; apply GlobalTheory.IwasawaFinAd.iwasawaAf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SemilinearBasisImageIndepOfBasis
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem semilinear_basis_image_indep_of_basis :
    ∀ (K : Type) [Field K] (e : K →+* ℂ) (V : Type) [AddCommGroup V] [Module K V]
      (W : Type) [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) (ι κ : Type)
      (b : Module.Basis ι K V) (b' : Module.Basis κ K V),
      (LinearIndependent ℂ (fun i => j (b i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b i)) = ⊤) →
      LinearIndependent ℂ (fun i => j (b' i)) ∧
        Submodule.span ℂ (Set.range fun i => j (b' i)) = ⊤ := by
  intro K _ e V _ _ W _ _ j ι κ b b' ⟨hli, hsp⟩
  letI : Algebra K ℂ := e.toAlgebra
  letI : Module K W := Module.compHom W e
  haveI : IsScalarTower K ℂ W := ⟨fun k c w => by
    change (e k * c) • w = e k • c • w
    exact mul_smul _ _ _⟩
  let j' : V →ₗ[K] W :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun k v => j.map_smulₛₗ k v }
  let L : ℂ ⊗[K] V →ₗ[ℂ] W := j'.liftBaseChange ℂ
  have hL : ∀ v : V, L (1 ⊗ₜ[K] v) = j v := fun v => by
    simp [L, j']
  let c : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  let E : ℂ ⊗[K] V ≃ₗ[ℂ] W := (b.baseChange ℂ).equiv c (Equiv.refl ι)
  have hE : (E : ℂ ⊗[K] V →ₗ[ℂ] W) = L := by
    refine (b.baseChange ℂ).ext fun i => ?_
    rw [LinearEquiv.coe_coe]
    simp only [E, Module.Basis.equiv_apply, Equiv.refl_apply, c, Module.Basis.mk_apply]
    rw [Module.Basis.baseChange_apply, hL]
  have hb : (fun i => j (b' i)) = ⇑((b'.baseChange ℂ).map E) := by
    funext i
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, ← hL, ← hE, LinearEquiv.coe_coe]
  rw [hb]
  exact ⟨Module.Basis.linearIndependent _, Module.Basis.span_eq _⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerProductPositiveDefinite
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem re_pos_of_majAt {K V ι M : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (σ : K →+* ℂ) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : IsUnit (X (InfinitePlace.mk σ)).det) (e : V →ₛₗ[σ] M) (Q : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h : ∀ x, (Formalism.HermitianLatticesTheory.majAt b X (InfinitePlace.mk σ) x x).re = (Q (e x) (e x)).re)
    (φ : M) (hφ : φ ∈ Submodule.span ℂ (Set.range fun a => e (b a))) (h0 : φ ≠ 0) :
    0 < (Q φ φ).re := by
  set v := InfinitePlace.mk σ with hv
  obtain ⟨ρ, hρc, hρρ, hρσ⟩ : ∃ ρ : ℂ →+* ℂ, Continuous ρ ∧ (∀ z, ρ (ρ z) = z) ∧
      ∀ x, ρ (v.embedding x) = σ x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact ⟨RingHom.id ℂ, continuous_id, fun _ => rfl, fun x => by rw [hv, h1]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun z => Complex.conj_conj z, fun x => by
        rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]⟩
  have hd0 : DenseRange (Pi.map (fun _ : ι => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have key : ∀ w : ι → ℂ, (Q (∑ a, ρ (w a) • e (b a)) (∑ a, ρ (w a) • e (b a))).re =
      ∑ i, ‖((X v)⁻¹.mulVec w) i‖ ^ 2 := by
    intro w
    induction w using hd0.induction_on with
    | hp =>
      apply isClosed_eq
      · set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            RingHom.id_apply]
        have hρ : ∀ i : ι, Continuous (fun y : ι → ℂ => ρ (y i)) :=
          fun i => hρc.comp (continuous_apply i)
        fun_prop
      · have : Continuous fun w : ι → ℂ => (X v)⁻¹.mulVec w :=
          Continuous.matrix_mulVec continuous_const continuous_id
        fun_prop
    | ih y =>
      have h1 := h (b.equivFun.symm y)
      have h2 : e (b.equivFun.symm y) =
          ∑ a, ρ (Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y a) • e (b a) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [b.equivFun_symm_apply, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [LinearMap.map_smulₛₗ, Pi.map_apply, hρσ]
      have h3 : Formalism.HermitianLatticesTheory.vecAt b v (b.equivFun.symm y) = Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y := by
        funext a
        have : b.repr (b.equivFun.symm y) a = y a := by
          rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
        simp only [Formalism.HermitianLatticesTheory.vecAt, this, Pi.map_apply]
      rw [← h2, ← h1, ← normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Formalism.HermitianLatticesTheory.fcoord, h3]
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hφ
  have hk := key fun a => ρ (z a)
  simp only [hρρ] at hk
  rw [hk]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => by positivity) fun hs => h0 ?_
  have h4 : (X v)⁻¹.mulVec (fun a => ρ (z a)) = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hs.symm i (Finset.mem_univ i)
    simpa using this
  have h5 : (fun a => ρ (z a)) = 0 := by
    have := congrArg (X v).mulVec h4
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  refine Finset.sum_eq_zero fun a _ => ?_
  have h6 : z a = 0 := by
    rw [← hρρ (z a), show ρ (z a) = 0 from congrFun h5 a, map_zero]
  rw [h6, zero_smul]

theorem ipC_zero_re_pos : ∀ (B : Base) (C : Cols B) (u : B.Word), (∀ φ ψ : (C.mem u).A.Mu0, (C.fm u).ipC 0 ψ φ = star ((C.fm u).ipC 0 φ ψ)) → ∀ φ : (C.mem u).A.Mu0, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re := by
  intro B C u _ φ hφ
  let Q : ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ⋆[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) ((C.fm u).ipC 0)
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  refine re_pos_of_majAt B.embLL ((C.fm u).lat 0).b ((C.fm u).lat 0).X (((C.fm u).lat_good 0).1 _)
    ((C.fm u).emb 0) Q ((C.fm u).emb_norm 0) φ ?_ (fun h => hφ (Subtype.ext h))
  rw [((C.fm u).emb_basis 0).2, (C.fm u).Fi_zero]
  exact φ.2

end GlobalTheory.Mem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMultiplierUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RatPt

variable {D : D7} {S T : HSp D}

theorem exists_fin_add_real (w : WO S T) :
    ∃ u v : WO S T, u.map (infPart D) = 0 ∧ v.map (finPart D) = 0 ∧ w = u + v := by
  let e : AE D := (pairA D.host.F 1 0) ⊗ₜ[D.host.F] (1 : D.host.E)
  have h1 : infPart D e = 1 := rfl
  have h0 : finPart D e = 0 := by
    change (0 : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  refine ⟨Matrix.of fun i j => (1 - e) * w i j, Matrix.of fun i j => e * w i j, ?_, ?_, ?_⟩
  · ext i j
    change infPart D ((1 - e) * w i j) = 0
    rw [RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, sub_self, zero_mul]
  · ext i j
    change finPart D (e * w i j) = 0
    rw [RingHom.map_mul, h0, zero_mul]
  · ext i j
    change w i j = (1 - e) * w i j + e * w i j
    rw [← add_mul, sub_add_cancel, one_mul]

theorem isTheta_heisO {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) : IsThetaFunO ψ S T (heisO ψ S T w f) := by
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_fin_add_real w
  have h : IsThetaFunO ψ S T (heisO ψ S T u (heisO ψ S T v f)) := by
    simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1
      (heisO ψ S T v f) (GlobalTheory.WeilVacMove.isTheta_heisO_real hψ hv hf)
      Unit Finset.univ (fun _ => u) (fun _ => 1) (by intro i hi; exact hu)
  rw [GlobalTheory.WeilVacMove.heisO_heisO, (GlobalTheory.WeilVacMove.symplOH_fin_real S T u v hu hv).1, AddChar.map_zero_eq_one,
    one_smul] at h
  exact h

theorem actO_one (h : GA D T) (w : WO S T) : actO S T 1 h w =
    HMul.hMul (Formalism.L2.Theta.mt T h) (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  rw [inv_one, GlobalTheory.Ker.OmRat.mt_one', Matrix.mul_one]

theorem compAt_mul (θ : InfFam D) (ρ : D.what₂.Tau) {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) :
    compAt θ ρ (x * y : Mx D a c) = compAt θ ρ x * compAt θ ρ y :=
  Matrix.map_mul (f := (θ ρ).comp (infPart D))

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) {a b : ℕ}
    (m : Matrix (Fin a) (Fin b) D.host.E) : compAt θ ρ (m.map (incA D)) = m.map (tauE D ρ) := by
  ext i j
  exact (hθ ρ).1 (m i j)

theorem rational_points : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ δ ∈ GQ T, ∃ ga : GL (Fin r) D.host.E, Formalism.L2.Theta.mt T δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) ∧ IsUn X ga ∧ (∀ Z : Fam T, lact ga (frOf hr eT Z) = frOf hr eT (mvZ θ δ Z)) ∧ (∀ w : WO S T, (GlobalTheory.Ker.IsRealPt w → ∃ w' : WO S T, GlobalTheory.Ker.IsRealPt w' ∧ w = actO S T 1 δ w') ∧ ∀ τ k, rePt θ hr eT (actO S T 1 δ w) τ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ rePt θ hr eT w τ k) ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∀ w, om (1, δ) f (actO S T 1 δ w) = f w := by
  intro D S T r g hr ψ θ X eT bas idx hS δ hδ
  subst hr
  obtain ⟨hψ, hθ, -, -, hM, -, he, -⟩ := hS
  obtain ⟨ga, hga, hδ'⟩ := id hδ
  have hm : Formalism.L2.Theta.mt T δ = (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map (incA D) :=
    (congrArg Units.val hδ').symm
  have hc : ∀ τ : X.Ψ, compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) =
      (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 := fun τ => by
    rw [hm, compAt_rat hθ, ← he, Equiv.apply_symm_apply]
  refine ⟨ga, hm, ?_, fun Z => ?_, fun w => ⟨fun hw => ⟨actO S T 1 δ⁻¹ w, ?_, ?_⟩, fun τ k => ?_⟩, ?_⟩
  · intro x y
    have hG : X.Gm = (-T.gram)ᵀ := hM.1
    rw [hG, GlobalTheory.Ker.Grp.herm_eq, GlobalTheory.Ker.Grp.herm_eq]
    refine GlobalTheory.Ker.Grp.hform_mulVec _ _ _ ?_ _ _
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ga.1 * T.gram * ga.1 = T.gram := hga
    rw [Matrix.mul_neg, Matrix.neg_mul, h]
  · funext τ
    change (ga : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map τ.1 * Z (eT.symm τ) =
      compAt θ (eT.symm τ) (Formalism.L2.Theta.mt T δ) * Z (eT.symm τ)
    rw [hc]
  · unfold GlobalTheory.Ker.IsRealPt at hw ⊢
    rw [GlobalTheory.KerReal.map_actO, hw, Matrix.mul_zero, Matrix.zero_mul]
  · have := GlobalTheory.Ker.OmRat.actO_inv_cancel (1 : GA D S) δ w
    rw [inv_one] at this
    exact this.symm
  · funext a
    change compAt θ (eT.symm τ) (actO S T 1 δ w) a k = _
    rw [actO_one, compAt_mul, hc]
    rfl
  · intro χS χT om H f hf w
    have h1 := H.om_heis 1 δ w f hf
    have h2 := H.om_aut 1 (one_mem _) δ hδ _ (isTheta_heisO hψ hf w)
    rw [← GlobalTheory.Ker.OmRat.heisO_at_zero ψ _ (om (1, δ) f), ← h1]
    exact h2.trans (GlobalTheory.Ker.OmRat.heisO_at_zero _ _ _)

end GlobalTheory.OneMapRef.RatPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenSubgroupFiniteSubset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SmallSub

theorem eq_zero_of_pow_mul {K : Type} [NormedField K] {C : Set K} (hC : IsCompact C) {c x : K} (hc : ‖c‖ < 1)
    (h : ∀ n : ℕ, ∃ u ∈ C, x = c ^ n * u) : x = 0 := by
  obtain ⟨B, hB⟩ := hC.isBounded.exists_norm_le
  have ht : Filter.Tendsto (fun n : ℕ => ‖c‖ ^ n * B) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg c) hc).mul_const B
  refine norm_le_zero_iff.1 (ge_of_tendsto' ht fun n => ?_)
  obtain ⟨u, hu, rfl⟩ := h n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (hB u hu) (by positivity)

theorem finiteAdele_eq_zero (F : Type) [Field F] [NumberField F] {C : Set (Af F)} (hC : IsCompact C) {x : Af F}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change evalV F v x = 0
  have hv : Continuous (evalV F v) := RestrictedProduct.continuous_eval v
  have h1 := (NumberField.FinitePlace.norm_lt_one_iff_mem F v _).2 (Ideal.absNorm_mem v.asIdeal)
  rw [map_natCast, map_natCast] at h1
  have h0 : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero fun e => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 e)
  refine eq_zero_of_pow_mul (hC.image hv) h1 fun n => ?_
  obtain ⟨u, hu, rfl⟩ := h _ (pow_pos h0 n)
  exact ⟨_, ⟨u, hu, rfl⟩, by rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow]⟩

theorem tensor_eq_zero (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {C : Set (Af F ⊗[F] E)} (hC : IsCompact C) {x : Af F ⊗[F] E}
    (h : ∀ M : ℕ, 0 < M → ∃ u ∈ C, x = M • u) : x = 0 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)
  refine b.ext_elem fun i => ?_
  have hc : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap _
  rw [map_zero, Finsupp.zero_apply]
  change b.coord i x = 0
  refine finiteAdele_eq_zero F (hC.image hc) fun M hM => ?_
  obtain ⟨u, hu, rfl⟩ := h M hM
  exact ⟨_, ⟨u, hu, rfl⟩, map_nsmul _ _ _⟩

theorem mem_GinfC_of_cong {D : D7} (V : HSp D) (k : GA D V)
    (h : ∀ n : ℕ, GlobalTheory.Ker.CongK V (GlobalTheory.SW.stdL D.host.E V.rank) n.factorial k) : k ∈ GinfC V := by
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat D.host.F D.host.E (GlobalTheory.SW.stdL D.host.E V.rank)
    (Submodule.fg_span (Set.finite_range _))
  refine Units.ext ?_
  change GlobalTheory.Ker.fmt V k = 1
  ext i j
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun w => by rw [map_one]; exact one_mem _
  have hy : (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D) ∈ GlobalTheory.Ker.hatV (D := D) (GlobalTheory.SW.stdL D.host.E V.rank) := by
    refine AddSubgroup.subset_closure ⟨1, h1, Pi.single j 1, Submodule.subset_span ⟨j, rfl⟩, ?_⟩
    funext a
    by_cases e : a = j
    · subst e
      simp only [Pi.single_eq_same]
      rfl
    · simp [Pi.single_eq_of_ne e]
  have key : (GlobalTheory.Ker.fmt V k *ᵥ Pi.single j 1 - (Pi.single j 1 : Fin V.rank → GlobalTheory.Ker.AfE D)) i = 0 := by
    refine tensor_eq_zero D.host.F D.host.E (hC.image (continuous_apply i)) fun M hM => ?_
    obtain ⟨u, hu, e⟩ := (h M).2 _ hy
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hM le_rfl
    refine ⟨_, ⟨c • u, hLC _ (nsmul_mem hu c), rfl⟩, ?_⟩
    rw [e, hc, mul_smul]
    rfl
  rw [Pi.sub_apply, sub_eq_zero, Matrix.mulVec_single_one] at key
  rw [Matrix.one_apply, ← Pi.single_apply]
  exact key

theorem exists_open_subgroup_finite_subset : ∀ (D : D7) (V : HSp D), ∀ N ∈ 𝓝 (1 : GA D V), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ N := by
  intro D V N hN
  obtain ⟨i0, -, -, i3, -, -, hK⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  choose K hK1 hK2 hK3 _ using fun n : ℕ => hK _ n.factorial hL n.factorial_pos
  have hanti : Antitone fun n => (K n : Set (GA D V)) ∩ GfC V := by
    intro m n hmn k hk
    refine ⟨(hK1 m k).2 ⟨((hK1 n k).1 hk.1).1, fun u hu => ?_⟩, hk.2⟩
    obtain ⟨w, hw, e⟩ := ((hK1 n k).1 hk.1).2 u hu
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hmn
    exact ⟨c • w, nsmul_mem hw c, by rw [e, hc, mul_smul]⟩
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' (U := N) hanti.directed_ge hK3 (fun n => (hK3 n).isClosed)
    (mem_nhdsSet_iff_forall.2 fun x hx => by
      rw [Set.mem_iInter] at hx
      rwa [GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V (hx 0).2 (mem_GinfC_of_cong V x fun n => (hK1 n x).1 (hx n).1)])
  exact ⟨K n, hK2 n, fun k hk hf => hn ⟨hk, hf⟩⟩

end GlobalTheory.Mem.SmallSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDeriv
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightLocallyBounded
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiftHeight

theorem height_locally_bounded : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ g₀ : GA D V,
    ∃ C : ℝ, ∀ᶠ g in 𝓝 g₀, (height θ V g : ℝ) ≤ C := by
  intro D θ hθ V g₀
  obtain ⟨C, hC, h⟩ := GlobalTheory.Grow.height_comparison V hθ
  have hc := (GlobalTheory.Grow.continuous_height V).continuousAt (x := g₀)
  refine ⟨C * (GlobalTheory.Grow.height V g₀ + 1), ?_⟩
  filter_upwards [hc.eventually_lt continuousAt_const (lt_add_one _)] with g hg
  exact (h g).1.trans (mul_le_mul_of_nonneg_left hg.le hC.le)

end GlobalTheory.Mem.LiftHeight

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDeriv
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem IsKerSys.mul_decay_le {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {F : GA D V → ℂ} (hF : IsRapidDecay θ V F) :
    ∃ N : ℕ, ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ g h, ‖κ f g h * F g‖ ≤ C * (height θ W h : ℝ) ^ N := by
  obtain ⟨N, hN⟩ := hκ.growth
  obtain ⟨C', hC'⟩ := hF N
  refine ⟨N, fun f => ?_⟩
  obtain ⟨C, hC⟩ := hN f
  refine ⟨|C| * 2 ^ N * |C'|, by positivity, fun g h => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖κ f g h‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N := by
    have := hκ.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [← this]
    exact (hC _ _).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (NNReal.coe_nonneg _)) N)
      (by positivity) (abs_nonneg _))
  calc ‖κ f g h * F g‖ = ‖κ f g h‖ * ‖F g‖ := norm_mul _ _
    _ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N * ‖F g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖F g‖ * (quotHeight θ V g : ℝ) ^ N) * (height θ W h : ℝ) ^ N := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ |C| * 2 ^ N * |C'| * (height θ W h : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((hC' g).trans (le_abs_self _)) (by positivity))
          (by positivity)

theorem lift_conv_cont_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  intro D θ hθ V W M _ _ κ hκ μ 𝓕 hQ F hF
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have : SecondCountableTopology (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.1
  have : IsTopologicalGroup (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.2.2.2.1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hQ).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨hc, hd⟩ : Continuous F ∧ IsRapidDecay θ V F := hF.2.2 [] (by simp)
  obtain ⟨N, hN⟩ := hκ.mul_decay_le hd
  have hm : ∀ f h, AEStronglyMeasurable (fun g => κ f g h * F g) (μ.restrict 𝓕) := fun f h =>
    (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable
  have hint : ∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ := fun f h => by
    obtain ⟨C, -, hC⟩ := hN f
    exact Measure.integrableOn_of_bounded hfin
      (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable (.of_forall fun g => hC g h)
  have hloc : ∀ f h₀, ∃ B : ℝ, ∀ᶠ h in 𝓝 h₀, ∀ g, ‖κ f g h * F g‖ ≤ B := fun f h₀ => by
    obtain ⟨C, h0, hC⟩ := hN f
    obtain ⟨B, hB⟩ := GlobalTheory.Mem.LiftHeight.height_locally_bounded D θ hθ W h₀
    exact ⟨C * B ^ N, hB.mono fun h hh g => (hC g h).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh N) h0)⟩
  refine ⟨hint, fun f => continuous_iff_continuousAt.2 fun h₀ => ?_, ⟨N, fun f => ?_⟩, fun τ X hX f f' hder h => ?_⟩
  · obtain ⟨B, hB⟩ := hloc f h₀
    exact continuousAt_of_dominated (bound := fun _ => B) (.of_forall (hm f)) (hB.mono fun h hh => .of_forall hh)
      (integrable_const B) (.of_forall fun g =>
        (((hκ.cont f).comp (Continuous.prodMk_right g)).mul continuous_const).continuousAt)
  · obtain ⟨C, -, hC⟩ := hN f
    refine ⟨C * (μ.restrict 𝓕).real Set.univ, fun h => ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall fun g => hC g h)).trans_eq ?_
    ring
  · obtain ⟨B, hB⟩ := hloc f' h
    have hco : Filter.Tendsto (fun t : ℝ => h * oneP θ W τ X t) (𝓝 0) (𝓝 h) := by
      have := (continuous_const (y := h).mul (continuous_oneP hθ hX)).tendsto 0
      rw [Pi.mul_apply, oneP_zero hθ, mul_one] at this
      exact this
    have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
      (F := fun t g => κ f g (h * oneP θ W τ X t) * F g) (F' := fun t g => κ f' g (h * oneP θ W τ X t) * F g)
      (bound := fun _ => B) (hco.eventually hB) (.of_forall fun t => hm f _) (hint f _) (hm f' _)
      (.of_forall fun g t ht => ht g) (integrable_const B)
      (.of_forall fun g t _ => (hasDerivAt_oneP hθ hX (φ := κ f g) (φ' := κ f' g) (hder g) h t).mul_const (F g))).2
    simpa only [oneP_zero hθ, mul_one] using this

end GlobalTheory.Mem.Lift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDerivStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  first | exact @GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv | exact GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv | (intros; apply GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingHomOfIsIntegral
namespace GlobalTheory.RingHomOfIsIntegral

theorem exists_ringHom_of_isIntegral (R : Type) [CommRing R] [CharZero R] [Algebra.IsIntegral ℤ R]
    (l : ℕ) [hl : Fact (Nat.Prime l)] : Nonempty (R →+* AlgebraicClosure (ZMod l)) := by
  have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
  have hlp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R)
    (Ideal.span {(l : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [hinj (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  have := hP
  have hl0 : ((l : ℕ) : R ⧸ P) = 0 := by
    have h1 : (l : ℤ) ∈ P.comap (algebraMap ℤ R) := by
      change (l : ℤ) ∈ Ideal.under ℤ P
      rw [hPc]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa using h1
  have hchar : CharP (R ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  let : Algebra (ZMod l) (R ⧸ P) := ZMod.algebra _ l
  have : Algebra.IsIntegral (ZMod l) (R ⧸ P) := ⟨fun x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ) r).map (Ideal.Quotient.mkₐ ℤ P)).tower_top⟩
  exact ⟨(IsAlgClosed.lift (R := ZMod l) (S := R ⧸ P)
    (M := AlgebraicClosure (ZMod l))).toRingHom.comp (Ideal.Quotient.mk P)⟩

theorem nonempty_ringHom : ∀ (l : ℕ) [Fact (Nat.Prime l)],
    Nonempty (↥(integralClosure ℤ ℂ) →+* Formalism.CyclotomicNorms.Fbar l) := by
  intro l _
  exact exists_ringHom_of_isIntegral (integralClosure ℤ ℂ) l

end GlobalTheory.RingHomOfIsIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwExtend
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.SJ.Place

theorem exists_tw_extend {H K X : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (V : Submodule ℂ X) (φ : V →ₗ⋆[ℂ] K) (z : ℂ) (s : Bool) :
    ∃ sE : Tw s H →ₗ⋆[ℂ] Tw s K, ∀ (x : Tw s H) (hx : e (Tw.out x) ∈ V), sE x = Tw.mk s (z • φ ⟨e (Tw.out x), hx⟩) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V.comap e) (e.restrict (p := V.comap e) (q := V) fun _ h => h)
  refine ⟨{ toFun := fun x => Tw.mk s (z • φ (g (Tw.out x))), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    show z • φ (g (Tw.out x + Tw.out y)) = z • φ (g (Tw.out x)) + z • φ (g (Tw.out y))
    rw [map_add (f := _), map_add (f := _), smul_add]
  · intro a x
    show z • φ (g (cj s a • Tw.out x)) = cj s (starRingEnd ℂ a) • z • φ (g (Tw.out x))
    rw [map_smul, map_smulₛₗ, cj_conj, smul_comm]
  · intro x hx
    have := LinearMap.congr_fun hg ⟨Tw.out x, hx⟩
    show Tw.mk s (z • φ (g (Tw.out x))) = _
    rw [show g (Tw.out x) = ⟨e (Tw.out x), hx⟩ from this]

theorem scale_norm {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {c n a : ℝ} (hc : 0 < c) (hn : 0 < n) (y : K)
    (h : ‖y‖ ^ 2 = c * a) : n * ‖((1 : ℂ) * (((Real.sqrt (c * n))⁻¹ : ℝ) : ℂ)) • y‖ ^ 2 = a := by
  have hcn : 0 < c * n := mul_pos hc hn
  rw [one_mul, norm_smul, Complex.norm_real, mul_pow, h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hcn.le]
  field_simp

theorem sEEofTT_spec {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0)))
    (𝓕 : Set (GA D (D.sp.Y 0))) (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) (h : EvalTieT M μ 𝓕 E X G ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E X G ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re ∧
      ((sEEofTT M μ 𝓕 E X G ι t c T : HHX X) : L2X X) ∈ goodSub X G := by
  have e : sEEofTT M μ 𝓕 E X G ι t c = (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap := by
    unfold sEEofTT
    exact dif_pos h
  have e' : sEEofTT M μ 𝓕 E X G ι t c T = conjHH X G (h.choose_spec.2.choose T) := by
    rw [e]
    rfl
  rw [e']
  refine ⟨?_, (mem_EEC X G _).1 (h.choose_spec.2.choose T).2⟩
  rw [(conjHH X G).norm_map]
  exact (h.choose_spec.2.choose_spec T).2

theorem exists_placement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (ι : GA D (Yc D 0) ≃* St.B.I.GA) (t : GA D (Yc D 0)) (c : ℝ) (s : Bool), R.models_HE → 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c → ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX St)), 0 < κ ∧ ∀ (x : Tw s R.HE.H) (hx : R.HE.e (Tw.out x) ∈ R.EEat (R.levR F true)), sE x = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F true * ‖sE x‖ ^ 2 = ‖x‖ ^ 2 ∧ ((Tw.out (sE x) : HHX St) : L2X St) ∈ goodSub St Gd := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F St Gd ι t c s hE hc h
  have hn : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  obtain ⟨sE, hs⟩ := exists_tw_extend R.HE.e (R.EEat (R.levR F true))
    (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c)
    ((1 : ℂ) * (((Real.sqrt (c * RealDat.nP F true))⁻¹ : ℝ) : ℂ)) s
  refine ⟨(Real.sqrt (c * RealDat.nP F true))⁻¹, sE, inv_pos.2 (Real.sqrt_pos.2 (mul_pos hc hn)), fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := sEEofTT_spec (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c h ⟨R.HE.e (Tw.out x), hx⟩
  refine ⟨hs x hx, ?_, ?_⟩
  · rw [hs x hx]
    have hip : (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2 := by
      rw [← hE.2.2]
      exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (Tw.out x)).symm
    have key := scale_norm (K := HHX St) hc hn
      (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) (h1.trans (congrArg (c * ·) hip))
    exact key
  · rw [hs x hx]
    exact (goodSub St Gd).smul_mem _ h2

end GlobalTheory.Mem.SJ.Place
end
