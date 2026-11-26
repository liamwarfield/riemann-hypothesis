module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsAdelicSplit
public import GroundTheory.HeightsAndTheta.Theta.RealSignature
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Theta.RealPlace
namespace GroundTheory.Heights₂.Theta

open Matrix GroundTheory.Automorphic NumberField NumberField.InfinitePlace.Completion TensorProduct

section QuadComplex

variable {R : Type*} [Field R] (φ : R ≃+* ℝ) {a : R} (ha : φ a < 0)

noncomputable def quadComplexEquiv : QuadraticAlgebra R a 0 ≃+* ℂ where
  toFun z := ⟨φ z.re, φ z.im * Real.sqrt (-φ a)⟩
  invFun c := ⟨φ.symm c.re, φ.symm (c.im / Real.sqrt (-φ a))⟩
  left_inv z := by
    have hs : Real.sqrt (-φ a) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 ha)).ne'
    ext
    · simp
    · simp [hs]
  right_inv c := by
    have hs : Real.sqrt (-φ a) ≠ 0 := (Real.sqrt_pos.2 (neg_pos.2 ha)).ne'
    apply Complex.ext
    · simp
    · simp [hs]
  map_mul' z w := by
    have hsq : Real.sqrt (-φ a) * Real.sqrt (-φ a) = -φ a := Real.mul_self_sqrt (neg_pos.2 ha).le
    apply Complex.ext
    · simp only [QuadraticAlgebra.re_mul, map_add (f := _), map_mul, Complex.mul_re]
      linear_combination (φ z.im * φ w.im) * hsq
    · simp only [QuadraticAlgebra.im_mul, map_add (f := _), map_mul, zero_mul, add_zero,
        Complex.mul_im]
      ring
  map_add' z w := by
    apply Complex.ext
    · simp
    · simp [add_mul]

theorem quadComplexEquiv_apply (z : QuadraticAlgebra R a 0) :
    quadComplexEquiv φ ha z = ⟨φ z.re, φ z.im * Real.sqrt (-φ a)⟩ := rfl

theorem quadComplexEquiv_star (z : QuadraticAlgebra R a 0) :
    quadComplexEquiv φ ha (star z) = starRingEnd ℂ (quadComplexEquiv φ ha z) := by
  apply Complex.ext
  · simp [quadComplexEquiv_apply, QuadraticAlgebra.re_star]
  · simp [quadComplexEquiv_apply, QuadraticAlgebra.im_star]

theorem quadComplexEquiv_algebraMap (r : R) :
    quadComplexEquiv φ ha (algebraMap R (QuadraticAlgebra R a 0) r) = (φ r : ℂ) := by
  apply Complex.ext
  · change φ r = φ r
    rfl
  · change φ 0 * Real.sqrt (-φ a) = 0
    rw [map_zero, zero_mul]

end QuadComplex

section Place

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]

theorem two_ne_zero_of_infinitePlace (w : InfinitePlace K) : (2 : K) ≠ 0 := by
  intro h
  have := congrArg w.embedding h
  rw [map_ofNat, map_zero] at this
  exact two_ne_zero this


omit [Algebra.IsQuadraticExtension K E] in
variable (E) in
def IsNonsplitAt (w : InfinitePlace K) : Prop := IsField (w.Completion ⊗[K] E)


variable (K E) in
noncomputable def quadD (w : InfinitePlace K) : K :=
  (exists_algEquiv_quadraticAlgebra K E (two_ne_zero_of_infinitePlace w)).choose


variable (K E) in
noncomputable def quadPsi (w : InfinitePlace K) : E ≃ₐ[K] QuadraticAlgebra K (quadD K E w) 0 :=
  (exists_algEquiv_quadraticAlgebra K E (two_ne_zero_of_infinitePlace w)).choose_spec.choose

theorem quadPsi_conj (w : InfinitePlace K) (x : E) :
    quadPsi K E w (conj K E x) = star (quadPsi K E w x) :=
  (exists_algEquiv_quadraticAlgebra K E (two_ne_zero_of_infinitePlace w)).choose_spec.choose_spec.2 x

variable {w : InfinitePlace K} (hw : w.IsReal)

noncomputable def realPlaceD : ℝ :=
  ringEquivRealOfIsReal hw (algebraMap K w.Completion (quadD K E w))

noncomputable def realPlaceTensorEquiv :
    w.Completion ⊗[K] E ≃ₐ[w.Completion]
      QuadraticAlgebra w.Completion (algebraMap K w.Completion (quadD K E w)) 0 :=
  tensorQuadEquiv (quadPsi K E w) w.Completion

theorem realPlaceD_neg (hE : IsNonsplitAt E w) : realPlaceD (E := E) hw < 0 := by
  set φ := ringEquivRealOfIsReal hw
  set dw := algebraMap K w.Completion (quadD K E w)
  have hF : IsField (QuadraticAlgebra w.Completion dw 0) :=
    MulEquiv.isField hE (realPlaceTensorEquiv (E := E) (w := w)).symm.toMulEquiv
  by_contra hnn
  push Not at hnn
  set r := φ.symm (Real.sqrt (φ dw))
  have hr : r * r = dw := by
    apply φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact Real.mul_self_sqrt hnn
  set ω : QuadraticAlgebra w.Completion dw 0 := ⟨0, 1⟩
  set c := algebraMap w.Completion (QuadraticAlgebra w.Completion dw 0) r
  have hprod : (ω - c) * (ω + c) = 0 := by
    ext
    · change (0 - r) * (0 + r) + dw * (1 - 0) * (1 + 0) = 0
      rw [← hr]
      ring
    · change (0 - r) * (1 + 0) + (1 - 0) * (0 + r) + 0 * (1 - 0) * (1 + 0) = 0
      ring
  have hne : ω - c ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.im h
    change (1 : w.Completion) - 0 = 0 at this
    exact one_ne_zero (by simpa only [sub_zero] using this)
  have hne' : ω + c ≠ 0 := by
    intro h
    have := congrArg QuadraticAlgebra.im h
    change (1 : w.Completion) + 0 = 0 at this
    exact one_ne_zero (by simpa only [add_zero] using this)
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hne
  apply hne'
  calc ω + c = (y * (ω - c)) * (ω + c) := by rw [mul_comm y, hy, one_mul]
    _ = 0 := by rw [mul_assoc, hprod, mul_zero]


omit [Algebra.IsQuadraticExtension K E] in
theorem isNonsplitAt_of_algEquiv {d : K} (ψ : E ≃ₐ[K] QuadraticAlgebra K d 0)
    (hd : ringEquivRealOfIsReal hw (algebraMap K w.Completion d) < 0) : IsNonsplitAt E w :=
  MulEquiv.isField (MulEquiv.isField (Field.toIsField ℂ) (quadComplexEquiv _ hd).toMulEquiv)
    (tensorQuadEquiv ψ w.Completion).toMulEquiv

theorem isNonsplitAt_iff : IsNonsplitAt E w ↔ realPlaceD (E := E) hw < 0 :=
  ⟨realPlaceD_neg hw, isNonsplitAt_of_algEquiv hw (quadPsi K E w)⟩

end Place

section Phi

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {w : InfinitePlace K} (hw : w.IsReal) (hE : IsNonsplitAt E w)

noncomputable def realPlaceEquiv : w.Completion ⊗[K] E ≃+* ℂ :=
  (realPlaceTensorEquiv (E := E) (w := w)).toRingEquiv.trans
    (quadComplexEquiv (ringEquivRealOfIsReal hw) (realPlaceD_neg hw hE))

theorem realPlaceEquiv_conjBase (z : w.Completion ⊗[K] E) :
    realPlaceEquiv hw hE (conjBase K E w.Completion z) = starRingEnd ℂ (realPlaceEquiv hw hE z) := by
  simp only [realPlaceEquiv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
  rw [realPlaceTensorEquiv, tensorQuadEquiv_conjBase (R := w.Completion) (quadPsi_conj w)]
  exact quadComplexEquiv_star _ _ _

theorem realPlaceEquiv_algebraMap (t : w.Completion) :
    realPlaceEquiv hw hE (algebraMap w.Completion (w.Completion ⊗[K] E) t) =
      (ringEquivRealOfIsReal hw t : ℂ) := by
  simp only [realPlaceEquiv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
  exact quadComplexEquiv_algebraMap _ _ t

theorem realPlaceEquiv_smul (t : w.Completion) (z : w.Completion ⊗[K] E) :
    realPlaceEquiv hw hE (t • z) = (ringEquivRealOfIsReal hw t : ℂ) * realPlaceEquiv hw hE z := by
  rw [Algebra.smul_def, map_mul, realPlaceEquiv_algebraMap]

theorem realPlaceEquiv_symm_ofReal (r : ℝ) :
    (realPlaceEquiv hw hE).symm (r : ℂ) =
      algebraMap w.Completion (w.Completion ⊗[K] E) ((ringEquivRealOfIsReal hw).symm r) := by
  apply (realPlaceEquiv hw hE).injective
  rw [RingEquiv.apply_symm_apply, realPlaceEquiv_algebraMap, RingEquiv.apply_symm_apply]

theorem continuous_ringEquivRealOfIsReal_symm :
    Continuous (ringEquivRealOfIsReal hw).symm :=
  (isometryEquivRealOfIsReal hw).symm.continuous

attribute [local instance] tensorTopology isModuleTopology_tensor isTopologicalRing_tensor

theorem continuous_realPlaceEquiv : Continuous (realPlaceEquiv hw hE) := by
  let φ := ringEquivRealOfIsReal hw
  let : Module w.Completion ℂ := Module.compHom ℂ (φ : w.Completion →+* ℝ)
  have hsmul : ∀ (t : w.Completion) (c : ℂ), t • c = (φ t : ℂ) * c := fun t c => by
    change (φ t : ℝ) • c = _
    rw [Complex.real_smul]
  have : ContinuousSMul w.Completion ℂ := ⟨by
    have : (fun p : w.Completion × ℂ => p.1 • p.2) = fun p => (φ p.1 : ℂ) * p.2 :=
      funext fun p => hsmul p.1 p.2
    rw [this]
    exact (Complex.continuous_ofReal.comp
      ((continuous_ringEquivRealOfIsReal hw).comp continuous_fst)).mul continuous_snd⟩
  let L : (w.Completion ⊗[K] E) →ₗ[w.Completion] ℂ :=
    { toFun := realPlaceEquiv hw hE
      map_add' := map_add _
      map_smul' := fun t z => by
        rw [RingHom.id_apply, hsmul, realPlaceEquiv_smul] }
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_realPlaceEquiv_symm : Continuous (realPlaceEquiv hw hE).symm := by
  let φ := ringEquivRealOfIsReal hw
  let : Module ℝ (w.Completion ⊗[K] E) :=
    Module.compHom _ (φ.symm : ℝ →+* w.Completion)
  have hsmul : ∀ (r : ℝ) (z : w.Completion ⊗[K] E), r • z = φ.symm r • z := fun _ _ => rfl
  have : ContinuousSMul ℝ (w.Completion ⊗[K] E) := ⟨by
    have : (fun p : ℝ × (w.Completion ⊗[K] E) => p.1 • p.2) = fun p => φ.symm p.1 • p.2 :=
      funext fun p => hsmul p.1 p.2
    rw [this]
    exact ((continuous_ringEquivRealOfIsReal_symm hw).comp continuous_fst).smul continuous_snd⟩
  have : T2Space (w.Completion ⊗[K] E) := t2Space_tensor w.Completion
  let L : ℂ →ₗ[ℝ] (w.Completion ⊗[K] E) :=
    { toFun := (realPlaceEquiv hw hE).symm
      map_add' := map_add _
      map_smul' := fun r c => by
        rw [RingHom.id_apply, hsmul, Complex.real_smul, map_mul, realPlaceEquiv_symm_ofReal,
          Algebra.smul_def] }
  exact LinearMap.continuous_of_finiteDimensional L

end Phi

section Unitary

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {w : InfinitePlace K} (hw : w.IsReal) (hE : IsNonsplitAt E w)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

attribute [local instance] tensorTopology isModuleTopology_tensor isTopologicalRing_tensor

variable {H}

end Unitary

section Example

end Example

end GroundTheory.Heights₂.Theta
end

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField NumberField.InfinitePlace GroundTheory.Automorphic GroundTheory.Heights₂.Theta Module Matrix
  Topology TensorProduct NumberField.InfinitePlace.Completion

open scoped NumberField.AdeleRing

noncomputable section

attribute [local instance] tensorTopology isModuleTopology_tensor isTopologicalRing_tensor

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

theorem isNonsplitAt_of_isTotallyComplex (u : InfinitePlace F) : IsNonsplitAt E u := by
  have hu : u.IsReal := IsTotallyReal.isReal u
  rw [isNonsplitAt_iff hu]
  by_contra hnn
  push Not at hnn
  let ρ := ringEquivRealOfIsReal hu
  letI : Algebra u.Completion ℝ := (ρ : u.Completion →+* ℝ).toAlgebra
  have hs : Real.sqrt (ρ (algebraMap F u.Completion (quadD F E u))) *
      Real.sqrt (ρ (algebraMap F u.Completion (quadD F E u))) =
      algebraMap F u.Completion (quadD F E u) • (1 : ℝ) +
        (0 : u.Completion) • Real.sqrt (ρ (algebraMap F u.Completion (quadD F E u))) := by
    have hnn' : 0 ≤ ρ (algebraMap F u.Completion (quadD F E u)) := hnn
    rw [Real.mul_self_sqrt hnn', zero_smul, add_zero, Algebra.smul_def, mul_one]
    rfl
  let f := QuadraticAlgebra.lift ⟨_, hs⟩
  let σ : E →+* ℂ := Complex.ofRealHom.comp ((f : _ →+* ℝ).comp
    ((realPlaceTensorEquiv (E := E) (w := u)).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[F] u.Completion ⊗[F] E).toRingHom))
  apply IsTotallyComplex.complexEmbedding_not_isReal σ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [σ, ComplexEmbedding.conjugate_coe_eq, Complex.conj_ofReal]

def placeEmbedding (u : InfinitePlace F) : E →+* ℂ :=
  (realPlaceEquiv (IsTotallyReal.isReal u)
      (isNonsplitAt_of_isTotallyComplex (E := E) u)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : E →ₐ[F] u.Completion ⊗[F] E).toRingHom

theorem norm_placeEmbedding_algebraMap (u : InfinitePlace F) (x : F) :
    ‖placeEmbedding (E := E) u (algebraMap F E x)‖ = u x := by
  have hu := IsTotallyReal.isReal u
  simp only [placeEmbedding, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.toRingHom_eq_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply F u.Completion (u.Completion ⊗[F] E),
    realPlaceEquiv_algebraMap,
    Complex.norm_real, ringEquivRealOfIsReal_apply]
  have h : extensionEmbeddingOfIsReal hu (algebraMap F u.Completion x) =
      embedding_of_isReal hu x := by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
      Algebra.algebraMap_self_apply]
    simpa using extensionEmbeddingOfIsReal_coe hu (WithAbs.toAbs u.1 x)
  rw [h, norm_embedding_of_isReal hu x]

def placeAbove (u : InfinitePlace F) : InfinitePlace E :=
  InfinitePlace.mk (placeEmbedding u)

theorem comap_placeAbove (u : InfinitePlace F) :
    (placeAbove (E := E) u).comap (algebraMap F E) = u := by
  apply InfinitePlace.ext
  intro x
  rw [placeAbove, comap_mk, InfinitePlace.apply, RingHom.comp_apply]
  exact norm_placeEmbedding_algebraMap u x

theorem placeAbove_injective : Function.Injective (placeAbove (F := F) (E := E)) := by
  intro a b hab
  rw [← comap_placeAbove (E := E) a, ← comap_placeAbove (E := E) b, hab]

theorem card_infinitePlace :
    Fintype.card (InfinitePlace F) = Fintype.card (InfinitePlace E) := by
  have h1 := card_add_two_mul_card_eq_rank F
  have h2 := card_add_two_mul_card_eq_rank E
  have h3 := Module.finrank_mul_finrank ℚ F E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two F E] at h3
  have h4 : nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  have h5 : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  rw [card_eq_nrRealPlaces_add_nrComplexPlaces, card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

def placeAboveEquiv : InfinitePlace F ≃ InfinitePlace E :=
  Equiv.ofBijective placeAbove
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨placeAbove_injective, card_infinitePlace⟩)

theorem placeAboveEquiv_apply (u : InfinitePlace F) :
    placeAboveEquiv (E := E) u = placeAbove u := rfl

theorem exists_completionTensorEquiv (u : InfinitePlace F) :
    ∃ Ψ : u.Completion ⊗[F] E ≃+* ℂ, Continuous Ψ ∧ Continuous Ψ.symm ∧
      (∀ z, Ψ (conjBase F E u.Completion z) = starRingEnd ℂ (Ψ z)) ∧
      ∀ e, Ψ (Algebra.TensorProduct.includeRight e) = (placeAbove u).embedding e := by
  have hu := IsTotallyReal.isReal u
  have hE := isNonsplitAt_of_isTotallyComplex (E := E) u
  rcases embedding_mk_eq (placeEmbedding (E := E) u) with h | h
  · refine ⟨realPlaceEquiv hu hE, continuous_realPlaceEquiv hu hE,
      continuous_realPlaceEquiv_symm hu hE, realPlaceEquiv_conjBase hu hE, fun e => ?_⟩
    rw [placeAbove, h]
    rfl
  · refine ⟨(realPlaceEquiv hu hE).trans (starRingAut : RingAut ℂ), ?_, ?_, fun z => ?_,
      fun e => ?_⟩
    · exact Complex.continuous_conj.comp (continuous_realPlaceEquiv hu hE)
    · refine ((continuous_realPlaceEquiv_symm hu hE).comp Complex.continuous_conj).congr fun z => ?_
      rfl
    · simp [realPlaceEquiv_conjBase]
    · rw [placeAbove, h, ComplexEmbedding.conjugate_coe_eq]
      rfl

def completionTensorEquiv (u : InfinitePlace F) : u.Completion ⊗[F] E ≃+* ℂ :=
  (exists_completionTensorEquiv u).choose

theorem continuous_completionTensorEquiv (u : InfinitePlace F) :
    Continuous (completionTensorEquiv (E := E) u) :=
  (exists_completionTensorEquiv u).choose_spec.1

theorem continuous_completionTensorEquiv_symm (u : InfinitePlace F) :
    Continuous (completionTensorEquiv (E := E) u).symm :=
  (exists_completionTensorEquiv u).choose_spec.2.1

theorem completionTensorEquiv_conjBase (u : InfinitePlace F) (z : u.Completion ⊗[F] E) :
    completionTensorEquiv u (conjBase F E u.Completion z) =
      starRingEnd ℂ (completionTensorEquiv u z) :=
  (exists_completionTensorEquiv u).choose_spec.2.2.1 z

theorem completionTensorEquiv_includeRight (u : InfinitePlace F) (e : E) :
    completionTensorEquiv u (Algebra.TensorProduct.includeRight e) = (placeAbove u).embedding e :=
  (exists_completionTensorEquiv u).choose_spec.2.2.2 e

section Unitary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
def unitaryPointsComplexEquiv {R : Type*} [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (H : Matrix ι ι E) (Ψ : R ⊗[F] E ≃+* ℂ) (hc : Continuous Ψ)
    (hc' : Continuous Ψ.symm) (hs : ∀ z, Ψ (conjBase F E R z) = starRingEnd ℂ (Ψ z))
    {H' : Matrix ι ι ℂ}
    (hH : (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)).map Ψ = H') :
    unitaryPoints F E H R ≃ₜ* unitaryGroupMatrix (starRingEnd ℂ) H' where
  toMulEquiv := unitaryGroupMatrixCongr Ψ hs hH
  continuous_toFun := by
    have hv : Continuous fun g : unitaryPoints F E H R =>
        ((g : GL ι (R ⊗[F] E)) : Matrix ι ι (R ⊗[F] E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have h1 : Continuous fun g : unitaryPoints F E H R =>
        ((g : GL ι (R ⊗[F] E)) : Matrix ι ι (R ⊗[F] E)).map Ψ :=
      hv.matrix_map hc
    have h2 : Continuous fun g : unitaryPoints F E H R =>
        ((((g : GL ι (R ⊗[F] E))⁻¹ : GL ι (R ⊗[F] E))) : Matrix ι ι (R ⊗[F] E)).map Ψ :=
      ((Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_map hc
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _
  continuous_invFun := by
    have h1 : Continuous fun g : unitaryGroupMatrix (starRingEnd ℂ) H' =>
        ((g : GL ι ℂ) : Matrix ι ι ℂ).map Ψ.symm :=
      (Units.continuous_val.comp continuous_subtype_val).matrix_map hc'
    have h2 : Continuous fun g : unitaryGroupMatrix (starRingEnd ℂ) H' =>
        ((((g : GL ι ℂ))⁻¹ : GL ι ℂ) : Matrix ι ι ℂ).map Ψ.symm :=
      (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_map hc'
    exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, h2⟩) _

variable {W : Type*} [AddCommGroup W] [Module E W]

theorem map_completionTensorEquiv_gram (h : HermitianForm F E W) (v : Basis ι E W)
    (u : InfinitePlace F) :
    ((gram h.toSesq v).map (Algebra.TensorProduct.includeRight : E →ₐ[F] u.Completion ⊗[F] E)).map
      (completionTensorEquiv u) = gramAt h v (placeAboveEquiv u) := by
  ext i j
  simp only [Matrix.map_apply, gramAt, placeAboveEquiv_apply]
  exact completionTensorEquiv_includeRight u _

def unitaryPointsPlaceEquiv (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) :
    unitaryPoints F E (gram h.toSesq v) ((placeAboveEquiv (F := F) (E := E)).symm w).Completion ≃ₜ*
      unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w) :=
  unitaryPointsComplexEquiv (gram h.toSesq v)
    (completionTensorEquiv ((placeAboveEquiv (F := F) (E := E)).symm w))
    (continuous_completionTensorEquiv _) (continuous_completionTensorEquiv_symm _)
    (completionTensorEquiv_conjBase _)
    (by rw [map_completionTensorEquiv_gram, Equiv.apply_symm_apply])


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
def piUnitaryEquivArch (h : HermitianForm F E W) (v : Basis ι E W) :
    (∀ w : InfinitePlace E, unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w)) ≃ₜ*
      archUnitary h v where
  toFun g := ⟨fun w => (g w : GL ι ℂ), (Subgroup.mem_pi _).2 fun w _ => (g w).2⟩
  invFun g := fun w => ⟨g.1 w, (Subgroup.mem_pi _).1 g.2 w (Set.mem_univ _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_pi fun w => continuous_subtype_val.comp (continuous_apply w)) _
  continuous_invFun := continuous_pi fun w =>
    Continuous.subtype_mk ((continuous_apply w).comp continuous_subtype_val) _

def piCongrRightEquiv {α : Type*} {X Y : α → Type*} [∀ a, Mul (X a)] [∀ a, Mul (Y a)]
    [∀ a, TopologicalSpace (X a)] [∀ a, TopologicalSpace (Y a)] (f : ∀ a, X a ≃ₜ* Y a) :
    (∀ a, X a) ≃ₜ* ∀ a, Y a where
  toFun g a := f a (g a)
  invFun g a := (f a).symm (g a)
  left_inv g := funext fun a => (f a).symm_apply_apply (g a)
  right_inv g := funext fun a => (f a).apply_symm_apply (g a)
  map_mul' g g' := funext fun a => map_mul (f a) (g a) (g' a)
  continuous_toFun := continuous_pi fun a => (f a).continuous.comp (continuous_apply a)
  continuous_invFun := continuous_pi fun a => (f a).symm.continuous.comp (continuous_apply a)

def piReindexEquiv {α β : Type*} (e : α ≃ β) (Y : β → Type*) [∀ b, Group (Y b)]
    [∀ b, TopologicalSpace (Y b)] : (∀ b, Y b) ≃ₜ* ∀ a, Y (e a) where
  toFun g a := g (e a)
  invFun := Homeomorph.piCongrLeft e
  left_inv g := (Homeomorph.piCongrLeft e).apply_symm_apply g
  right_inv z := (Homeomorph.piCongrLeft e).symm_apply_apply z
  map_mul' _ _ := rfl
  continuous_toFun := (Homeomorph.piCongrLeft e).symm.continuous
  continuous_invFun := (Homeomorph.piCongrLeft e).continuous

def infiniteUnitaryEquiv (h : HermitianForm F E W) (v : Basis ι E W) :
    unitaryPoints F E (gram h.toSesq v) (InfiniteAdeleRing F) ≃ₜ* archUnitary h v :=
  ((unitaryCongr (gram h.toSesq v) (infiniteAdeleRingEquivPi F) (by exact continuous_id)
      (by exact continuous_id)).trans
    ((unitaryPiEquiv F (gram h.toSesq v) (fun u : InfinitePlace F => u.Completion)
      (isUnit_det_gram h v)).trans
    (piReindexEquiv placeAboveEquiv.symm _))).trans
    ((piCongrRightEquiv (unitaryPointsPlaceEquiv h v)).trans (piUnitaryEquivArch h v))

end Unitary

section Compat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module E W]

theorem adeleSplit_hermitianDiagonal_fst (h : HermitianForm F E W) (v : Basis ι E W)
    (γ : h.unitaryGroup) (i j : ι) :
    (((adeleSplit h v (hermitianDiagonal h v γ)).1 : GL ι (InfiniteAdeleRing F ⊗[F] E)) :
      Matrix ι ι (InfiniteAdeleRing F ⊗[F] E)) i j =
      (1 : InfiniteAdeleRing F) ⊗ₜ
        ((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) i j := by
  change tensorMap E
      (AlgHom.fst F (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (tensorMap E (adeleRingEquivProd F : 𝔸[F] →ₐ[F] _) (tensorMap E (Algebra.ofId F 𝔸[F])
      ((Algebra.TensorProduct.lid F E).symm
        (((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) i j)))) = _
  rw [Algebra.TensorProduct.lid_symm_apply, tensorMap_tmul, tensorMap_tmul, tensorMap_tmul, map_one,
    map_one, map_one]

theorem infiniteUnitaryEquiv_hermitianDiagonal (h : HermitianForm F E W) (v : Basis ι E W)
    (γ : h.unitaryGroup) :
    infiniteUnitaryEquiv h v (adeleSplit h v (hermitianDiagonal h v γ)).1 = archEmbed h v γ := by
  apply Subtype.ext
  funext w
  apply Units.ext
  ext i j
  have hx := adeleSplit_hermitianDiagonal_fst h v γ i j
  change completionTensorEquiv ((placeAboveEquiv (F := F) (E := E)).symm w)
      (tensorMap E (Pi.evalAlgHom F (fun u : InfinitePlace F => u.Completion)
          ((placeAboveEquiv (F := F) (E := E)).symm w))
        (tensorMap E (infiniteAdeleRingEquivPi F : InfiniteAdeleRing F →ₐ[F] _)
          ((((adeleSplit h v (hermitianDiagonal h v γ)).1 : GL ι (InfiniteAdeleRing F ⊗[F] E)) :
            Matrix ι ι (InfiniteAdeleRing F ⊗[F] E)) i j))) =
    w.embedding (((unitaryGroupEquivMatrix h v γ : GL ι E) : Matrix ι ι E) i j)
  rw [hx, tensorMap_tmul, tensorMap_tmul, map_one, map_one,
    ← Algebra.TensorProduct.includeRight_apply, completionTensorEquiv_includeRight,
    ← placeAboveEquiv_apply, Equiv.apply_symm_apply]

end Compat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module E W]

theorem ArchimedeanUnitaryEquiv.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchimedeanUnitaryEquiv.Statement h v :=
  ⟨infiniteUnitaryEquiv h v, infiniteUnitaryEquiv_hermitianDiagonal h v⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
