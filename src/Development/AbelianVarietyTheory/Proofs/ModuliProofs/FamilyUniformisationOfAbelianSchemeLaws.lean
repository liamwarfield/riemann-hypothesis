module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRelativeExpOfParts
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicMapModuliLiftsLocallyToPeriods
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDifferentiableOnTransfer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameOfPreconnected
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharAtPoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalPeriodLift
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnComplexExtend
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

noncomputable def complexExtend {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) : ℂ ⊗[ℤ] O →ₐ[ℂ] M :=
  Algebra.TensorProduct.lift (Algebra.ofId ℂ M) f.toIntAlgHom
    (fun x y => Algebra.commute_algebraMap_left x (f y))

theorem complexExtend_tmul {O M : Type} [CommRing O] [Ring M] [Algebra ℂ M]
    (f : O →+* M) (c : ℂ) (a : O) : complexExtend f (c ⊗ₜ a) = c • f a := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.lift_tmul _ _ _ c a

theorem exists_eigen_element (O : Type) [CommRing O] [Module.Finite ℤ O]
    [IsReduced (ℂ ⊗[ℤ] O)] (τ : O →+* ℂ) :
    ∃ e : ℂ ⊗[ℤ] O, complexExtend τ e = 1 ∧ ∀ a : O, ((1 : ℂ) ⊗ₜ[ℤ] a) * e = τ a • e := by
  haveI : IsArtinianRing (ℂ ⊗[ℤ] O) := IsArtinianRing.of_finite ℂ _
  haveI : IsSemisimpleRing (ℂ ⊗[ℤ] O) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  obtain ⟨f, hf, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent
    (RingHom.ker (complexExtend τ))
  have hf0 : complexExtend τ f = 0 := by
    have : f ∈ RingHom.ker (complexExtend τ) := hI ▸ Ideal.mem_span_singleton_self f
    exact this
  refine ⟨1 - f, by simp [hf0], fun a => ?_⟩
  have hk : ((1 : ℂ) ⊗ₜ[ℤ] a) - algebraMap ℂ (ℂ ⊗[ℤ] O) (τ a) ∈
      RingHom.ker (complexExtend τ) := by
    rw [RingHom.mem_ker, map_sub, complexExtend_tmul, AlgHom.commutes]
    simp
  rw [hI, Ideal.mem_span_singleton'] at hk
  obtain ⟨y, hy⟩ := hk
  rw [Algebra.smul_def, ← sub_eq_zero, ← sub_mul, ← hy, _root_.mul_assoc, mul_sub, _root_.mul_one, hf.eq,
    sub_self, mul_zero]

theorem complexExtend_diagonal {O : Type} [CommRing O] {g : ℕ}
    (f : O →+* Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (O →+* ℂ))
    (hf : ∀ a, f a = Matrix.diagonal (fun i => ty i a)) (x : ℂ ⊗[ℤ] O) :
    complexExtend f x = Matrix.diagonal (fun i => complexExtend (ty i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, hf]
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Matrix.diagonal_add]

theorem differentiableOn_complexExtend {O : Type} [CommRing O] {g m : ℕ}
    {B : Set (Fin m → ℂ)} (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ))
    (hF : ∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) (x : ℂ ⊗[ℤ] O) (i j : Fin g) :
    DifferentiableOn ℂ (fun b => complexExtend (F b) x i j) B := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    simp only [complexExtend_tmul, Matrix.smul_apply, smul_eq_mul]
    exact (hF a i j).const_mul c
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.add_apply]
    exact hx.add hy

theorem holomorphic_diagonalisation :
    ∀ (O : Type) [CommRing O] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (O →+* Matrix (Fin g) (Fin g) ℂ)) (ty : Fin g → (O →+* ℂ)), Module.Finite ℤ O → IsReduced (ℂ ⊗[ℤ] O) → IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → (∀ a, F b₀ a = Matrix.diagonal (fun i => ty i a)) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * Matrix.diagonal (fun i => ty i a) := by
  intro O _ g m B b₀ F ty hfin hred hB hb₀ hF hF₀
  choose e he1 he using fun τ => exists_eigen_element O τ
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ :=
    fun b => Matrix.of fun i j => complexExtend (F b) (e (ty j)) i j
  have hd : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := fun i j =>
    differentiableOn_complexExtend F hF _ i j
  have h0 : h b₀ = 1 := by
    ext i j
    simp only [h, Matrix.of_apply, complexExtend_diagonal _ ty hF₀]
    by_cases hij : i = j
    · subst hij; simp [he1]
    · simp [hij]
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hd i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (Continuous.matrix_det continuous_id).comp_continuousOn hc
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h0]⟩,
    Set.inter_subset_left, h0, fun i j => (hd i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  ext i j
  have key := congrArg (fun x => complexExtend (F b) x i j) (he (ty j) a)
  simp only [map_mul, map_smul, complexExtend_tmul, one_smul, Matrix.smul_apply,
    smul_eq_mul] at key
  rw [Matrix.mul_diagonal, mul_comm]
  exact key

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_local_period_lift :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g → ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶ Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀ ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀ 0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range) ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀ a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a))) :=
  fun hT hL => GlobalTheory.T.holomorphic_map_moduli_lifts_locally_to_periods hT hL
    (fun k _ X s hs => let h := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k X s hs; ⟨h.1, fun x => ⟨h.2.1.1 x, h.2.1.2 x⟩, h.2.2⟩)
    obj_isAbelianScheme_dim_rigidified_sym obj_pull RelExp.exists_relative_exp latContinuation
    holomorphic_diagonalisation (torsion_eq_and_weilIs_of_isHolTo hL)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisati
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToModulipointExpOfHolomorphicPeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToPointAndExp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HolPeriods

section Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

def Uniformises (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (D' : Datum H)
    (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) : Prop :=
  y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧
    IsHolTo Set.univ (fun z => (e z).left) ∧
    (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧
    (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))

theorem Uniformises.comp_equiv {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {D' : Datum H}
    {t : D.La →ₗ[𝓞 E] D'.La} {P P' : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ Xo.X}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)} (h : Uniformises Xo σ ty D' t P' y e) (hP : IsPeriod D' ty P)
    (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ a, P' a = k (P a))
    (hlin : ∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i) :
    Uniformises Xo σ ty D' t P y (fun z => e (k z)) := by
  obtain ⟨h1, -, ⟨h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12⟩ := h
  refine ⟨h1, hP, ⟨fun z w => by simp only [map_add (f := _), h3], h4.comp k.surjective, ?_, fun w => ?_, fun v hv => ?_⟩,
    fun z => ?_, fun a z => by simp only [hlin, h9], fun n a a₂ c hn hc => ?_, fun a ha => ?_, fun a => ?_⟩
  · have hd : DifferentiableOn ℂ (fun z => k z) Set.univ :=
      k.toContinuousLinearEquiv.differentiable.differentiableOn
    have := isHolTo_comp h5 isOpen_univ hd (Set.mapsTo_univ _ _)
    exact this
  · simp only [isDerivAt0_comp_equiv (fun z => (e z).left) k]
    exact h6 _
  · simp only [isDerivAt0_comp_equiv (fun z => (e z).left) k]
    obtain ⟨w, hw, hu⟩ := h7 v (by simpa only [map_zero] using hv)
    refine ⟨k.symm w, by simpa only [LinearEquiv.apply_symm_apply] using hw, fun w' hw' => ?_⟩
    rw [← hu _ hw', LinearEquiv.symm_apply_apply]
  · rw [h8]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, k.injective (by rw [← hk, ha])⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hk a⟩
  · simp only [map_smul, ← hk]
    exact h10 n a a₂ c hn hc
  · simp only [map_smul, ← hk]
    exact h11 a ha
  · simp only [map_smul, ← hk]
    exact h12 a

end Pointwise

theorem isHolTo_point_and_exp : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' D''
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (t' : D.La →ₗ[𝓞 E] D''.La) (P : D'.La →+ (Fin g → ℂ)) (P'
    : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)) (e'
    : (Fin g → ℂ) → (Over.mk y' ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧
    ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left)
    ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y' ≫ Xo.s = spMap σ ∧ IsPeriod
    D'' ty P' ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y' ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y' ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P').range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D''.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D''.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P'
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P' (t' a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P' (t' a))) → (y = y' ↔ ∃ (gam : D'.La ≃ₗ[𝓞
    E] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D''.EF (gam a) (gam
    b) = D'.EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), ∃ x, gam (t a) = t' a + l.M • x) ∧ (∀ a, ∃ x, gam (t
    a) = t' a + l.A • x) ∧ ∀ a, P' (gam a) = h (P a))) → (∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g
    : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P
    : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X) (e e' : (Fin g → ℂ) → (Over.mk y ⟶
    Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧
    ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left)
    ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
    (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e
    0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧
    (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂
    : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ)
    / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) → (y ≫ Xo.s = spMap σ ∧ IsPeriod D'
    ty P ∧ ((∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ IsHolTo Set.univ
    (fun z => (e' z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e'
    z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ
    ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left)) ∧
    (∀ z, e' z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a
    : E) * z k) = e' z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e' ((k : ℂ)⁻¹ • P a)) (e' ((k : ℂ)⁻¹ • P
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e' ((l.M : ℂ)⁻¹ • P (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e' ((l.A : ℂ)⁻¹ • P (t a))) → e = e') → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ
    : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA
    l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B
    : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (b₀ : Fin m → ℂ) (P₀ : D'.La →+ (Fin g →
    ℂ)) (e₀ : (Fin g → ℂ) → (Over.mk (y b₀) ⟶
    Xo.univ.t.G)), IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ((y b₀) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty P₀ ∧ ((∀ z w, e₀ (z + w) = e₀ z * e₀ w) ∧ Function.Surjective e₀
    ∧ IsHolTo Set.univ (fun z => (e₀ z).left) ∧ (∀ w, ∃! v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e₀ z).left) w v.left) ∧ (∀ v : epsPt (y
    b₀) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e₀
    0).left → ∃! w, IsDerivAt0 (fun z => (e₀ z).left) w v.left)) ∧ (∀ z, e₀ z = 1 ↔ z ∈ (P₀).range)
    ∧ (∀ (a : 𝓞 E) z, e₀ (fun k => ty k (a : E) * z k) = e₀ z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a
    a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂
    : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e₀ ((k : ℂ)⁻¹ • P₀ a)) (e₀ ((k : ℂ)⁻¹ • P₀
    a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = e₀ ((l.M : ℂ)⁻¹ • P₀ (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = e₀ ((l.A : ℂ)⁻¹ • P₀ (t a))) → ∃ (B' : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ty B' P ∧ IsHolTo (B'
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', ((y b) ≫
    Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧
    Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P₀
    : D.La →+ (Fin g → ℂ)), IsTypeFn H D.p D.q ty → IsPeriod D ty P₀ → ∃ (Z : (D.La →+ (Fin g →
    ℂ)) → (Fin D.dim → ℂ)) (s : Finset D.La) (ε : ℝ), 0 < ε ∧ (∀ (m : ℕ) (B : Set (Fin m → ℂ)) (P
    : (Fin m → ℂ) → (D.La →+ (Fin g →
    ℂ))), IsOpen B → IsHolPeriods D ty B P → (∀ b ∈ B, ∀ x ∈ s, ‖P b x - P₀ x‖ < ε) → DifferentiableOn ℂ (fun b => Z (P
    b)) B) ∧ ∀ P P' : D.La →+ (Fin g →
    ℂ), IsPeriod D ty P → IsPeriod D ty P' → (∀ x ∈ s, ‖P x - P₀ x‖ < ε) → (∀ x ∈ s, ‖P' x - P₀ x‖ < ε) → Z P = Z P' → ∃ h : (Fin
    g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, P' a = h (P a)) ∧ ∀ (a : 𝓞 E) z, h (fun k => ty k (a
    : E) * z k) = fun k => ty k (a : E) * h z k) → (∀ (n : ℕ) (U : Set (Fin n → ℂ)) (f : (Fin n →
    ℂ) → (Fin n →
    ℂ)), IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U → ∀ a ∈ U, Function.Bijective (fderiv ℂ f
    a)) → (∀ (k : Type) [Field k] (σ : k →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp k) (d : ℕ) (y₀
    : Sp ℂ ⟶ X), SmoothOfRelativeDimension d s → y₀ ≫ s = spMap σ → ∃ (B : Set (Fin d → ℂ)) (y
    : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (U : X.Opens) (f : Fin d → Γ(X, U)) (n : ℕ) (r : Fin n → Γ(X,
    U)), IsOpen B ∧ (0
    : Fin d → ℂ) ∈ B ∧ y 0 = y₀ ∧ (∀ b ∈ B, y b ≫ s = spMap σ) ∧ IsHolTo B y ∧ Set.InjOn y B ∧ ⊤ ≤ y₀ ⁻¹ᵁ U ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ U → (∀ i, ‖valAt' x U (r
    i) - valAt' y₀ U (r i)‖ < ε) → x ∈ y '' B) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField
    E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty
    : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D'
    : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+
    (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶
    Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν
    : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n *
    m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n
    : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi *
    Complex.I) * (ν l.A : ℂ) /
    l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧
    IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧
    IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y
    b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y
    b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b)
    0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P
    b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e
    b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c
    : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) /
    k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ •
    (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞
    E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧
    ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B
    ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  intro hUniq hExp hLift hCoord hOpen hChart E _ _ _ H D l Xo σ g ty hpq hσ hty D' t m B P y e hgen hB hP hU
  have hU' : ∀ b ∈ B, Uniformises Xo σ ty D' t (P b) (y b) (e b) := hU
  have uniq : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ Xo.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ Xo.univ.t.G)},
      Uniformises Xo σ ty D' t Q x u → Uniformises Xo σ ty D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) → x = x' := by
    intro Q Q' x x' u u' h h' k hk
    exact (hUniq E H D l Xo σ g ty hpq hσ hty D' D' t t Q Q' x x' u u' h h').2
      ⟨LinearEquiv.refl _ _, k, fun _ _ => rfl, fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, hk⟩
  have expo : ∀ {Q Q' : D'.La →+ (Fin g → ℂ)} {x x' : Sp ℂ ⟶ Xo.X}
      {u : (Fin g → ℂ) → (Over.mk x ⟶ Xo.univ.t.G)} {u' : (Fin g → ℂ) → (Over.mk x' ⟶ Xo.univ.t.G)},
      Uniformises Xo σ ty D' t Q x u → Uniformises Xo σ ty D' t Q' x' u' →
      ∀ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ a, Q' a = k (Q a)) →
      (∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i) →
      ∀ z, (show Sp ℂ ⟶ Xo.univ.t.G.left from (u z).left) = (u' (k z)).left := by
    intro Q Q' x x' u u' h h' k hk hlin z
    obtain rfl := uniq h h' k hk
    have := hExp E H D l Xo σ g ty hpq hσ hty D' t Q x u (fun z => u' (k z)) hgen h
      (h'.comp_equiv h.2.1 k hk hlin)
    rw [this]
  have hdim : D'.dim = D.dim := by simp only [Datum.dim, hgen.1, hgen.2.1]
  have hsm : SmoothOfRelativeDimension D'.dim Xo.s := hdim ▸ Xo.smooth
  have hty' : IsTypeFn H D'.p D'.q ty := by rw [hgen.1, hgen.2.1]; exact hty
  have near : ∀ {n : ℕ} {C : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → (D'.La →+ (Fin g → ℂ))}
      (P₀ : D'.La →+ (Fin g → ℂ)) (s : Finset D'.La) (ε : ℝ), IsOpen C → IsHolPeriods D' ty C R →
      IsOpen {c | c ∈ C ∧ ∀ x ∈ s, ‖R c x - P₀ x‖ < ε} := by
    intro n C R P₀ s ε hC hR
    refine isOpen_iff_mem_nhds.2 fun c hc => ?_
    refine Filter.Eventually.and (hC.mem_nhds hc.1) ((Filter.eventually_all_finset s).2 fun x hx => ?_)
    have : ContinuousAt (fun c => ‖R c x - P₀ x‖) c :=
      (((hR.2 x).continuousOn.continuousAt (hC.mem_nhds hc.1)).sub continuousAt_const).norm
    exact this.eventually_lt continuousAt_const (hc.2 x hx)
  have loc : ∀ b₀ ∈ B, ∃ B' : Set (Fin m → ℂ), b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolTo B' y ∧
      IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
    intro b₀ hb₀
    obtain ⟨C₀, y₁, -, -, -, -, hC₀, h0, hy0, hover, hhol, hinj, -⟩ :=
      hChart (KA l) σ Xo.X Xo.s D'.dim (y b₀) hsm (hU' b₀ hb₀).1
    obtain ⟨e₀, he₀⟩ : ∃ e₀, Uniformises Xo σ ty D' t (P b₀) (y₁ 0) e₀ := by
      rw [hy0]; exact ⟨_, hU' b₀ hb₀⟩
    obtain ⟨C₁, P₁, e₁, hC₁, h01, hsub, hP0, hP₁, he₁, hU₁⟩ :=
      hLift E H D l Xo σ g ty hpq hσ hty D' t D'.dim C₀ y₁ 0 (P b₀) e₀ hC₀ h0 hover hhol he₀
    have hU₁' : ∀ c ∈ C₁, Uniformises Xo σ ty D' t (P₁ c) (y₁ c) (e₁ c) := hU₁
    obtain ⟨Z, s, ε, hε, hZ, hZinj⟩ := hCoord E H D' g ty (P b₀) hty' (hP.1 b₀ hb₀)
    set C₂ := {c | c ∈ C₁ ∧ ∀ x ∈ s, ‖P₁ c x - P b₀ x‖ < ε} with hC₂def
    have hC₂ : IsOpen C₂ := near (P b₀) s ε hC₁ hP₁
    have h02 : (0 : Fin D'.dim → ℂ) ∈ C₂ := ⟨h01, fun x _ => by simpa [hP0] using hε⟩
    have hF : DifferentiableOn ℂ (fun c => Z (P₁ c)) C₂ :=
      hZ _ C₂ P₁ hC₂ ⟨fun c hc => hP₁.1 c hc.1, fun x => (hP₁.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    have hFinj : Set.InjOn (fun c => Z (P₁ c)) C₂ := by
      intro c hc c' hc' hcc
      obtain ⟨k, hk, -⟩ := hZinj _ _ (hP₁.1 c hc.1) (hP₁.1 c' hc'.1) hc.2 hc'.2 hcc
      exact hinj (hsub hc.1) (hsub hc'.1) (uniq (hU₁' c hc.1) (hU₁' c' hc'.1) k hk)
    obtain ⟨W, G, hW, hW0, hG, hGW⟩ :=
      exists_local_section hC₂ hF h02 (hOpen _ C₂ _ hC₂ hF hFinj 0 h02)
    set B₁ := {b | b ∈ B ∧ ∀ x ∈ s, ‖P b x - P b₀ x‖ < ε} with hB₁def
    have hB₁ : IsOpen B₁ := near (P b₀) s ε hB hP
    have hZP : DifferentiableOn ℂ (fun b => Z (P b)) B₁ :=
      hZ _ B₁ P hB₁ ⟨fun c hc => hP.1 c hc.1, fun x => (hP.2 x).mono fun c hc => hc.1⟩ fun c hc => hc.2
    set B₂ := B₁ ∩ (fun b => Z (P b)) ⁻¹' W with hB₂def
    have hB₂ : IsOpen B₂ := hZP.continuousOn.isOpen_inter_preimage hB₁ hW
    have hb₂ : b₀ ∈ B₂ := ⟨⟨hb₀, fun x _ => by simpa using hε⟩, by simpa [hP0] using hW0⟩
    have hβ : DifferentiableOn ℂ (fun b => G (Z (P b))) B₂ :=
      hG.comp (hZP.mono Set.inter_subset_left) fun b hb => hb.2
    have hβC : ∀ b ∈ B₂, G (Z (P b)) ∈ C₂ := fun b hb => (hGW _ hb.2).1
    have hk : ∀ b, ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), b ∈ B₂ → (∀ a, P₁ (G (Z (P b))) a = k (P b a)) ∧
        ∀ (a : 𝓞 E) z, k (fun i => ty i (a : E) * z i) = fun i => ty i (a : E) * k z i := by
      intro b
      by_cases hb : b ∈ B₂
      · obtain ⟨k, hk⟩ := hZinj _ _ (hP.1 b hb.1.1) (hP₁.1 _ (hβC b hb).1) hb.1.2 (hβC b hb).2
          (hGW _ hb.2).2.symm
        exact ⟨k, fun _ => hk⟩
      · exact ⟨LinearEquiv.refl _ _, fun h => absurd h hb⟩
    choose k hk using hk
    obtain ⟨B₃, hB₃, hb₃, hsub₃, hkd⟩ := exists_differentiableOn_transfer (Q := P)
      (Q' := fun b => P₁ (G (Z (P b)))) hB₂ (fun x => (hP.2 x).mono fun b hb => hb.1.1)
      (fun x => (hP₁.2 x).comp hβ fun b hb => (hβC b hb).1) hb₂ (hP.1 b₀ hb₀).2.2.2.1
      (fun b => (k b).toLinearMap) fun b hb x => (hk b hb).1 x
    refine ⟨B₃, hb₃, fun b hb => (hsub₃ hb).1.1, ?_, ?_⟩
    · refine isHolTo_congr (isHolTo_comp hhol hB₃ (hβ.mono hsub₃)
        fun b hb => hsub (hβC b (hsub₃ hb)).1) fun b hb => ?_
      exact uniq (hU' b (hsub₃ hb).1.1) (hU₁' _ (hβC b (hsub₃ hb)).1) (k b) (hk b (hsub₃ hb)).1
    · have hφ : DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (G (Z (P bz.1)), k bz.1 bz.2))
          (B₃ ×ˢ Set.univ) :=
        (hβ.comp differentiableOn_fst fun bz (hbz : bz ∈ B₃ ×ˢ Set.univ) => hsub₃ hbz.1).prodMk hkd
      refine isHolTo_congr (isHolTo_comp he₁ (hB₃.prod isOpen_univ) hφ
        fun bz hbz => ⟨(hβC _ (hsub₃ hbz.1)).1, trivial⟩) fun bz hbz => ?_
      exact expo (hU' _ (hsub₃ hbz.1).1.1) (hU₁' _ (hβC _ (hsub₃ hbz.1)).1) (k bz.1)
        (hk _ (hsub₃ hbz.1)).1 (hk _ (hsub₃ hbz.1)).2 bz.2
  refine ⟨isHolTo_of_local fun b hb => ?_, isHolTo_of_local fun bz hbz => ?_⟩
  · obtain ⟨B', h1, h2, h3, -⟩ := loc b hb
    exact ⟨B', h1, h2, h3⟩
  · obtain ⟨B', h1, h2, -, h4⟩ := loc bz.1 hbz.1
    exact ⟨B' ×ˢ Set.univ, ⟨h1, trivial⟩, Set.prod_mono h2 le_rfl, h4⟩

end GlobalTheory.HolPeriods
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToModulipointExpOfHolomorphicPeriods
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isHolTo_point_and_exp_of_isHolPeriods :
    ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) :=
  fun hθ hL => HolPeriods.isHolTo_point_and_exp (UnifPoint.point_eq_iff_isometry_closed hθ hL) exp_eq_of_periods_of_marking
    (exists_local_period_lift hθ hL) PeriodCoord.exists_period_coordinates InjHol.bijective_fderiv_of_injOn
    SubfieldChart.exists_holomorphic_chart

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToModulipointExpOfHolomorphicPeriodsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolTo_modulipoint_exp_of_holomorphic_periods : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsOpen B → IsHolPeriods D' ty B P → (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → IsHolTo B y ∧ IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) := by
  first | exact @GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods | exact GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods | (intros; apply GlobalTheory.isHolTo_point_and_exp_of_isHolPeriods <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueThetaCharOfUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.existsUnique_thetaChar_of_unif : ThetaUnifAV → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → ∀ b₀ ∈ B, ∃! cc : (Fin g → ℂ) × (Fin g → ℂ), ∃ c₁ c₂, cc = (c₁, c₂) ∧ (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP {b₀} y (fun b z => (e b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) :=
  fun hT hLaws _ _ => GlobalTheory.existsUnique_thetaChar_at_point' hT hLaws
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem exists_thetaFrame_family : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ Xo.univ.t.G)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ b ∈ B, ((y b) ≫ Xo.s = spMap σ ∧ IsPeriod D' ty (P b) ∧ ((∀ z w, (e b) (z + w) = (e b) z * (e b) w) ∧ Function.Surjective (e b) ∧ IsHolTo Set.univ (fun z => ((e b) z).left) ∧ (∀ w, ∃! v : epsPt (y b) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => ((e b) z).left) w v.left) ∧ (∀ v : epsPt (y b) ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = ((e b) 0).left → ∃! w, IsDerivAt0 (fun z => ((e b) z).left) w v.left)) ∧ (∀ z, (e b) z = 1 ↔ z ∈ ((P b)).range) ∧ (∀ (a : 𝓞 E) z, (e b) (fun k => ty k (a : E) * z k) = (e b) z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k ((e b) ((k : ℂ)⁻¹ • (P b) a)) ((e b) ((k : ℂ)⁻¹ • (P b) a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = (e b) ((l.M : ℂ)⁻¹ • (P b) (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = (e b) ((l.A : ℂ)⁻¹ • (P b) (t a)))) → (∀ a b, D'.EF (bas a) (bas b) = sgn * omegaStd a b) → (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k, (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧ (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) → IsOpen B → IsPreconnected B → IsHolPeriods D' ty B P → IsHolTo B y → IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) → ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧ IsThetaFrame Xo.univ.t.PP B y (fun b z => (e b z).left) (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z)) :=
  fun hT hL => ThetaFamily.exists_thetaFrame_of_preconnected hL
    isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field
    obj_isAbelianScheme_dim_rigidified_sym
    (existsUnique_thetaChar_of_unif hT hL obj_pull obj_isAbelianScheme_dim_rigidified_sym)
    (SecFamily.exists_secOn_nonvanishing hL)
    differentiableOn_quotient_of_differentiableOn_slice

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationAtPointClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationAtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PointUnif

theorem exists_uniformisation_at_point : ThetaUnifAV → Out.Laws → (∀ (O : Type) [CommRing O] (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (a : OAct O G) (a' : OAct O G'), IsGrpPullback G' G f φ → (∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (τ : O →+* k) (n : ℕ), LieMult a' x τ n ↔ LieMult a (x ≫ f) τ n) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF → (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) → (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT _ _ hPull hPol hDat E _ _ _ H D l Xo σ g ty _ hσ hty y hy
  let b' : Base l ℂ :=
    { unit := fun n hn => IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')
      ρ := σ (baseKA l).ρ
      ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
      ζ := σ (baseKA l).ζ
      ζ_prim := (baseKA l).ζ_prim.map_of_injective σ.injective }
  obtain ⟨o, ⟨m⟩⟩ := hPull E H D l (KA l) ℂ (baseKA l) b' σ Xo.X (Sp ℂ) Xo.s (𝟙 _) y rfl rfl
    (hy.trans (Category.id_comp _).symm) Xo.univ
  obtain ⟨hab, hsm, hrig, hsym⟩ := hPol E H D l ℂ b' (Sp ℂ) (𝟙 _) o
  obtain ⟨rig, hr⟩ := id hrig
  obtain ⟨u, Hm, χ, Ef, hAH, -, h1, h2, hF, -, hE, hbij, hweil⟩ :=
    hT { A := o.t.G, isAb := hab, g := _, smoothDim := hsm, L := o.t.PP.L, isLB := o.t.PP.isLB, rigid := hrig,
         sym := hsym, ample := o.ample, ktriv := o.ktriv } rig hr
  have hLiso : LBIso o.t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push m.cart (𝟙_ _)
    (weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ Xo.univ.t.PP.isLB o.t.PP.isLB m.cart hLiso _) y (Category.id_comp y)
  have he₀ := isExp_push m.cart u h1 h2 Φ hΦ
  have hker₀ : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep Xo.univ.t.act u.Λ u.discrete hker₀ fun a => by
    obtain ⟨F, hF⟩ := hF (o.t.act.act a) (o.t.act.hom a)
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    rw [hΦ, hF, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc]
    exact congrArg _ (m.act a)
  obtain ⟨hdet, I, hζ, hA, hM⟩ := Xo.univ.geom ℂ y σ hy
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 (hφ.trans hσ.symm))]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 fun h => hφ (h.trans hσ))]
  have he := he₀.comp_equiv h
  have hlin : ∀ (a : 𝓞 E) z, Φ (u.ex (h fun k => ty k (a : E) * z k)) = Φ (u.ex (h z)) ≫ Xo.univ.t.act.act a :=
    fun a z => by rw [← hρ, ← hh, diagRep_apply]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => by
    have := Xo.univ.t.act.hom a
    rw [← hker₀, hρ, (hker₀ x).2 hx, MonObj.one_comp]
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hker : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P.range := fun z => (hker₀ _).trans (hrange z).symm
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  have hweil' : ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P b))))
        (unitOn c) := fun k a b c hk hc => by
    rw [map_smul, map_smul, hP, hP]
    exact hΦW _ _ _ _ (hweil k a b c hk hc)
  obtain ⟨D', ε, hp, hq, hε⟩ := hDat E H u.Λ Ef D.p D.q g ty P Hm' hty hbij
    (adj_of_tateIso Xo.univ.t.PP.isLB he hker hPs hlin hweil' I) hPs hPi hPd hPf hH' hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩
    · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
    · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
    · rw [hε]; exact him _ _
  have hker' : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P'.range := hr' ▸ hker
  have hweil'' : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P' a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P' b))))
        (unitOn c) := fun k a b c hk hc => hweil' k (ε a) (ε b) c hk (by rw [hc, hε])
  obtain ⟨f, ν, f1, f2, f3, f4, f5⟩ := similar_with_multiplier
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I
    (expTateIso he hper hker' hlin hweil'')
  have hM' : 0 < l.M' := Nat.lcm_pos (lt_of_lt_of_le (by norm_num) l.three_le) l.A_pos
  refine ⟨D', f l.M', P', fun z => Φ (u.ex (h z)), ⟨hp, hq, f, ν, f1, f2, f3, ?_, rfl⟩, hy, hper, he, hker', hlin,
    hweil'', fun a ha => (hM a ha).trans (f5 _ _ hM' (Nat.dvd_lcm_left _ _) a),
    fun a => (hA a).trans (f5 _ _ hM' (Nat.dvd_lcm_right _ _) a)⟩
  rw [← hζ, f4 _ l.A_pos]
  exact expNegUnit_zpow_val _ _

end GlobalTheory.PointUnif
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PointUnif

theorem exists_uniformisation_at_point_closed : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') ∧ (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) :=
  fun hT hL => exists_uniformisation_at_point hT hL GlobalTheory.LiePull.lieMult_pull GlobalTheory.obj_pull
    GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym GlobalTheory.PeriodDatum.exists_datum

end GlobalTheory.PointUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_thetaUnif : ThetaUnifAV → Out.Laws → N1c := fun hU hL =>
  GlobalTheory.familyUnif_of_parts GlobalTheory.datum_exists_period
    (GlobalTheory.PointUnif.exists_uniformisation_at_point_closed hU hL) (GlobalTheory.Moduli.exists_point_of_isPeriod hU hL) (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hU hL)
    (GlobalTheory.exists_local_period_lift hU hL) (GlobalTheory.T.isHolTo_modulipoint_exp_of_holomorphic_periods hU hL)
    (GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families GlobalTheory.SubfieldChart.exists_holomorphic_chart)
    (GlobalTheory.exists_thetaFrame_family hU hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUniformisationOfAbelianVarietyUniformisatiStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation : ThetaUnifAV → Out.Laws → N1c := by
  first | exact @GlobalTheory.familyUnif_of_thetaUnif | exact GlobalTheory.familyUnif_of_thetaUnif | (intros; apply GlobalTheory.familyUnif_of_thetaUnif <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_laws : Out.Laws → N1c := by
  intro hL
  have hU : ThetaUnifAV :=
    thetaUnifAV_of_laws (by cases hL; assumption) (by cases hL; assumption) (by cases hL; assumption)
      (by cases hL; assumption) (by cases hL; assumption)
  exact GlobalTheory.T.familyUniformisation_of_abelianVariety_uniformisation hU hL

end GlobalTheory
