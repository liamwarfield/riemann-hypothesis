module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotients

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh

namespace GlobalTheory.CompanionTheory.GE

def twSecs {X : Scheme.{0}} (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) {P : X.Modules} (S : Subobject P) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) S.arrow).app ⊤)

def twPow {A : Type} [CommRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))]
    (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (n : ℤ) (P : X.Modules) (m : ℕ) : Set Γ(GlobalTheory.twistZ P H n, ⊤) :=
  ((Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ m) • ⊤ : Submodule Γ(X, ⊤) Γ(GlobalTheory.twistZ P H n, ⊤)) :
    Set Γ(GlobalTheory.twistZ P H n, ⊤))

structure OpSeq {X : Scheme.{0}} (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (d : ℕ) : Prop where
  coherent : ∀ e, IsCoherent (M e)
  comm : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)
  gen : ∀ e, d ≤ e → ∀ U : X.affineOpens,
    Submodule.span Γ(X, U) (⋃ i, Set.range ((T i e).app U)) = ⊤

def GradedNoeth : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (k : ℕ) (M : ℕ → Type)
    [∀ e, AddCommGroup (M e)] [∀ e, Module R (M e)] [∀ e, Module.Finite R (M e)]
    (T : Fin k → ∀ e, M e →ₗ[R] M (e + 1)),
    (∀ i j e x, T j (e + 1) (T i e x) = T i (e + 1) (T j e x)) →
    ∀ d : ℕ, (∀ e, d ≤ e → ⨆ i, LinearMap.range (T i e) = ⊤) →
    ∀ L : ∀ e, Submodule R (M e), (∀ i e, (L e).map (T i e) ≤ L (e + 1)) →
    ∃ d' : ℕ, ∀ e, d' ≤ e → ⨆ i, (L e).map (T i e) = L (e + 1)

def UniformVanishing : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∀ e q, 0 < q → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (M e) H n) q)

def UniformGen : Prop :=
  ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))]
    [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H →
    ∀ (k : ℕ) (M : ℕ → X.Modules) (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ), OpSeq k M T d →
    ∃ n₁ : ℤ, ∀ n, n₁ ≤ n → ∀ e, d ≤ e →
      Submodule.span Γ(X, ⊤)
        (⋃ i, Set.range ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (T i e)).app ⊤)) = ⊤

end GlobalTheory.CompanionTheory.GE
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasis
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL

theorem exists_compact_open_subgroup_subset (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
      IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧
        (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, hJo, hJU, hJK, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, hJo, (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hJo) hJK, hJU⟩

end GlobalTheory.CompanionTheory.SmGL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactOpenSubgroupsBasisStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_open_subgroups_basis : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset | exact GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset | (intros; apply GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

abbrev thC (n : ℕ) : Monoid.End (GL (Fin n) ℂ) := thetaR (starRingEnd ℂ) n

theorem nil_sq_mul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ nilrad W₁ W₂) : X * X * X = 0 := by
  have h : ∀ y, (X * X * X) *ᵥ y = 0 := fun y => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hX.2.2 _ (hX.2.1 _ (hX.1 y))
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

def uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) : GL (Fin n) ℂ where
  val := 1 + X.1
  inv := 1 - X.1 + X.1 * X.1
  val_inv := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp
  inv_val := by
    have h := nil_sq_mul X.2
    noncomm_ring
    rw [← mul_assoc, h]; simp

@[simp] theorem uOf_val {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (X : nilrad W₁ W₂) :
    (uOf X).val = 1 + X.1 := rfl

theorem continuous_uOf {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} :
    Continuous (uOf : nilrad W₁ W₂ → GL (Fin n) ℂ) := by
  have h : Continuous fun X : nilrad W₁ W₂ => X.1 := continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add h
  · have : Continuous fun X : nilrad W₁ W₂ => (1 - X.1 + X.1 * X.1 : Matrix (Fin n) (Fin n) ℂ) :=
      (continuous_const.sub h).add (h.matrix_mul h)
    exact this

def NilChange : Prop := ∀ (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∃ Φ : nilrad W₁ W₂ → nilrad W₁ W₂, Continuous Φ ∧
    (∀ X, uOf (Φ X) = (uOf X)⁻¹ * (d * thC n (uOf X) * d⁻¹)) ∧
    ∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure], ∃ c : NNReal, ν.map Φ = (c : ENNReal) • ν

def QuotVanish : Prop := ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)),
  (d * thC n d).val.charpoly.Separable → W₁ ≠ ⊥ → W₁ ≤ W₂ →
  perpD (starRingEnd ℂ) d W₁ = W₂ → perpD (starRingEnd ℂ) d W₂ = W₁ →
  ∀ F : GL (Fin n) ℂ → ℂ, Measurable F → (∀ t ∈ twCent (thC n) d, ∀ x, F (t * x) = F x) →
    (∀ x k, thC n k = k → F (x * k) = F x) →
    (∀ [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
      [ν.IsAddHaarMeasure] (q : GL (Fin n) ℂ), ∫ X, F (uOf X * q) ∂ν = 0) →
    quotIntegral μ (twCent (thC n) d) μd F = 0

theorem mem_img' (g : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ img g W ↔ (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W := by
  have e1 : ∀ z : Fin n → ℂ, (g⁻¹ : GL (Fin n) ℂ).val *ᵥ (g.val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e2 : ∀ z : Fin n → ℂ, g.val *ᵥ ((g⁻¹ : GL (Fin n) ℂ).val *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, e1]; exact hx
  · intro h
    exact ⟨_, h, by rw [Matrix.toLin'_apply, e2]⟩

theorem img_mul (a b : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    img (a * b) W = img a (img b W) := by
  ext y
  simp only [mem_img', _root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem img_one (W : Submodule ℂ (Fin n → ℂ)) : img (1 : GL (Fin n) ℂ) W = W := by
  ext y
  simp [mem_img']

theorem thC_val (q : GL (Fin n) ℂ) : (thC n q).val = (q⁻¹ : GL (Fin n) ℂ).valᴴ := by
  rw [thC, thetaR_val]; ext i j; simp [Matrix.conjTranspose_apply]

theorem mem_perp' (W : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    y ∈ perp (starRingEnd ℂ) W ↔ ∀ x ∈ W, star x ⬝ᵥ y = 0 := Iff.rfl

theorem perp_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perp (starRingEnd ℂ) (img q W) = img (thC n q) (perp (starRingEnd ℂ) W) := by
  have hi : ((thC n q)⁻¹ : GL (Fin n) ℂ).val = q.valᴴ := by
    rw [← map_inv, thC_val, inv_inv]
  ext y
  rw [mem_img', mem_perp', mem_perp', hi]
  constructor
  · intro h x hx
    have := h (q.val *ᵥ x) ⟨x, hx, by rw [Matrix.toLin'_apply]⟩
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at this
    exact this
  · rintro h _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    exact h x hx

theorem perpD_twConj (d q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perpD (starRingEnd ℂ) (twConj (thC n) q d) (img q⁻¹ W) =
      img q⁻¹ (perpD (starRingEnd ℂ) d W) := by
  rw [perpD, perpD, perp_img, ← img_mul, twConj, map_inv]
  simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [img_mul]

theorem img_le_img (g : GL (Fin n) ℂ) {W W' : Submodule ℂ (Fin n → ℂ)} (h : W ≤ W') :
    img g W ≤ img g W' := Submodule.map_mono h

theorem img_ne_bot (g : GL (Fin n) ℂ) {W : Submodule ℂ (Fin n → ℂ)} (h : W ≠ ⊥) : img g W ≠ ⊥ := by
  intro h0
  apply h
  have : img g⁻¹ (img g W) = W := by rw [← img_mul, inv_mul_cancel, img_one]
  rw [← this, h0]
  exact Submodule.map_bot _

theorem conj_mem (p : GL (Fin n) ℂ) {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) :
    p.val * X * (p⁻¹ : GL (Fin n) ℂ).val ∈ nilrad (img p W₁) (img p W₂) := by
  have hpp : ∀ y : Fin n → ℂ, (p⁻¹ : GL (Fin n) ℂ).val *ᵥ (p.val *ᵥ y) = y := fun z => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp
  have e : ∀ y : Fin n → ℂ, (p.val * X * (p⁻¹ : GL (Fin n) ℂ).val) *ᵥ y =
      p.val *ᵥ (X *ᵥ ((p⁻¹ : GL (Fin n) ℂ).val *ᵥ y)) := fun y => by
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [e, mem_img', hpp]
    exact hX.1 _
  · rw [mem_img'] at hy
    rw [e, mem_img', hpp]
    exact hX.2.1 _ hy
  · rw [mem_img'] at hy
    rw [e, hX.2.2 _ hy, Matrix.mulVec_zero]

theorem img_inv_img (q : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : img q (img q⁻¹ W) = W := by
  rw [← img_mul, mul_inv_cancel, img_one]

def cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) := ⟨(q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val, by
    have := conj_mem q⁻¹ X.2
    rwa [inv_inv] at this⟩

def cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    nilrad W₁ W₂ := ⟨q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val, by
    have := conj_mem q Z.2
    rwa [img_inv_img, img_inv_img] at this⟩

theorem cnF_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (cnF q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem cnB_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    (cnB q W₁ W₂ Z).1 = q.val * Z.1 * (q⁻¹ : GL (Fin n) ℂ).val := rfl

theorem cnF_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X Y : nilrad W₁ W₂) :
    cnF q W₁ W₂ (X + Y) = cnF q W₁ W₂ X + cnF q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnF_val, mul_add, add_mul])

theorem cnB_add (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (X Y : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) :
    cnB q W₁ W₂ (X + Y) = cnB q W₁ W₂ X + cnB q W₁ W₂ Y :=
  Subtype.ext (by
    simp only [Submodule.coe_add, cnB_val, mul_add, add_mul])

theorem cnB_cnF (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    cnB q W₁ W₂ (cnF q W₁ W₂ X) = X :=
  Subtype.ext (by
    have h1 : q.val * (q⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
    rw [cnB_val, cnF_val]
    calc _ = (q.val * (q⁻¹ : GL (Fin n) ℂ).val) * X.1 * (q.val * (q⁻¹ : GL (Fin n) ℂ).val) := by
          simp only [mul_assoc]
      _ = X.1 := by rw [h1]; simp)

theorem cnF_cnB (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (Z : nilrad (img q⁻¹ W₁) (img q⁻¹ W₂)) : cnF q W₁ W₂ (cnB q W₁ W₂ Z) = Z :=
  Subtype.ext (by
    have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
    rw [cnF_val, cnB_val]
    calc _ = ((q⁻¹ : GL (Fin n) ℂ).val * q.val) * Z.1 * ((q⁻¹ : GL (Fin n) ℂ).val * q.val) := by
          simp only [mul_assoc]
      _ = Z.1 := by rw [h1]; simp)

def conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    nilrad W₁ W₂ ≃+ nilrad (img q⁻¹ W₁) (img q⁻¹ W₂) :=
  AddMonoidHom.toAddEquiv (AddMonoidHom.mk' (cnF q W₁ W₂) (cnF_add q W₁ W₂))
    (AddMonoidHom.mk' (cnB q W₁ W₂) (cnB_add q W₁ W₂))
    (AddMonoidHom.ext fun X => cnB_cnF q W₁ W₂ X) (AddMonoidHom.ext fun Z => cnF_cnB q W₁ W₂ Z)
theorem conjNil_val (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    (conjNil q W₁ W₂ X).1 = (q⁻¹ : GL (Fin n) ℂ).val * X.1 * q.val := rfl

theorem continuous_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem continuous_conjNil_symm (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    Continuous (conjNil q W₁ W₂).symm :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem uOf_conjNil (q : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (X : nilrad W₁ W₂) :
    uOf (conjNil q W₁ W₂ X) = q⁻¹ * uOf X * q := by
  apply Units.ext
  have h1 : (q⁻¹ : GL (Fin n) ℂ).val * q.val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, conjNil_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem continuous_thC : Continuous (thC n) := by
  have hv : ∀ h : Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ),
      Continuous fun g : GL (Fin n) ℂ => (g : Matrix (Fin n) (Fin n) ℂ) := id
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : Continuous fun g : GL (Fin n) ℂ => (g⁻¹ : GL (Fin n) ℂ).valᴴ :=
      (Units.continuous_val.comp continuous_inv).matrix_conjTranspose
    exact this.congr fun g => (thC_val g).symm
  · have : Continuous fun g : GL (Fin n) ℂ => (g : GL (Fin n) ℂ).valᴴ :=
      Units.continuous_val.matrix_conjTranspose
    refine this.congr fun g => ?_
    have : (((thC n g)⁻¹ : GL (Fin n) ℂ)).val = g.valᴴ := by
      rw [← map_inv, thC_val, inv_inv]
    exact this.symm

end GlobalTheory.CompanionTheory.LocVan
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrbitFinite
theorem UpperTheory.Reformulated.B.Qf32.orbit_finite :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] {G : Type}
    [inst_2 : Group G] [inst_3 : TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (K : Subgroup G),
    IsCompact (↑K : Set G) →
      ∀ (w : V),
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) w = w} →
          {x : V | ∃ k ∈ K, ((ρ : G → V →ₗ[ℂ] V) k : V → V) w = x}.Finite := by
  intro V _ _ G _ _ _ ρ K hK w hw
  have hloc : IsLocallyConstant (fun g : G => ρ g w) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro k
    refine ⟨(fun g : G => k⁻¹ * g) ⁻¹' {g : G | ρ g w = w},
      hw.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
    intro g hg
    have hg' : ρ (k⁻¹ * g) w = w := hg
    calc ρ g w = ρ (k * (k⁻¹ * g)) w := by rw [mul_inv_cancel_left]
      _ = ρ k (ρ (k⁻¹ * g) w) := by rw [map_mul, Module.End.mul_apply]
      _ = ρ k w := by rw [hg']
  haveI : CompactSpace (K : Set G) := isCompact_iff_compactSpace.mp hK
  have hfin := (hloc.comp_continuous
    (continuous_subtype_val (p := fun g : G => g ∈ (K : Set G)))).range_finite
  refine hfin.subset ?_
  rintro x ⟨k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimple
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnitSemisimple

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_proj_finset (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) (t : Finset V) :
    ∀ v : V, ∃ w ∈ Submodule.span ℂ (t : Set V),
      ∀ s ∈ Submodule.span ℂ (t : Set V), B (v - w) s = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro v
    refine ⟨0, zero_mem _, fun s hs => ?_⟩
    have : s = 0 := by simpa using hs
    simp [this]
  | insert a t _ ih =>
    intro v
    obtain ⟨w₁, hw₁, h₁⟩ := ih v
    obtain ⟨a₁, ha₁, h₂⟩ := ih a
    have hle : Submodule.span ℂ (t : Set V) ≤ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.span_mono (by simp)
    have ha : a ∈ Submodule.span ℂ ((insert a t : Finset V) : Set V) :=
      Submodule.subset_span (by simp)
    obtain ⟨x, hx⟩ : ∃ x, x = a - a₁ := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, u = v - w₁ := ⟨_, rfl⟩
    obtain ⟨c, hcdef⟩ : ∃ c, c = B u x / B x x := ⟨_, rfl⟩
    have hc : B u x = c * B x x := by
      by_cases hx0 : x = 0
      · simp [hx0]
      · have h0 : B x x ≠ 0 := fun h => by simpa [h] using hp x hx0
        rw [hcdef]; field_simp
    refine ⟨w₁ + c • x, ?_, ?_⟩
    · refine add_mem (hle hw₁) (Submodule.smul_mem _ _ ?_)
      rw [hx]; exact sub_mem ha (hle ha₁)
    · intro s hs
      rw [Finset.coe_insert] at hs
      obtain ⟨b, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hs
      have hz' : b • a₁ + z ∈ Submodule.span ℂ (t : Set V) :=
        add_mem (Submodule.smul_mem _ _ ha₁) hz
      have e1 : v - (w₁ + c • x) = u - c • x := by rw [hu]; abel
      have e2 : b • a + z = b • x + (b • a₁ + z) := by rw [hx, smul_sub]; abel
      have k1 : B u (b • a₁ + z) = 0 := by rw [hu]; exact h₁ _ hz'
      have k2 : B x (b • a₁ + z) = 0 := by rw [hx]; exact h₂ _ hz'
      rw [e1, e2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
        (B u).map_add (b • x), (B x).map_add (b • x),
        k1, k2, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hc]
      simp only [smul_eq_mul, add_zero]
      ring

theorem mem_fixed_iff {G : Type} [Group G] (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

theorem orbit_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (K : Subgroup G) (hK : IsCompact (K : Set G)) (w : V)
    (hS : IsOpen {g : G | ρ g w = w}) : {x : V | ∃ k ∈ K, ρ k w = x}.Finite :=
  _root_.UpperTheory.Reformulated.B.Qf32.orbit_finite ρ K hK w hS

theorem orthogonal_of_fixed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (W : Subrepresentation ρ) (u : V) (hu : ∀ k ∈ K, ρ k u = u)
    (huW : ∀ s ∈ W.toSubmodule ⊓ fixed ρ K, B u s = 0)
    (w : V) (hw : w ∈ W.toSubmodule) (hS : IsOpen {g : G | ρ g w = w}) : B u w = 0 := by
  classical
  have hO := orbit_finite ρ K hK w hS
  set O : Finset V := hO.toFinset with hOdef
  have hmem : ∀ x, x ∈ O ↔ ∃ k ∈ K, ρ k w = x := fun x => by simp [hOdef]
  have hinv : ∀ k ∈ K, ∀ x, ρ k⁻¹ (ρ k x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hinv' : ∀ k ∈ K, ∀ x, ρ k (ρ k⁻¹ x) = x := fun k _ x => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hst : ∀ k ∈ K, ∀ x ∈ O, ρ k x ∈ O := by
    intro k hk x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    refine (hmem _).2 ⟨k * l, K.mul_mem hk hl, ?_⟩
    rw [map_mul, Module.End.mul_apply]
  have hsW : ∑ x ∈ O, x ∈ W.toSubmodule := by
    refine Submodule.sum_mem _ fun x hx => ?_
    obtain ⟨l, _, rfl⟩ := (hmem x).1 hx
    exact W.apply_mem_toSubmodule l hw
  have hsF : ∑ x ∈ O, x ∈ fixed ρ K := by
    rw [mem_fixed_iff]
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_nbij' (ρ k) (ρ k⁻¹) (fun x hx => hst k hk x hx)
      (fun x hx => hst _ (K.inv_mem hk) x hx) (fun x _ => hinv k hk x) (fun x _ => hinv' k hk x)
      (fun x _ => rfl)
  have h0 := huW _ ⟨hsW, hsF⟩
  have hterm : ∀ x ∈ O, B u x = B u w := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := (hmem x).1 hx
    conv_lhs => rw [← hu l hl]
    exact hi l u w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl hterm, Finset.sum_const] at h0
  have hne : O.card ≠ 0 := Finset.card_ne_zero.2 ⟨w, (hmem w).2 ⟨1, K.one_mem, by simp⟩⟩
  rw [nsmul_eq_mul] at h0
  exact (mul_eq_zero.1 h0).resolve_left (by exact_mod_cast hne)

def orth {G : Type} [Group G] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hi : ∀ g v w, B (ρ g v) (ρ g w) = B v w) (W : Subrepresentation ρ) : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ w ∈ W.toSubmodule, B v w = 0}
      add_mem' := fun {a b} ha hb w hw => by simp [ha w hw, hb w hw]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c v hv w hw => by simp [hv w hw] }
  apply_mem_toSubmodule := by
    intro g v hv w hw
    have e : ρ g (ρ g⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    have := hv _ (W.apply_mem_toSubmodule g⁻¹ hw)
    rw [← e, hi]; exact this

theorem exists_isCompl : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  intro G V _ _ _ _ _ ρ hbasis hadm hun W
  obtain ⟨B, hh, hp, hi⟩ := hun
  refine ⟨orth ρ B hi W, IsCompl.of_eq ?_ ?_⟩
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_inf]
    refine (Submodule.eq_bot_iff _).2 fun v hv => ?_
    by_contra hv0
    have h0 : B v v = 0 := hv.2 v hv.1
    simpa [h0] using hp v hv0
  · apply Subrepresentation.toSubmodule_injective
    rw [Subrepresentation.toSubmodule_sup]
    refine (Submodule.eq_top_iff').2 fun v => ?_
    obtain ⟨K, hKo, hKc, hKv⟩ := hbasis {g | ρ g v = v} ((hadm.1 v).mem_nhds (by simp))
    have hfd : FiniteDimensional ℂ (fixed ρ K) := hadm.2 K hKo hKc
    have hfd' : FiniteDimensional ℂ (W.toSubmodule ⊓ fixed ρ K : Submodule ℂ V) :=
      Submodule.finiteDimensional_inf_right _ _
    have hfg : (W.toSubmodule ⊓ fixed ρ K).FG := Module.Finite.iff_fg.1 hfd'
    obtain ⟨t, ht⟩ := hfg
    obtain ⟨w, hw, hort⟩ := exists_proj_finset B hp t v
    rw [ht] at hw hort
    have hfix : ∀ k ∈ K, ρ k (v - w) = v - w := by
      intro k hk
      have h1 : ρ k v = v := hKv hk
      have h2 : ρ k w = w := (mem_fixed_iff ρ K w).1 hw.2 k hk
      rw [map_sub, h1, h2]
    have hmem : v - w ∈ (orth ρ B hi W).toSubmodule := fun y hy =>
      orthogonal_of_fixed ρ B hi K hKc W (v - w) hfix hort y hy (hadm.1 y)
    have : v = w + (v - w) := by abel
    rw [this]
    exact Submodule.add_mem_sup hw.1 hmem

end GlobalTheory.CompanionTheory.UnitSemisimple
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitarySemisimpleStatement
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_unitary_semisimple : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → IsAdmissible ρ → IsUnitarisable ρ → ∀ W : Subrepresentation ρ, ∃ W' : Subrepresentation ρ, IsCompl W W' := by
  first | exact @GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | exact GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl | (intros; apply GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivatives
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivatives
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.LimSmooth

theorem tendstoLocallyUniformlyOn_frame {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] {A : ι → Mat n → CLof (Mat n) ℝ} (hA : ∀ p, ContinuousOn (A p) (GLs n))
    {u : ι → ℕ → Mat n → V} {U : ι → Mat n → V}
    (hu : ∀ p, TendstoUniformlyOn (u p) (U p) atTop (GLs n)) :
    TendstoLocallyUniformlyOn
      (fun (k : ℕ) (z : Mat n) => (∑ p, (A p z).smulRight (u p k z) : CLof (Mat n) V))
      (fun z => (∑ p, (A p z).smulRight (U p z) : CLof (Mat n) V)) atTop (GLs n) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set M : ℝ := ∑ p, (‖A p x‖ + 1) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun p _ => by positivity
  have hnear : ∀ᶠ y in 𝓝[GLs n] x, ∀ p, ‖A p y‖ < ‖A p x‖ + 1 := by
    rw [Filter.eventually_all]
    intro p
    exact Filter.Tendsto.eventually_lt_const (lt_add_one _) (hA p x hx).norm
  have hpos : 0 < ε / (M + 1) := by positivity
  refine ⟨{y | ∀ p, ‖A p y‖ < ‖A p x‖ + 1} ∩ GLs n,
    Filter.inter_mem hnear self_mem_nhdsWithin, ?_⟩
  have hev : ∀ᶠ k in atTop, ∀ p, ∀ y ∈ GLs n, dist (U p y) (u p k y) < ε / (M + 1) := by
    rw [Filter.eventually_all]
    intro p
    exact Metric.tendstoUniformlyOn_iff.1 (hu p) _ hpos
  filter_upwards [hev] with k hk y hy
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  have hterm : ∀ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖
      ≤ (‖A p x‖ + 1) * (ε / (M + 1)) := by
    intro p
    have he : (A p y).smulRight (U p y) - (A p y).smulRight (u p k y)
        = (A p y).smulRight (U p y - u p k y) := by
      ext v
      simp [smul_sub]
    rw [he, ContinuousLinearMap.norm_smulRight_apply]
    have h1 := hk p y hy.2
    rw [dist_eq_norm] at h1
    exact mul_le_mul (hy.1 p).le h1.le (norm_nonneg _) (by positivity)
  calc _ ≤ ∑ p, ‖(A p y).smulRight (U p y) - (A p y).smulRight (u p k y)‖ := norm_sum_le _ _
    _ ≤ ∑ p, (‖A p x‖ + 1) * (ε / (M + 1)) := Finset.sum_le_sum fun p _ => hterm p
    _ = M * (ε / (M + 1)) := by rw [Finset.sum_mul]
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

theorem sum_smulRight_apply {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {ι : Type} [Fintype ι] (B : ι → CLof (Mat n) ℝ) (c : ι → V) (v : Mat n) :
    (∑ q, (B q).smulRight (c q) : CLof (Mat n) V) v = ∑ q, B q v • c q := by
  simp

theorem limit_smooth : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) →
    (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) →
    ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V,
      (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧
      ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  intro n V _ _ _ g hg hc
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.derivative_right_basis_expansion n
  have hopen : IsOpen (GLs n) := isOpen_GLs
  let Gf : List (Bool × Fin n × Fin n) → Mat n → V :=
    fun w z => limUnder atTop (fun k => Rw w (g k) z)
  have hpt : ∀ w, ∀ z ∈ GLs n, Tendsto (fun k => Rw w (g k) z) atTop (𝓝 (Gf w z)) := by
    intro w z hz
    have hcs : CauchySeq (fun k => Rw w (g k) z) := (hc w).cauchy_map hz
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
    have he : Gf w z = x := hx.limUnder_eq
    rwa [he]
  have hu : ∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n) := fun w =>
    (hc w).tendstoUniformlyOn_of_tendsto (hpt w)
  have hsm : ∀ k w, ContDiffOn ℝ ∞ (Rw w (g k)) (GLs n) := fun k w =>
    GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' (hg k) w
  have hderiv : ∀ k w, ∀ z ∈ GLs n, fderiv ℝ (Rw w (g k)) z
      = (∑ p, (A p z).smulRight (Rw (p :: w) (g k) z) : CLof (Mat n) V) := by
    intro k w z hz
    exact hA V (fderiv ℝ (Rw w (g k)) z) z hz
  have hhas : ∀ w, ∀ z ∈ GLs n, HasFDerivAt (Gf w)
      (∑ p, (A p z).smulRight (Gf (p :: w) z) : CLof (Mat n) V) z := by
    intro w z hz
    refine hasFDerivAt_of_tendstoLocallyUniformlyOn (f := fun k => Rw w (g k))
      (f' := fun (k : ℕ) (y : Mat n) =>
        (∑ p, (A p y).smulRight (Rw (p :: w) (g k) y) : CLof (Mat n) V))
      (g' := fun y => (∑ p, (A p y).smulRight (Gf (p :: w) y) : CLof (Mat n) V))
      hopen (tendstoLocallyUniformlyOn_frame (u := fun p k => Rw (p :: w) (g k))
        (U := fun p => Gf (p :: w)) (fun p => hAc p |>.continuousOn) (fun p => hu (p :: w)))
      ?_ (hpt w) hz
    intro k y hy
    have hd : DifferentiableAt ℝ (Rw w (g k)) y :=
      ((hsm k w).contDiffAt (hopen.mem_nhds hy)).differentiableAt (by simp)
    have h2 := hd.hasFDerivAt
    rwa [hderiv k w y hy] at h2
  have hRd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Gf w) z = Gf (p :: w) z := by
    intro w p z hz
    have h1 : Rd (bs p) (Gf w) z
        = (∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p) := by
      have h0 := (hhas w z hz).fderiv
      exact congrArg (fun L : CLof (Mat n) V => L (z * bs p)) h0
    have h2 : Tendsto (fun k => Rw (p :: w) (g k) z) atTop
        (𝓝 ((∑ q, (A q z).smulRight (Gf (q :: w) z) : CLof (Mat n) V) (z * bs p))) := by
      have h3 : ∀ k, Rw (p :: w) (g k) z
          = ∑ q, (A q z (z * bs p)) • Rw (q :: w) (g k) z := by
        intro k
        have h4 : Rw (p :: w) (g k) z
            = (∑ q, (A q z).smulRight (Rw (q :: w) (g k) z) : CLof (Mat n) V) (z * bs p) :=
          congrArg (fun L : CLof (Mat n) V => L (z * bs p)) (hderiv k w z hz)
        rw [h4, sum_smulRight_apply]
      rw [sum_smulRight_apply]
      simp only [h3]
      exact tendsto_finsetSum _ fun q _ => (hpt (q :: w) z hz).const_smul _
    rw [h1]
    exact tendsto_nhds_unique h2 (hpt (p :: w) z hz)
  have hfam : ∀ v, ContDiffOn ℝ ∞ (Gf v) (GLs n) :=
    GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) Gf (fun p w => p :: w)
      (fun v z hz => (hhas v z hz).differentiableAt) (fun v p z hz => hRd v p z hz)
  refine ⟨Gf, hu, hfam [], ?_⟩
  intro w
  induction w with
  | nil => intro z _; rfl
  | cons p w ih =>
    intro z hz
    exact (Rd_congr ih (bs p) z hz).trans (hRd w p z hz)

end GlobalTheory.CompanionTheory.PresSobA.LimSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivativesStatement
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_limit_right_derivatives : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) → ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V, (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧ ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth | exact GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth | (intros; apply GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth <;> assumption)
end
end
end
