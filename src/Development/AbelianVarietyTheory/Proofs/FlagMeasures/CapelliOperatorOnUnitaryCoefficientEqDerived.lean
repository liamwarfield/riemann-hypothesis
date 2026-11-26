module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
open Matrix Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.SmoothVecMod

noncomputable section

namespace GlobalTheory.CapelliCoef

variable {n : ℕ} {ε : Fin n → Bool}

lemma eabV_pair {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (L : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    L (EabV ε a b f g) = EabV ε a b (fun x => L (f x)) g := by
  obtain ⟨h1, h2, -, -⟩ := complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  unfold EabV EcV
  rw [map_add (f := _), map_smul, (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h1 hg).2,
    (rdVPair_of vector_right_derivative_extends n ε E E' L f _ g hf h2 hg).2]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma dsigC_unitM (ab : Fin n × Fin n) (v : H) :
    PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM ab) v = EabV ε ab.1 ab.2 (fun x => σ x v) 1 := by
  simp only [PI.DSInfCharCap.dsigC, PI.DSInfCharCap.unitM, PI.DSInfCharCap.thetaJ, PI.PhMeasCore.dsig,
    EabV, EcV, RdV, cpart1, cpart2, Matrix.one_mul, sub_neg_eq_add, ← sub_eq_add_neg]

def freeAct (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) :
    FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ (smoothVec ε σ) :=
  FreeAlgebra.lift ℂ fun ab => unitAct hσ ab.1 ab.2

lemma dsigCW_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (w : List (Fin n × Fin n)) (v : smoothVec ε σ) :
    PI.DSInfCharCap.dsigCW ε σ (w.map PI.DSInfCharCap.unitM) v =
      ((w.map fun ab => unitAct hσ ab.1 ab.2).prod v : smoothVec ε σ) := by
  induction w with
  | nil => rfl
  | cons ab w ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, PI.DSInfCharCap.dsigCW]
    rw [ih, dsigC_unitM, unitAct_coe]

lemma actU_eq (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (p : FreeAlgebra ℂ (Fin n × Fin n))
    (v : smoothVec ε σ) : PI.DSInfCharCap.actU ε σ p v = (freeAct hσ p v : smoothVec ε σ) := by
  have e : freeAct hσ = (MonoidAlgebra.lift ℂ _ _ (FreeMonoid.lift fun ab => unitAct hσ ab.1 ab.2)).comp
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := Fin n × Fin n)).toAlgHom := by
    ext1
    funext ab
    simp [freeAct, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [e]
  simp only [AlgHom.comp_apply, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, dsigCW_eq hσ, Finsupp.sum,
    LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, FreeMonoid.lift_apply]
  rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def IsCoef (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P : H →L[ℂ] Wp)
    (B : Wq →ₗ[ℂ] smoothVec ε σ) (f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ g, inUJ ε g → ∀ w, f g w = P (σ g (B w))

lemma IsCoef.smooth {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) : SmoothOnGV ε f :=
  smooth_congr (PI.UnitaryGroupMassFormula.CapelliEig.coef_smoothOnGV ε σ P
    (LinearMap.toContinuousLinearMap ((smoothVec ε σ).subtype ∘ₗ B)) fun w => (B w).2)
    fun g hg => ContinuousLinearMap.ext fun w => h g hg w

lemma IsCoef.eab (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (a b : Fin n) :
    IsCoef ε σ P (unitAct hσ a b ∘ₗ B) (EabV ε a b f) := by
  intro g hg w
  have e1 := eabV_pair (ContinuousLinearMap.apply ℂ Wp w) h.smooth a b hg
  simp only [ContinuousLinearMap.apply_apply] at e1
  rw [e1, eabV_congr (fun x hx => h x hx w) a b hg, ← eabV_pair P (B w).2 a b hg, LinearMap.comp_apply,
    unitAct_coe, rep_eabV hσ (B w).2 a b hg]

lemma IsCoef.top (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (u : ℂ) (a b : Fin n) :
    IsCoef ε σ P (freeAct hσ (Tm (PI.DSInfCharCap.Egl n) u a b) ∘ₗ B) (Top (EabV ε) u a b f) := by
  intro g hg w
  have e := h.eab hσ a b g hg w
  have e' := h g hg w
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, PI.DSInfCharCap.Egl, freeAct, Module.algebraMap_end_apply, e', e]
  · simp [Formalism.QuantumDeterminants.Top, Tm, hab, PI.DSInfCharCap.Egl, freeAct, e]

lemma IsCoef.word (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P : H →L[ℂ] Wp} {B : Wq →ₗ[ℂ] smoothVec ε σ}
    {f : Matrix (Fin n) (Fin n) ℂ → (Wq →L[ℂ] Wp)} (h : IsCoef ε σ P B f) (l : List (ℂ × Fin n × Fin n)) :
    IsCoef ε σ P (freeAct hσ (l.map fun q => Tm (PI.DSInfCharCap.Egl n) q.1 q.2.1 q.2.2).prod ∘ₗ B)
      ((l.map fun q => Top (EabV ε) q.1 q.2.1 q.2.2).foldr (fun T h => T h) f) := by
  induction l with
  | nil => simpa [Module.End.one_eq_id] using h
  | cons q l ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, map_mul, Module.End.mul_eq_comp,
      LinearMap.comp_assoc]
    exact ih.top hσ _ _ _

theorem capelli_coef : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  intro n ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hds P Q hQ u g hg w
  have hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := hds.2.2.1
  let B : Wq →ₗ[ℂ] smoothVec ε σ := (Q : Wq →ₗ[ℂ] Hs).codRestrict _ hQ
  have h0 : IsCoef ε σ P B (fun x => P.comp ((σ x).comp Q)) := fun _ _ _ => rfl
  have e : Q w = (B w : Hs) := rfl
  rw [e, actU_eq hσ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [capelli, qdetOp, qminorOp, qdet, qminor, map_sum, map_mul, map_intCast, Finset.sum_apply,
    _root_.sum_apply, LinearMap.sum_apply, Submodule.coe_sum, Pi.smul_apply,
    _root_.smul_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := h0.word hσ (List.ofFn fun k : Fin n => (u - ((k : ℕ) : ℂ), τ k, k)) g hg w
  simp only [List.map_ofFn, Function.comp_def] at h
  simp only [id]
  rw [h]
  simp [Module.End.intCast_apply, ← Int.cast_smul_eq_zsmul ℂ]

end GlobalTheory.CapelliCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerivedStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  first | exact @GlobalTheory.CapelliCoef.capelli_coef | exact GlobalTheory.CapelliCoef.capelli_coef | (intros; apply GlobalTheory.CapelliCoef.capelli_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroups
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem inv_keeps {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hA : ∀ y ∈ V, A *ᵥ y ∈ V) : ∀ y ∈ V, B *ᵥ y ∈ V := by
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by simpa using hA y hy
  have hinj : Function.Injective ((Matrix.toLin' A).restrict hA') := by
    intro x y hxy
    have h1 : A *ᵥ (x : Fin n → ℂ) = A *ᵥ (y : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxy
    have h2 := congrArg (fun z => B *ᵥ z) h1
    simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at h2
    exact Subtype.ext h2
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have h1 : A *ᵥ (x : Fin n → ℂ) = y := by
    simpa using congrArg Subtype.val hx
  rw [← h1, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  exact x.2

variable (ε) in
def leviSub {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := flagM ε W
  one_mem' := by
    intro i y hy
    simpa [uMat_one] using hy
  mul_mem' := by
    intro g h hg hh i y hy
    rw [uMat_mul, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg i _ (hh i y hy).1).1, (hh i _ (hg i y hy).2).2⟩
  inv_mem' := by
    intro g hg i y hy
    refine ⟨inv_keeps (uMat_inv_mul g) (W i) (fun z hz => (hg i z hz).1) y hy,
      inv_keeps (A := (uMat g)ᴴ) ?_ (W i) (fun z hz => (hg i z hz).2) y hy⟩
    rw [← Matrix.conjTranspose_mul, uMat_mul_inv, Matrix.conjTranspose_one]

variable (ε) in
def compactSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := maxK ε
  one_mem' := by
    show (uMat (1 : Formalism.REAL.UJ ε))ᴴ * uMat (1 : Formalism.REAL.UJ ε) = 1
    simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have hh' : (uMat h)ᴴ * uMat h = 1 := hh
    show (uMat (g * h))ᴴ * uMat (g * h) = 1
    rw [uMat_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
      Matrix.one_mul, hh']
  inv_mem' := by
    intro g hg
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have h1 : uMat g⁻¹ = (uMat g)ᴴ := by
      calc uMat g⁻¹ = ((uMat g)ᴴ * uMat g) * uMat g⁻¹ := by rw [hg', Matrix.one_mul]
        _ = (uMat g)ᴴ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
    show (uMat g⁻¹)ᴴ * uMat g⁻¹ = 1
    conv_lhs => enter [1]; rw [h1, Matrix.conjTranspose_conjTranspose]
    exact uMat_mul_inv g

theorem isClosed_flagM {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : IsClosed (flagM ε W) := by
  have h : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp only [flagM, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_mulVec continuous_const)).inter
    ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_conjTranspose.matrix_mulVec continuous_const))

theorem isClosed_maxK : IsClosed (maxK ε) :=
  isClosed_eq (continuous_uMat.matrix_conjTranspose.matrix_mul continuous_uMat) continuous_const

theorem conj_sub (m u : Formalism.REAL.UJ ε) (y : Fin n → ℂ) :
    uMat (m * u * m⁻¹) *ᵥ y - y = uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec y (uMat m) (uMat m⁻¹), uMat_mul_inv, Matrix.one_mulVec,
    uMat_mul, uMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem form_inv (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = star (uMat m *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem conj_mem_flagN {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {m u : Formalism.REAL.UJ ε}
    (hm : m ∈ flagM ε W) (hu : u ∈ flagN ε W) : m * u * m⁻¹ ∈ flagN ε W := by
  have hm' : m⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hm
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [conj_sub]
    exact (hm _ _ (hu.1 i _ (hm' _ y hy).1)).1
  · rw [conj_sub]
    refine (hm _ _ (hu.2 _ fun x hx => ?_)).1
    rw [form_inv]
    exact hy _ (hm _ x hx).1

theorem levi_compact_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)),
    (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧
    (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧
    ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W :=
  fun _ ε _ W => ⟨⟨leviSub ε W, rfl⟩, isClosed_flagM W, ⟨compactSub ε, rfl⟩, isClosed_maxK,
    fun _ hm _ hu => conj_mem_flagN W hm hu⟩

end GlobalTheory.FlagLeviGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroupsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧ (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧ ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.FlagLeviGroup.levi_compact_subgroups | exact GlobalTheory.FlagLeviGroup.levi_compact_subgroups | (intros; apply GlobalTheory.FlagLeviGroup.levi_compact_subgroups <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRank
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

private theorem card_infinitePlace_E_eq_F (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.E) = Fintype.card (InfinitePlace I.F) := by
  have hsurj : Function.Surjective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) :=
    fun v => InfinitePlace.comap_surjective v
  have hinj : Function.Injective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
    intro w₁ w₂ h
    have key : ∀ w : InfinitePlace I.E,
        w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases _root_.GlobalTheory.Count.Test.embedding_cases I w with hw | hw
      · rw [← hw, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← hw, InfinitePlace.mk_embedding]
    rw [key w₁, key w₂]
    simp only at h
    rw [h]
  exact Fintype.card_of_bijective ⟨hinj, hsurj⟩

private theorem card_infinitePlace_F_eq_finrank (I : _root_.Formalism.MainNotions.S.AutInst) :
    Fintype.card (InfinitePlace I.F) = Module.finrank ℚ I.F := by
  haveI := I.cm.totReal
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero] at *
  omega

private theorem one_le_abs_discr_E (I : _root_.Formalism.MainNotions.S.AutInst) : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
  have h := discr_ne_zero I.E
  rw [← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h

theorem _root_.GlobalTheory.FlagMeas.instance_numbers : ∀ I : _root_.Formalism.MainNotions.S.AutInst, _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * _root_.Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, _root_.GlobalTheory.FlagMeas.HasSig I p q → p + q = I.n := by
  intro I
  have hdeg : _root_.Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f _root_.Formalism.HermitianLatticesTheory.fDeg
    rw [card_infinitePlace_E_eq_F, card_infinitePlace_F_eq_finrank]
  have hcardF : Fintype.card (InfinitePlace I.F) = I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact card_infinitePlace_F_eq_finrank I
  have hfpos : 1 ≤ I.f := by
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    exact Module.finrank_pos
  refine ⟨hdeg, ?_, ?_, hfpos, hcardF, ?_⟩
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd _root_.Formalism.HermitianLatticesTheory.vInv
    rw [hdeg]
    unfold _root_.Formalism.MainNotions.S.AutInst.f
    ring
  · unfold _root_.Formalism.MainNotions.S.AutInst.rd
    apply Real.one_le_rpow (one_le_abs_discr_E I)
    positivity
  · intro p q h
    unfold _root_.GlobalTheory.FlagMeas.HasSig at h
    have hne : Nonempty (InfinitePlace I.F) := by
      apply Fintype.card_pos_iff.mp
      omega
    obtain ⟨v⟩ := hne
    obtain ⟨hp, hq⟩ := h v
    rw [← hp, ← hq]
    unfold _root_.Formalism.MainNotions.S.AutInst.pAt _root_.Formalism.MainNotions.S.AutInst.qAt
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin I.n))) (fun a => I.ε v a = true)
    simpa using this

end GlobalTheory.FlagMeas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autInst_degree_rootDiscriminant_rank : ∀ I : AutInst, Formalism.HermitianLatticesTheory.fDeg I.E = I.f ∧ 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd ∧ 1 ≤ I.rd ∧ 1 ≤ I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ ∀ p q, HasSig I p q → p + q = I.n := by
  first | exact @GlobalTheory.FlagMeas.instance_numbers | exact GlobalTheory.FlagMeas.instance_numbers | (intros; apply GlobalTheory.FlagMeas.instance_numbers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.AdelicLattice

theorem adelicLattice_selfDual : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  intro I y
  have hsig : ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) = starRingEnd I.E := by
    ext a
    rfl
  have hdual : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ ∀ z ∈ I.L,
      Formalism.UG.hform ((I.cm.sig : I.E →ₐ[I.F] I.E) : I.E →+* I.E) I.J z x ∈
        (algebraMap (𝓞 I.E) I.E).range := by
    rw [hsig]
    exact I.L_dual

  have hgen : Set.range (fun x : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)) =
      (fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E)) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hLf : ∀ u, u ∈ I.Lf ↔ u ∈ Submodule.span (IntAf I.F I.E)
      ((fun x : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) '' (I.L : Set (Fin I.n → I.E))) := by
    intro u
    show u ∈ Submodule.span _ _ ↔ _
    rw [hgen]
  constructor
  · intro hy y' hy'
    have hy'' := (hLf y').1 hy'
    unfold hAf
    induction hy using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      exact Formalism.UG.P.csDual_span I.cm.sig I.J I.L (x : Fin I.n → I.E) ((hdual _).1 x.2) y' hy''
    | zero =>
      rw [Formalism.UG.P.csScale_hform_zero_right]
      exact zero_mem _
    | add u v _ _ hu hv =>
      rw [Formalism.UG.P.csScale_hform_add_right]
      exact add_mem hu hv
    | smul c v _ hv =>
      rw [Subring.smul_def, Formalism.UG.P.csScale_hform_smul_right]
      exact mul_mem c.2 hv
  · intro h
    have hmem := GlobalTheory.PointLattice.mem_latS_of_integral (F := I.F) I.cm.sig I.J I.L hdual I.L_span y
      (fun w hw => h w ((hLf w).2 hw))
    exact (hLf y).2 hmem

end GlobalTheory.AdelicLattice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitianStatement
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_selfDual_hermitian : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  first | exact @GlobalTheory.AdelicLattice.adelicLattice_selfDual | exact GlobalTheory.AdelicLattice.adelicLattice_selfDual | (intros; apply GlobalTheory.AdelicLattice.adelicLattice_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

def lev (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def wC (k r : ℕ) : Mat k r := bigCell k r (fun _ => 1) 1

def torD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal fun i =>
  if h : i.val < r then x ⟨i.val, h⟩
  else if h' : r + k < i.val then -star (x ⟨2 * r + k - i.val, by omega⟩) else 0

def um {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X : lieE S) : Matrix (Fin m) (Fin m) ℂ :=
  unrealify (X : EuclideanSpace ℝ (Fin m × Fin m × Bool))

abbrev EE (k r : ℕ) : Type :=
  (lieE (Nset k r) × lieE (Nset k r)) × ((Fin r → ℂ) × lieE (Formalism.FourierDecayAlt.B2.UWb k r))

def chart (k r : ℕ) (v : EE k r) : Mat k r :=
  wC k r * (NormedSpace.exp (-um v.1.1) * bigCell k r (fun a => 1 + v.2.1 a) 1 * NormedSpace.exp (um v.2.2) *
    NormedSpace.exp (um v.1.2))

def dchart (k r : ℕ) (v : EE k r) : Mat k r :=
  -(wC k r * um v.1.1 * wC k r) + torD k r v.2.1 + um v.2.2 + um v.1.2

end GlobalTheory.CellDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.UnipRad

variable {n : ℕ} {ε : Fin n → Bool}

private lemma uMat_mul' (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

private lemma uMat_one' : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

private lemma inv_mulVec_mulVec (g : Formalism.REAL.UJ ε) (y : Fin n → ℂ) : uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← uMat_mul', inv_mul_cancel, uMat_one', Matrix.one_mulVec]

lemma inv_keeps (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ V, uMat g *ᵥ y ∈ V) :
    ∀ y ∈ V, uMat g⁻¹ *ᵥ y ∈ V := by
  intro y hy
  have h' : ∀ y ∈ V, Matrix.toLin' (uMat g) y ∈ V := fun y hy => by simpa using h y hy
  have hinj : Function.Injective ((Matrix.toLin' (uMat g)).restrict h') := by
    intro x z hxz
    have h1 : uMat g *ᵥ (x : Fin n → ℂ) = uMat g *ᵥ (z : Fin n → ℂ) := by
      simpa using congrArg Subtype.val hxz
    apply Subtype.ext
    rw [← inv_mulVec_mulVec g x, h1, inv_mulVec_mulVec]
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨y, hy⟩
  have h1 : uMat g *ᵥ (x : Fin n → ℂ) = y := by simpa using congrArg Subtype.val hx
  rw [← h1, inv_mulVec_mulVec]
  exact x.2

lemma keeps {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    (u : Formalism.REAL.UJ ε) (hu : u ∈ flagN ε W) (i : Fin (a + 1)) : ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  intro y hy
  induction i using Fin.cases with
  | zero =>
    rw [hW.1] at hy ⊢
    rw [(Submodule.mem_bot ℂ).mp hy]
    simp
  | succ i =>
    have h1 := hW.2.1 (Fin.castSucc_le_succ i) (hu.1 i y hy)
    simpa using (W i.succ).add_mem h1 hy

private lemma step_mul (g h : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) (h2 : uMat h *ᵥ y - y ∈ V) :
    uMat (g * h) *ᵥ y - y ∈ V := by
  have := V.add_mem (hk _ h2) h1
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← uMat_mul'] at this
  simpa using this

private lemma step_inv (g : Formalism.REAL.UJ ε) (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ)
    (hk : ∀ y ∈ V, uMat g *ᵥ y ∈ V) (h1 : uMat g *ᵥ y - y ∈ V) :
    uMat g⁻¹ *ᵥ y - y ∈ V := by
  have := V.neg_mem (inv_keeps g V hk _ h1)
  rw [Matrix.mulVec_sub, inv_mulVec_mulVec] at this
  simpa using this

private lemma closed_step (V : Submodule ℂ (Fin n → ℂ)) (y : Fin n → ℂ) :
    IsClosed {g : Formalism.REAL.UJ ε | uMat g *ᵥ y - y ∈ V} := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g :=
    Units.continuous_val.comp continuous_subtype_val
  exact V.closed_of_finiteDimensional.preimage
    ((hc.matrix_mulVec continuous_const).sub continuous_const)

theorem flagN_subgroup_closed_keeps (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (hW : IsIsoFlag ε j W) :
    (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧
      ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  refine ⟨⟨{ carrier := flagN ε W, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩, ?_,
    fun u hu i => keeps hW u hu i⟩
  · intro g h hg hh
    exact ⟨fun i y hy => step_mul g h _ y (keeps hW g hg _) (hg.1 i y hy) (hh.1 i y hy),
      fun y hy => step_mul g h _ y (keeps hW g hg _) (hg.2 y hy) (hh.2 y hy)⟩
  · refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
    · rw [uMat_one', Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
  · intro g hg
    exact ⟨fun i y hy => step_inv g _ y (keeps hW g hg _) (hg.1 i y hy),
      fun y hy => step_inv g _ y (keeps hW g hg _) (hg.2 y hy)⟩
  · unfold flagN
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => closed_step _ y)

end GlobalTheory.FlagMeas.UnipRad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeepsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_closed_subgroup_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧ ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  first | exact @GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | exact GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | (intros; apply GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheorem
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ClosedMatGroup

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem pow_mem_of_mul {S : Set 𝔸} (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) {a : 𝔸} (ha : a ∈ S) (n : ℕ) :
    a ^ n ∈ S := by
  induction n with
  | zero => simpa using h1
  | succ n ih => rw [pow_succ]; exact hm _ ih _ ha

def lieSub (S : Set 𝔸) (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : Submodule ℝ 𝔸 where
  carrier := {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ S}
  zero_mem' := by intro t; simpa [NormedSpace.exp_zero] using h1
  add_mem' := by
    intro X Y hX hY t
    rw [smul_add]
    refine hc.mem_of_tendsto (Formalism.FourierDecayAlt.P.GroupGeneratedByExp.trotter (t • X) (t • Y)) (Eventually.of_forall fun n => ?_)
    refine pow_mem_of_mul h1 hm (hm _ ?_ _ ?_) n
    · rw [smul_smul]; exact hX _
    · rw [smul_smul]; exact hY _
  smul_mem' := by
    intro c X hX t
    rw [smul_smul]; exact hX _

theorem exp_smul_mem_of_tendsto {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S) {y : ℕ → 𝔸} {u : 𝔸}
    (hy0 : Tendsto y atTop (𝓝 0)) (hne : ∀ n, y n ≠ 0) (hS : ∀ n, NormedSpace.exp (y n) ∈ S)
    (hu : Tendsto (fun n => ‖y n‖⁻¹ • y n) atTop (𝓝 u)) (t : ℝ) : NormedSpace.exp (t • u) ∈ S := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have key : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • u) ∈ S := by
    intro t ht
    have hpos : ∀ n, 0 < ‖y n‖ := fun n => norm_pos_iff.2 (hne n)
    have hn0 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using hy0.norm
    have hk : Tendsto (fun n => ((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) atTop (𝓝 t) := by
      have hl : Tendsto (fun n => t - ‖y n‖) atTop (𝓝 t) := by simpa using hn0.const_sub t
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds (fun n => ?_) (fun n => ?_)
      · have h := (Nat.lt_floor_add_one (t / ‖y n‖)).le
        rw [div_le_iff₀ (hpos n)] at h
        show t - ‖y n‖ ≤ _
        nlinarith
      · have h := Nat.floor_le (div_nonneg ht (hpos n).le)
        rw [le_div_iff₀ (hpos n)] at h
        exact h
    have hlim := (NormedSpace.exp_continuous.tendsto _).comp (hk.smul hu)
    refine hc.mem_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have e : (((⌊t / ‖y n‖⌋₊ : ℕ) : ℝ) * ‖y n‖) • ‖y n‖⁻¹ • y n = (⌊t / ‖y n‖⌋₊ : ℕ) • y n := by
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hpos n).ne', mul_one, Nat.cast_smul_eq_nsmul]
    simp only [Function.comp]
    rw [e, NormedSpace.exp_nsmul]
    exact pow_mem_of_mul h1 hm (hS n) _
  rcases le_total 0 t with ht | ht
  · exact key t ht
  · have := hi _ (key (-t) (by linarith))
    rwa [neg_smul, neg_neg] at this

theorem eventually_eq_zero [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {W : Submodule ℝ 𝔸} (hW : Disjoint (lieSub S hc h1 hm) W) :
    ∀ᶠ y in 𝓝 (0 : 𝔸), y ∈ W → NormedSpace.exp y ∈ S → y = 0 := by
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨y, hy0, hy⟩ := exists_seq_forall_of_frequently hcon
  push_neg at hy
  haveI : ProperSpace 𝔸 := FiniteDimensional.proper ℝ 𝔸
  have hsph : ∀ n, ‖y n‖⁻¹ • y n ∈ Metric.sphere (0 : 𝔸) 1 := fun n => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 (hy n).2.2)]
  obtain ⟨u, hu1, φ, hφ, hu⟩ := (isCompact_sphere (0 : 𝔸) 1).tendsto_subseq hsph
  have huL : u ∈ lieSub S hc h1 hm :=
    exp_smul_mem_of_tendsto hc h1 hm hi (y := y ∘ φ) (hy0.comp hφ.tendsto_atTop) (fun n => (hy _).2.2)
      (fun n => (hy _).2.1) hu
  have huW : u ∈ W :=
    W.closed_of_finiteDimensional.mem_of_tendsto hu (Eventually.of_forall fun n => W.smul_mem _ (hy _).1)
  have h0 : u = 0 := (Submodule.disjoint_def.1 hW) u huL huW
  rw [h0] at hu1
  simp at hu1

theorem map_exp_mul_exp (p : 𝔸 →L[ℝ] 𝔸) :
    map (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z)) (𝓝 0) = 𝓝 (1 : 𝔸) := by
  have hexp : HasStrictFDerivAt NormedSpace.exp (1 : 𝔸 →L[ℝ] 𝔸) (0 : 𝔸) := hasStrictFDerivAt_exp_zero
  have h1 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z)) ((1 : 𝔸 →L[ℝ] 𝔸).comp p) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (by rw [map_zero]; exact hexp) p.hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun z => NormedSpace.exp (z - p z))
      ((1 : 𝔸 →L[ℝ] 𝔸).comp (ContinuousLinearMap.id ℝ 𝔸 - p)) 0 :=
    HasStrictFDerivAt.comp (0 : 𝔸) (f := fun z => z - p z) (by rw [map_zero, sub_zero]; exact hexp)
      (ContinuousLinearMap.id ℝ 𝔸 - p).hasStrictFDerivAt
  have h3 := h1.mul' h2
  have h4 : HasStrictFDerivAt (fun z => NormedSpace.exp (p z) * NormedSpace.exp (z - p z))
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
    refine h3.congr_fderiv ?_
    ext z
    simp [NormedSpace.exp_zero]
  have h5 := h4.map_nhds_eq_of_equiv
  simpa [NormedSpace.exp_zero] using h5

theorem eventually_exists_exp [FiniteDimensional ℝ 𝔸] {S : Set 𝔸} (hc : IsClosed S) (h1 : (1 : 𝔸) ∈ S)
    (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ Z : 𝔸, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S)
    {U : Set 𝔸} (hU : U ∈ 𝓝 (0 : 𝔸)) :
    ∀ᶠ g in 𝓝 (1 : 𝔸), g ∈ S → ∃ X ∈ U, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ S) ∧ NormedSpace.exp X = g := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨W, hW⟩ := (lieSub S hc h1 hm).exists_isCompl
  let p : 𝔸 →L[ℝ] 𝔸 := LinearMap.toContinuousLinearMap ((lieSub S hc h1 hm).projection W hW)
  have hpL : ∀ z, p z ∈ lieSub S hc h1 hm := fun z => Submodule.projection_apply_mem hW z
  have hqW : ∀ z, z - p z ∈ W := fun z => by
    have h := Submodule.projection_add_projection_eq_self hW z
    have e : z - p z = W.projection _ hW.symm z := by
      rw [sub_eq_iff_eq_add']; exact h.symm
    rw [e]; exact Submodule.projection_apply_mem hW.symm z
  rw [← map_exp_mul_exp p, eventually_map]
  have hp0 : Tendsto p (𝓝 0) (𝓝 0) := by simpa using p.continuous.tendsto 0
  have hq0 : Tendsto (fun z => z - p z) (𝓝 0) (𝓝 (0 : 𝔸)) := by simpa using (tendsto_id (x := 𝓝 (0 : 𝔸))).sub hp0
  filter_upwards [hp0.eventually hU, hq0.eventually (eventually_eq_zero hc h1 hm hi hW.disjoint)] with z hz1 hz2 hg
  have hneg : NormedSpace.exp (-p z) ∈ S := by simpa using hpL z (-1)
  have hq : NormedSpace.exp (z - p z) ∈ S := by
    have h := hm _ hneg _ hg
    rwa [← mul_assoc, ← NormedSpace.exp_add_of_commute (Commute.refl (p z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero, one_mul] at h
  refine ⟨p z, hz1, hpL z, ?_⟩
  rw [hz2 (hqW z) hq, NormedSpace.exp_zero, mul_one]

end Banach

theorem unrealify_realify {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

theorem unrealify_mem_lieOf {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    {x : EuclideanSpace ℝ (Fin m × Fin m × Bool)} (hx : x ∈ lieE S) : unrealify x ∈ lieOf S := by
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have hL : ∀ X, X ∈ lieOf S ↔ X ∈ lieSub S hS.1 hS.2.1 hS.2.2.1 := fun X => by
    simp only [lieOf, Set.mem_setOf_eq, Complex.coe_smul]; rfl
  rw [hL]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨X, hX, rfl⟩ := hx
    rw [unrealify_realify]; exact (hL X).1 hX
  | zero =>
    have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have e : unrealify (x + y) = unrealify x + unrealify y := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have e : unrealify (c • x) = c • unrealify x := by
      ext i j; apply Complex.ext <;> simp [unrealify]
    rw [e]; exact Submodule.smul_mem _ _ hx

theorem eventually_exists_exp_matrix {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (hS : PI.IsMatGroup S)
    {U : Set (Matrix (Fin m) (Fin m) ℂ)} (hU : U ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) ℂ)) :
    ∀ᶠ g in 𝓝 (1 : Matrix (Fin m) (Fin m) ℂ), g ∈ S → ∃ X ∈ U, X ∈ lieOf S ∧ NormedSpace.exp X = g := by
  have hi : ∀ Z : Matrix (Fin m) (Fin m) ℂ, NormedSpace.exp Z ∈ S → NormedSpace.exp (-Z) ∈ S := fun Z hZ => by
    rw [Matrix.exp_neg]; exact (hS.2.2.2 _ hZ).1
  let _ := Matrix.linftyOpNormedRing (n := Fin m) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin m) (α := ℂ)
  have hc : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  have h := eventually_exists_exp hS.1 hS.2.1 hS.2.2.1 hi hU
  simp only [lieOf, Set.mem_setOf_eq, Complex.coe_smul]
  exact h

theorem closed_subgroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  intro m S hS
  refine ⟨fun X => unrealify_mem_lieOf hS X.2, fun ρ hρ => ?_⟩
  let R : Matrix (Fin m) (Fin m) ℂ → EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
    fun X => (WithLp.equiv 2 _).symm (realifyFun X)
  have hR : Continuous R := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
    obtain ⟨i, j, b⟩ := p
    cases b
    · simp only [realifyFun]; simp; fun_prop
    · simp only [realifyFun]; simp; fun_prop
  have hR0 : R 0 = 0 := by
    ext p; simp [R, realifyFun]
  have hU : R ⁻¹' Metric.ball 0 ρ ∈ 𝓝 (0 : Matrix (Fin m) (Fin m) ℂ) :=
    hR.continuousAt.preimage_mem_nhds (by rw [hR0]; exact Metric.ball_mem_nhds _ hρ)
  have h := eventually_exists_exp_matrix hS hU
  obtain ⟨δ, hδ, hb⟩ := (Metric.eventually_nhds_iff (α := Fin m → Fin m → ℂ)).1 h
  refine ⟨δ, hδ, fun g hg hgδ => ?_⟩
  obtain ⟨X, hXU, hXL, rfl⟩ := @hb g (by
    refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => ?_
    rw [dist_eq_norm]; exact hgδ i j) hg
  refine ⟨⟨R X, Submodule.subset_span ⟨X, hXL, rfl⟩⟩, ?_, ?_⟩
  · rw [mem_ball_zero_iff]; exact mem_ball_zero_iff.1 hXU
  · simp only [R]; rw [unrealify_realify]

end GlobalTheory.ClosedMatGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheoremStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_matrix_subgroup_theorem : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)), PI.IsMatGroup S → (∀ X : lieE S, unrealify (X : EuclideanSpace ℝ _) ∈ lieOf S) ∧ ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) → Matrix.of.symm g ∈ expSet S (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.ClosedMatGroup.closed_subgroup | exact GlobalTheory.ClosedMatGroup.closed_subgroup | (intros; apply GlobalTheory.ClosedMatGroup.closed_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpen
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem Hpk_ne_zero' (k r : ℕ) : Hpk k r ≠ 0 := by
  intro h
  have h1 : Hpk k r ⟨r + k, by omega⟩ ⟨r + k, by omega⟩ = -1 := by
    simp [Hpk]
  rw [h] at h1
  simp at h1

theorem IsClosedSub.mul_inv {S : Set (Mat k r)} (hS : IsClosedSub k r S) {a : Mat k r} (ha : a ∈ S) :
    a * a⁻¹ = 1 := by
  by_cases hd : IsUnit a.det
  · exact Matrix.mul_nonsing_inv a hd
  · exfalso
    have h0 : a⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit a hd
    have hm : a⁻¹ ∈ GG k r := hS.1 (hS.2.2.2.2 a ha)
    rw [h0] at hm
    have : (0 : Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hm
    simp at this
    exact Hpk_ne_zero' k r this.symm

theorem IsClosedSub.isMatGroup {S : Set (Mat k r)} (hS : IsClosedSub k r S) : PI.IsMatGroup S :=
  ⟨hS.2.1, hS.2.2.1, hS.2.2.2.1, fun a ha => ⟨hS.2.2.2.2 a ha, hS.mul_inv ha⟩⟩

theorem haarOn_locFinite_openPos :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ →
      (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧
      (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  intro k r S μ hS hμ
  have hμ' : PI.IsHaarOnM S μ := hμ
  obtain ⟨-, hK, hU⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ S μ hS.isMatGroup hμ'
  refine ⟨fun C hC => ?_, hU⟩
  have hA : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS.2.1
  have h1 : μ C ≤ μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) + μ (C \ {x : Mt k r | Matrix.of x ∈ S}) :=
    measure_le_inter_add_sdiff μ C _
  have h2 : μ (C \ {x : Mt k r | Matrix.of x ∈ S}) = 0 :=
    measure_mono_null (fun x hx => hx.2) hμ.2.2.1
  have h3 : μ (C ∩ {x : Mt k r | Matrix.of x ∈ S}) < ⊤ :=
    hK _ (hC.inter_right hA) (fun x hx => hx.2)
  rw [h2, add_zero] at h1
  exact lt_of_le_of_lt h1 h3

end GlobalTheory.SgInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselHaarFiniteCompactPosOpenStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedSubgroupBessel_haar_finite_compact_pos_open : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ → (∀ C : Set (Mt k r), IsCompact C → μ C < ⊤) ∧ (∀ U : Set (Mt k r), IsOpen U → (∃ x ∈ U, Matrix.of x ∈ S) → 0 < μ U) := by
  first | exact @GlobalTheory.SgInf.haarOn_locFinite_openPos | exact GlobalTheory.SgInf.haarOn_locFinite_openPos | (intros; apply GlobalTheory.SgInf.haarOn_locFinite_openPos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualPropertiesStatement
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autPointLatticeIntersection_selfDual_properties : ∀ (I : AutInst) (x : I.GA), (∀ y, y ∈ lamX I x ↔ I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf) ∧ (lamX I x).FG ∧ Submodule.span I.E (lamX I x : Set (Fin I.n → I.E)) = ⊤ ∧ (∀ y, y ∈ lamX I x ↔ ∀ z ∈ lamX I x, Formalism.UG.hform (starRingEnd I.E) I.J z y ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ ∀ k : I.GA, k.2 ∈ I.Kset → lamX I (x * k) = lamX I x := by
  first | exact @GlobalTheory.PointLattice.lamX_selfDual | exact GlobalTheory.PointLattice.lamX_selfDual | (intros; apply GlobalTheory.PointLattice.lamX_selfDual <;> assumption)
end
