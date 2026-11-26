module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRi
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

open Matrix

theorem isSst_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n (Bst P)),
    (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) *
      (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → IsSst P ρ := by
  intro l _ P AI T n _ _ K V _ _ b ρ Q hQ
  haveI : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    haveI := K.2
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  obtain ⟨crd, hcrd⟩ : ∃ crd : V ⊗[ℚ_[l]] Bst P ≃ₗ[ℚ_[l]] (n → Bst P),
      ∀ v c, crd (v ⊗ₜ c) = fun i => b.repr v i • c := by
    refine ⟨(TensorProduct.congr b.equivFun (LinearEquiv.refl _ _)) ≪≫ₗ TensorProduct.comm _ _ _ ≪≫ₗ
      TensorProduct.piScalarRight ℚ_[l] ℚ_[l] (Bst P) n, fun v c => ?_⟩
    funext i
    simp
  obtain ⟨ι, hι⟩ : ∃ ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P, ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) :=
    ⟨(Polynomial.CAlgHom.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B)).toLinearMap, fun _ => rfl⟩
  set M : ↥(GK K) → Matrix n n (Bst P) := fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P))
    with hM

  have hact : ∀ g x, crd (stRep P ρ g x) = M g *ᵥ (fun i => actSt P (g : GQ l) (crd x i)) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero =>
      funext i
      simp only [map_zero, Pi.zero_apply]
      rw [show (fun _ : n => (0 : Bst P)) = 0 from rfl, Matrix.mulVec_zero, Pi.zero_apply]
    | tmul v c =>
      funext i
      rw [stRep_tmul, hcrd, hcrd, ← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgHom.commutes,
        map_sum, Finset.sum_mul, mul_assoc]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add (f := _)]

  have hmv : ∀ (g : ↥(GK K)) (w : n → Bst P),
      (fun i => actSt P (g : GQ l) (((Q : Matrix n n (Bst P)) *ᵥ w) i)) =
        (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) *ᵥ (fun i => actSt P (g : GQ l) (w i)) := by
    intro g w
    funext i
    exact RingHom.map_mulVec ((actSt P (g : GQ l)) : Bst P →+* Bst P) _ w i
  have hQinv : ∀ w : n → Bst P, ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ ((Q : Matrix n n (Bst P)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Q.inv_mul, Matrix.one_mulVec]
  have hQinv' : ∀ w : n → Bst P, (Q : Matrix n n (Bst P)) *ᵥ (((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Q.mul_inv, Matrix.one_mulVec]
  let f : (n → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    crd.symm.toLinearMap ∘ₗ (((Q : Matrix n n (Bst P)).mulVecLin).restrictScalars ℚ_[l]) ∘ₗ LinearMap.compLeft ι n
  have hf : ∀ c, crd (f c) = (Q : Matrix n n (Bst P)) *ᵥ (fun i => ι (c i)) := by
    intro c
    simp [f, LinearMap.compLeft]
    rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h1 : (fun i => ι (c i)) = 0 := by
      have := hf c
      rw [hc, map_zero] at this
      rw [← hQinv (fun i => ι (c i)), ← this, Matrix.mulVec_zero]
    funext i
    have h2 := congrFun h1 i
    rw [hι, Pi.zero_apply, Polynomial.C_eq_zero] at h2
    exact (algebraMap ↥(K0 K) P.R.B).injective (h2.trans (map_zero _).symm)
  have hrange : LinearMap.range f = Dst P ρ := by
    ext x
    rw [mem_Dst, LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩ g
      apply crd.injective
      rw [hact, hf, hmv, Matrix.mulVec_mulVec, hQ g]
      congr 1
      funext i
      exact ((GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K (ι (c i))).mpr ⟨c i, hι _⟩) g
    · intro hx
      set z := ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ crd x with hz
      have hy : crd x = (Q : Matrix n n (Bst P)) *ᵥ z := (hQinv' _).symm
      have hinv : ∀ i g, actSt P ((g : ↥(GK K)) : GQ l) (z i) = z i := by
        intro i g
        have h1 := congrArg crd (hx g)
        rw [hact, hy, hmv, Matrix.mulVec_mulVec, hQ g] at h1
        have h2 := congrArg (fun w => ((Q⁻¹ : GL n (Bst P)) : Matrix n n (Bst P)) *ᵥ w) h1
        simp only [hQinv] at h2
        exact congrFun h2 i
      choose c hc using fun i => (GlobalTheory.T.semistablePeriodRing_galois_invariants_iff_const l P AI T K (z i)).mp (hinv i)
      refine ⟨c, crd.injective ?_⟩
      rw [hf, hy]
      congr 1
      funext i
      rw [hι, hc i]
  unfold IsSst
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Module.finrank_eq_card_basis b, mul_comm]

end GlobalTheory.PMon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableOfInvertiblePeriodMatrixSemistableRiStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemistable_of_invertible_periodMatrix_semistableRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n (Bst P)), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) → IsSst P ρ := by
  first | exact @GlobalTheory.PMon.isSst_of_periodMatrix | exact GlobalTheory.PMon.isSst_of_periodMatrix | (intros; apply GlobalTheory.PMon.isSst_of_periodMatrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteField
open Matrix Formalism.IndefR.Datum
open Classical

namespace GlobalTheory

theorem addChar_inv_isPrimitive_of_isPrimitive {k : Type} [Field k] {R : Type} [CommRing R] (ψ : AddChar k R)
    (hψ : ψ.IsPrimitive) : (ψ⁻¹).IsPrimitive := by
  intro a ha h
  apply hψ (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply, neg_mul] using this

theorem sum_addChar_trace_rectMatrix_mul {k : Type} [Field k] [Fintype k] {R : Type} [CommRing R] [IsDomain R]
    (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r t : ℕ} (m : Matrix (Fin t) (Fin r) k) :
    ∑ b : Matrix (Fin r) (Fin t) k, ψ (trace (b * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r * t) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin t) k) = Fintype.card (Fin r → Fin t → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, mul_comm]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin t) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin t) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

variable {k : Type} [Field k] {r t : ℕ}

def squareAndRectColumnsEquivWideMatrix : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k ≃ Matrix (Fin r) (Fin (r + t)) k where
  toFun p := fun i j => Fin.addCases (p.1 i) (p.2 i) j
  invFun y := (y.submatrix id (Fin.castAdd t), y.submatrix id (Fin.natAdd r))
  left_inv p := by
    ext i j
    · exact Fin.addCases_left (motive := fun _ => k) j
    · exact Fin.addCases_right (motive := fun _ => k) j
  right_inv y := by
    funext i j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

theorem topLeftBlock_neg_eq_submatrix_castAdd (y : Matrix (Fin r) (Fin (r + t)) k) :
    topL r (-y) = -(y.submatrix id (Fin.castAdd t)) := by
  ext i j; simp only [topL]; rw [dite_eq_left ⟨i.2, by omega⟩]; rfl

theorem topLeftBlock_eq_submatrix_castAdd (u : Matrix (Fin (r + t)) (Fin r) k) :
    topL r u = u.submatrix (Fin.castAdd t) id := by
  ext i j; simp only [topL]; rw [dite_eq_left ⟨by omega, j.2⟩]; rfl

theorem lowZero_iff_submatrix_natAdd_eq_zero (u : Matrix (Fin (r + t)) (Fin r) k) :
    LowZero r u ↔ u.submatrix (Fin.natAdd r) id = 0 := by
  constructor
  · intro h; ext i j; exact h (Fin.natAdd r i) j (by simp) j.2
  · intro h i j hi _
    obtain ⟨i', rfl⟩ : ∃ i' : Fin t, i = Fin.natAdd r i' := ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp; omega)⟩
    simpa using congr_fun (congr_fun h i') j

theorem trace_mul_split_castAdd_natAdd (y : Matrix (Fin r) (Fin (r + t)) k) (u : Matrix (Fin (r + t)) (Fin r) k) :
    trace (y * u) = trace (y.submatrix id (Fin.castAdd t) * u.submatrix (Fin.castAdd t) id) +
      trace (y.submatrix id (Fin.natAdd r) * u.submatrix (Fin.natAdd r) id) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_add, Finset.sum_add_distrib]

theorem sum_GL_character_neg_det_addChar_trace (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ)
    (w : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-a).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (a * w))
      = ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
          ψ⁻¹ (trace (w * (x : Matrix (Fin r) (Fin r) k))) := by
  symm
  refine Fintype.sum_of_injective (fun x : GL (Fin r) k => -(x : Matrix (Fin r) (Fin r) k))
    (fun x y e => Units.ext (neg_injective e)) _ _ ?_ ?_
  · intro a ha
    rw [dite_eq_right, zero_mul]
    intro h
    exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (-a) h.ne_zero, by simp⟩
  · intro x
    have hx : IsUnit (-(-(x : Matrix (Fin r) (Fin r) k))).det := by
      rw [neg_neg]; exact (Matrix.isUnit_iff_isUnit_det _).mp x.isUnit
    rw [dite_eq_left hx]
    have hu : hx.unit = Matrix.GeneralLinearGroup.det x := Units.ext (by simp)
    rw [hu, MonoidHom.inv_apply, inv_inv, AddChar.inv_apply, Matrix.trace_mul_comm w, neg_mul, trace_neg]

end GlobalTheory

namespace GlobalTheory

theorem fourier_flatDatum_finite : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  intro k _ _ ψ ξ r n hψ hξ
  rcases lt_or_ge n r with hnr | hrn
  · refine ⟨1, 0, one_ne_zero, isIntegral_one, by simpa using isIntegral_one, fun u => ?_⟩
    have h1 : ∀ y : Matrix (Fin r) (Fin n) k, (topL r (-y)).det = 0 := fun y =>
      Matrix.det_eq_zero_of_column_eq_zero ⟨n, hnr⟩ (fun i => by simp [topL])
    have h2 : (topL r u).det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨n, hnr⟩ (fun j => by simp [topL])
    rw [one_mul, dite_eq_right (by rintro ⟨-, h⟩; rw [h2] at h; exact not_isUnit_zero h)]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [dite_eq_right (by rw [h1 y]; exact not_isUnit_zero), zero_mul]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have hψ' : (ψ⁻¹).IsPrimitive := addChar_inv_isPrimitive_of_isPrimitive ψ hψ
  have hξ' : ξ⁻¹ ≠ 1 := inv_ne_one.mpr hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ⁻¹ ξ⁻¹ r hψ' hξ'
  set G : ℂ := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hG
  obtain ⟨hnorm, hGint, hGinv, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul k ψ⁻¹ ξ⁻¹ r hψ' hξ' G rfl
  set q : ℂ := (Fintype.card k : ℂ) with hq
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG0 : G ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have : (0 : ℝ) < (Fintype.card k : ℝ) ^ (r ^ 2) := pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
    rw [← hnorm] at this
    norm_num at this
  refine ⟨q ^ (r * t) * G, r * t + r ^ 2, mul_ne_zero (pow_ne_zero _ hq0) hG0, ?_, ?_, fun u => ?_⟩
  · refine IsIntegral.mul (IsIntegral.pow ?_ _) hGint
    rw [hq]
    exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (Fintype.card k : ℤ)))
  · have : q ^ (r * t + r ^ 2) * (q ^ (r * t) * G)⁻¹ = q ^ (r ^ 2) * G⁻¹ := by
      rw [pow_add, mul_inv]
      field_simp
    rw [this]
    exact hGinv

  set u₁ := u.submatrix (Fin.castAdd t) id
  set u₂ := u.submatrix (Fin.natAdd r) id
  have hsplit : ∀ p : Matrix (Fin r) (Fin r) k × Matrix (Fin r) (Fin t) k,
      ((if h : IsUnit (-p.1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace (p.1 * u₁))) *
        ψ (trace (p.2 * u₂)) =
      (if h : IsUnit (topL r (-(squareAndRectColumnsEquivWideMatrix p))).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (Matrix.trace (squareAndRectColumnsEquivWideMatrix p * u)) := by
    intro p
    have e1 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.castAdd t) = p.1 :=
      congrArg Prod.fst (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    have e2 : (squareAndRectColumnsEquivWideMatrix p).submatrix id (Fin.natAdd r) = p.2 :=
      congrArg Prod.snd (squareAndRectColumnsEquivWideMatrix.symm_apply_apply p)
    rw [mul_assoc, ← AddChar.map_add_eq_mul, trace_mul_split_castAdd_natAdd _ u, topLeftBlock_neg_eq_submatrix_castAdd, e1, e2]
  rw [← Fintype.sum_equiv squareAndRectColumnsEquivWideMatrix _ _ hsplit, Fintype.sum_prod_type]
  rw [show (∑ x : Matrix (Fin r) (Fin r) k, ∑ y : Matrix (Fin r) (Fin t) k,
      (if h : IsUnit (-(x, y).1).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (trace ((x, y).1 * u₁)) *
        ψ (trace ((x, y).2 * u₂))) =
      (∑ x : Matrix (Fin r) (Fin r) k, (if h : IsUnit (-x).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) *
        ψ (trace (x * u₁))) * ∑ y : Matrix (Fin r) (Fin t) k, ψ (trace (y * u₂)) by
    rw [Finset.sum_mul_sum]]
  rw [sum_GL_character_neg_det_addChar_trace, sum_addChar_trace_rectMatrix_mul ψ hψ u₂]
  by_cases hu2 : u₂ = 0
  swap
  · rw [if_neg hu2, mul_zero, dite_eq_right (fun h => hu2 ((lowZero_iff_submatrix_natAdd_eq_zero u).mp h.1)), mul_zero]
  rw [if_pos hu2]
  by_cases hdet : IsUnit u₁.det
  swap
  · have h0 : u₁.det = 0 := by
      by_contra h; exact hdet (isUnit_iff_ne_zero.mpr h)
    rw [hsing u₁ h0, zero_mul, dite_eq_right, mul_zero]
    rintro ⟨-, h⟩
    rw [topLeftBlock_eq_submatrix_castAdd] at h
    exact hdet h
  have hh : LowZero r u ∧ IsUnit (topL r u).det := ⟨(lowZero_iff_submatrix_natAdd_eq_zero u).mpr hu2, by rw [topLeftBlock_eq_submatrix_castAdd]; exact hdet⟩
  rw [dite_eq_left hh]
  set a : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero u₁ hdet.ne_zero
  have ha := hinv a
  simp only [Matrix.one_mul] at ha
  have hau : (a : Matrix (Fin r) (Fin r) k) = u₁ := rfl
  rw [hau] at ha
  rw [ha, ← hG]
  have hunit : hh.2.unit = Matrix.GeneralLinearGroup.det a := Units.ext (by simp [hau, topLeftBlock_eq_submatrix_castAdd, u₁])
  rw [hunit, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, _root_.zpow_neg_one]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierFlatCharacterDatumFiniteFieldStatement
open Matrix Formalism.IndefR.Datum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_flat_character_datum_finiteField : ∀ (k : Type) [Field k] [Fintype k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r n : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∃ (C : ℂ) (m : ℕ), C ≠ 0 ∧ IsIntegral ℤ C ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ m * C⁻¹) ∧ ∀ u : Matrix (Fin n) (Fin r) k, (∑ y : Matrix (Fin r) (Fin n) k, (if h : IsUnit (topL r (-y)).det then ((ξ h.unit : ℂˣ) : ℂ) else 0) * ψ (Matrix.trace (y * u))) = C * (if h : LowZero r u ∧ IsUnit (topL r u).det then ((ξ h.2.unit : ℂˣ) : ℂ) ^ (-1 : ℤ) else 0) := by
  first | exact @GlobalTheory.fourier_flatDatum_finite | exact GlobalTheory.fourier_flatDatum_finite | (intros; apply GlobalTheory.fourier_flatDatum_finite <;> assumption)
end
end
