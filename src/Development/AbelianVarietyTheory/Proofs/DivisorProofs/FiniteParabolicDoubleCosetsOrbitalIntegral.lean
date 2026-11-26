module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatrices
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isCompact_krylov_units : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  intro E _ _ w r Ω hΩ hcov
  classical
  let kr : (Fin r → w.adicCompletion E) → GLw r w → Matrix (Fin r) (Fin r) (w.adicCompletion E) :=
    fun e y => GlobalTheory.LeviDesc.Krylov.krylov y.val e
  have hkc : ∀ e, Continuous (kr e) := by
    intro e
    have hv : Continuous fun y : GLw r w => (y.val : Matrix (Fin r) (Fin r) (w.adicCompletion E)) :=
      Units.continuous_val
    refine continuous_matrix fun i j => ?_
    simp only [kr, GlobalTheory.LeviDesc.Krylov.krylov_apply]
    exact (continuous_apply i).comp ((hv.pow (j : ℕ)).matrix_mulVec continuous_const)
  let U : (Fin r → w.adicCompletion E) → Set (GLw r w) := fun e => {y | (kr e y).det ≠ 0}
  have hU : ∀ e, IsOpen (U e) := fun e => isOpen_ne_fun ((hkc e).matrix_det) continuous_const
  have hsub : Ω ⊆ ⋃ e, U e := by
    intro y hy
    obtain ⟨e, he⟩ := hcov y hy
    exact Set.mem_iUnion.2 ⟨e, he.ne_zero⟩
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover U hU hsub
  obtain ⟨K, hKc, hKU, hΩK⟩ := hΩ.finite_compact_cover t U (fun e _ => hU e) ht
  have hunit : ∀ e, ∀ y : K e, IsUnit (kr e y.1) := fun e y =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hKU e y.2))
  let f : ∀ e, K e → GLw r w := fun e y => (hunit e y).unit
  have hf : ∀ e, Continuous (f e) := by
    intro e
    rw [Units.continuous_iff]
    constructor
    · exact (hkc e).comp continuous_subtype_val
    · have : (fun y : K e => ((f e y)⁻¹ : GLw r w).val) = fun y => (kr e y.1)⁻¹ := by
        funext y
        rw [Matrix.coe_units_inv]
        rfl
      rw [this]
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (((hkc e).comp continuous_subtype_val).matrix_det.inv₀ fun y => hKU e y.2).smul
        ((hkc e).comp continuous_subtype_val).matrix_adjugate
  refine ⟨⋃ e ∈ t, Set.range (f e), t.isCompact_biUnion fun e _ => ?_, ?_⟩
  · haveI := isCompact_iff_compactSpace.1 (hKc e)
    exact isCompact_range (hf e)
  · intro y hy
    rw [hΩK] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨e, he, hyK⟩ := hy
    exact ⟨e, f e ⟨y, hyK⟩, Set.mem_biUnion he ⟨⟨y, hyK⟩, rfl⟩, rfl⟩

end GlobalTheory.LeviDesc.Krylov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatricesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_invertible_krylovMatrices : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units | exact GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEq
open Matrix Polynomial

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by
  have h := Matrix.aeval_self_charpoly y
  have hm := (Matrix.charpoly_monic y).as_sum
  have hd : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  rw [hd] at hm
  rw [hm] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Algebra.smul_def] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]
  simp only [Algebra.smul_def]
  exact eq_neg_of_add_eq_zero_left h

def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i

theorem mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < r
  · simp only [companion, Matrix.of_apply, hj, if_true]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]
    · simp [krylov_apply]
    · intro k _ hk
      have : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hr : (j : ℕ) + 1 = r := by omega
    simp only [companion, Matrix.of_apply, hj, if_false]
    rw [hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]
    simp [krylov_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

theorem krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by
  rw [krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]

end GlobalTheory.LeviDesc.Krylov
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEqStatement
open Matrix Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq : ∀ {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F), y.charpoly = y'.charpoly → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det → IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y' e').det → (GlobalTheory.LeviDesc.Krylov.krylov y e)⁻¹ * y * GlobalTheory.LeviDesc.Krylov.krylov y e = (GlobalTheory.LeviDesc.Krylov.krylov y' e')⁻¹ * y' * GlobalTheory.LeviDesc.Krylov.krylov y' e' := by
  first | exact @GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | exact GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq | (intros; apply GlobalTheory.LeviDesc.Krylov.krylov_conj_eq_of_charpoly_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegral
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LeviDesc.OrbFin
open GlobalTheory.LeviDesc.Krylov

theorem exists_cyclic {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (hy : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (krylov y e).det :=
  GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable y hy

theorem krylov_conj_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F)
    (hc : y.charpoly = y'.charpoly) (he : IsUnit (krylov y e).det) (he' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' :=
  GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq y y' e e' hc he he'

theorem isClosed_charpoly_eq (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ)
    (χ : (w.adicCompletion E)[X]) : IsClosed {y : GLw r w | y.val.charpoly = χ} := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  haveI : Infinite (w.adicCompletion E) := Infinite.of_injective Nat.cast Nat.cast_injective
  have hset : {y : GLw r w | y.val.charpoly = χ} =
      ⋂ t : w.adicCompletion E, {y : GLw r w | ((Matrix.scalar (Fin r) t) - y.val).det = χ.eval t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hy t; rw [← Matrix.eval_charpoly, hy]
    · intro hy; exact Polynomial.funext fun t => by rw [Matrix.eval_charpoly]; exact hy t
  rw [hset]
  refine isClosed_iInter fun t => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

theorem exists_compact_krylov (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w))
    (hΩ : IsCompact Ω) (h : ∀ y ∈ Ω, ∃ e, IsUnit (krylov y.val e).det) :
    ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = krylov y.val e :=
  GlobalTheory.T.exists_compact_invertible_krylovMatrices E w r Ω hΩ h

theorem isOpen_KGL (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w (n := r) : Set (GLw r w)) :=
  GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E))

theorem orbit_fin (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (γ : GLw r w)
    (hs : γ.val.charpoly.Separable) (Ω : Set (GLw r w)) (hΩ : IsCompact Ω) :
    ∃ T : Set (GLw r w), T.Finite ∧ ∀ q : GLw r w, q⁻¹ * γ * q ∈ Ω →
      ∃ z : GLw r w, z * γ = γ * z ∧ ∃ t ∈ T, ∃ k ∈ GlobalTheory.LFun.KGL w (n := r), q = z * t * k := by
  set Ωχ := Ω ∩ {y : GLw r w | y.val.charpoly = γ.val.charpoly} with hΩχ
  have hcpt : IsCompact Ωχ := hΩ.inter_right (isClosed_charpoly_eq E w r _)
  have hcyc : ∀ y ∈ Ωχ, ∃ e, IsUnit (krylov y.val e).det := fun y hy =>
    exists_cyclic _ (by rw [hy.2]; exact hs)
  obtain ⟨C, hC, hCy⟩ := exists_compact_krylov E w r Ωχ hcpt hcyc
  obtain ⟨f, hf⟩ := exists_cyclic γ.val hs
  have hfu : IsUnit (krylov γ.val f) := (Matrix.isUnit_iff_isUnit_det _).2 hf
  set Bf : GLw r w := hfu.unit with hBf
  set D : Set (GLw r w) := (fun c => Bf * c⁻¹) '' C with hD
  have hDc : IsCompact D := hC.image (continuous_const.mul continuous_inv)
  have hKo := isOpen_KGL E w r
  obtain ⟨T, hT⟩ := hDc.elim_finite_subcover (fun c : GLw r w => (fun x => c⁻¹ * x) ⁻¹' (GlobalTheory.LFun.KGL w (n := r) : Set (GLw r w)))
    (fun c => hKo.preimage (continuous_const.mul continuous_id)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨(T : Set (GLw r w)), T.finite_toSet, fun q hq => ?_⟩
  have hy : q⁻¹ * γ * q ∈ Ωχ := by
    refine ⟨hq, ?_⟩
    show ((q⁻¹ * γ * q : GLw r w) : Matrix (Fin r) (Fin r) (w.adicCompletion E)).charpoly = γ.val.charpoly
    have := Matrix.charpoly_units_conj (q⁻¹) γ.val
    simpa [Matrix.coe_units_inv] using this
  obtain ⟨e, c, hcC, hce⟩ := hCy _ hy
  have he : IsUnit (krylov (q⁻¹ * γ * q : GLw r w).val e).det := by
    rw [← hce, ← Matrix.isUnit_iff_isUnit_det]; exact c.isUnit
  have hconj := krylov_conj_eq _ _ e f (hy.2) he hf
  have h1 : c⁻¹ * (q⁻¹ * γ * q) * c = Bf⁻¹ * γ * Bf := by
    ext1
    rw [Units.val_mul (c⁻¹ * (q⁻¹ * γ * q)) c, Units.val_mul c⁻¹ (q⁻¹ * γ * q), Units.val_mul (Bf⁻¹ * γ) Bf,
      Units.val_mul Bf⁻¹ γ, Matrix.coe_units_inv c, Matrix.coe_units_inv Bf, hce, hBf, IsUnit.unit_spec]
    exact hconj
  have hxD : Bf * c⁻¹ ∈ D := ⟨c, hcC, rfl⟩
  obtain ⟨t, htT, ht⟩ := Set.mem_iUnion₂.1 (hT hxD)
  refine ⟨q * c * Bf⁻¹, ?_, t, htT, t⁻¹ * (Bf * c⁻¹), ht, by group⟩
  calc q * c * Bf⁻¹ * γ = q * c * (Bf⁻¹ * γ * Bf) * Bf⁻¹ := by group
    _ = q * c * (c⁻¹ * (q⁻¹ * γ * q) * c) * Bf⁻¹ := by rw [h1]
    _ = γ * (q * c * Bf⁻¹) := by group

theorem avg_ne_zero_exists {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [avg, hc]

theorem charpoly_blk_separable (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (hs : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    (blk h w m 0 : GLw n w).val.charpoly.Separable := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dif_pos hM]
    rfl
  rw [hval, Matrix.charpoly_reindex, Matrix.mul_zero, Matrix.charpoly_fromBlocks_zero₁₂]
  exact hs

theorem fin_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  intro E _ _ n a b h w f hf m hs hγ
  obtain ⟨K', -, hsupp, -⟩ := hf
  set γ : GLw n w := blk h w m 0 with hγdef
  set P := GlobalTheory.LeviDesc.parP a n w
  set K := GlobalTheory.LFun.KGL w (n := n)
  set γP : P := ⟨γ, hγ⟩
  obtain ⟨T, hT, hTq⟩ := orbit_fin E w n γ (charpoly_blk_separable E n a b h w m hs) (tsupport f) hsupp
  have hcent : ∀ z : GLw n w, z * γ = γ * z → z ∈ P := fun z hz =>
    GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hs (show z * γ = γ * MonoidHom.id _ z from hz)
  let Q : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) → GLw n w → Prop :=
    fun d t => t ∈ T ∧ ∃ z : GLw n w, z * γ = γ * z ∧ ∃ k ∈ K, ((Quotient.out d : P) : GLw n w) = z * t * k
  have hex : ∀ d ∈ {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) |
      GlobalTheory.LeviDesc.cavg K f (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) ≠ 0}, ∃ t, Q d t := by
    intro d hd
    obtain ⟨k, hk⟩ := avg_ne_zero_exists _ hd
    set p : GLw n w := ((Quotient.out d : P) : GLw n w)
    have hmem : (p * k)⁻¹ * γ * (p * k) ∈ tsupport f := by
      apply subset_tsupport
      have : (p * k)⁻¹ * γ * (p * k) = (k : GLw n w)⁻¹ * (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) * k := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, p, γP]; group
      rw [this]; exact hk
    obtain ⟨z, hz, t, ht, k₁, hk₁, hq⟩ := hTq _ hmem
    refine ⟨t, ht, z, hz, k₁ * (k : GLw n w)⁻¹, K.mul_mem hk₁ (K.inv_mem k.2), ?_⟩
    rw [← mul_assoc, ← hq, mul_inv_cancel_right]
  refine Set.Finite.of_injOn (f := fun d => if hd : ∃ t, Q d t then hd.choose else 1) (t := T) ?_ ?_ hT
  · intro d hd
    simp only [dif_pos (hex d hd)]
    exact (hex d hd).choose_spec.1
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [dif_pos (hex d₁ hd₁), dif_pos (hex d₂ hd₂)] at heq
    obtain ⟨-, z₁, hz₁, k₁, hk₁, hp₁⟩ := (hex d₁ hd₁).choose_spec
    obtain ⟨-, z₂, hz₂, k₂, hk₂, hp₂⟩ := (hex d₂ hd₂).choose_spec
    rw [heq] at hp₁
    set t := (hex d₂ hd₂).choose
    have hzP : z₂ * z₁⁻¹ ∈ P := hcent _ (by
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group)
    set hP : P := ⟨z₂ * z₁⁻¹, hzP⟩
    have hcP : hP ∈ twCent (MonoidHom.id _) γP := by
      show hP * γP = γP * MonoidHom.id _ hP
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.id_apply, hP, γP]
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group
    set kP : P := (Quotient.out d₁)⁻¹ * hP⁻¹ * Quotient.out d₂
    have hkv : (kP : GLw n w) = k₁⁻¹ * k₂ := by
      simp only [kP, hP, Subgroup.coe_mul, Subgroup.coe_inv, hp₁, hp₂]; group
    have hkK : kP ∈ K.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf, hkv]; exact K.mul_mem (K.inv_mem hk₁) hk₂
    rw [← DoubleCoset.out_eq' d₁, ← DoubleCoset.out_eq' d₂, DoubleCoset.eq]
    exact ⟨hP, hcP, kP, hkK, by simp only [kP]; group⟩

end GlobalTheory.LeviDesc.OrbFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteParabolicDoubleCosetsOrbitalIntegralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_parabolicDoubleCosets_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w (n := n)).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w (n := n)) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  first | exact @GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | exact GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets | (intros; apply GlobalTheory.LeviDesc.OrbFin.fin_doubleCosets <;> assumption)
end
