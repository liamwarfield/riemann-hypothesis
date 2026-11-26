module

public import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic

@[expose] public section

section -- merged from GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
namespace GroundTheory.Global

open Matrix

theorem exists_rat_intertwiner {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (A A' : J → Matrix ι ι ℚ) (P : Matrix ι ι ℝ) (hP : P.det ≠ 0)
    (h : ∀ j, P * (A j).map (Rat.cast : ℚ → ℝ) = (A' j).map (Rat.cast : ℚ → ℝ) * P) :
    ∃ Q : Matrix ι ι ℚ, Q.det ≠ 0 ∧ ∀ j, Q * A j = A' j * Q := by

  obtain ⟨V, hV⟩ : ∃ V : Submodule ℚ ℝ,
      V = Submodule.span ℚ (Set.range fun p : ι × ι => P p.1 p.2) := ⟨_, rfl⟩
  have : Module.Finite ℚ V := hV ▸ Module.Finite.span_of_finite ℚ (Set.finite_range _)
  obtain ⟨κ, _, ⟨c⟩⟩ : ∃ (κ : Type) (_ : Fintype κ), Nonempty (Module.Basis κ ℚ V) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℚ V⟩⟩
  have hmem : ∀ a b, P a b ∈ V := fun a b => hV ▸ Submodule.subset_span ⟨(a, b), rfl⟩

  let Bm : κ → Matrix ι ι ℚ := fun k a b => c.repr ⟨P a b, hmem a b⟩ k
  have hcast : ∀ (q : ℚ) (r : ℝ), q • r = (q : ℝ) * r := fun q r => by
    rw [Algebra.smul_def, eq_ratCast]
  have hP_eq : P = ∑ k, (c k : ℝ) • (Bm k).map (Rat.cast : ℚ → ℝ) := by
    ext a b
    have h1 := congrArg (Subtype.val : V → ℝ) (c.sum_repr ⟨P a b, hmem a b⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul, hcast] at h1
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hli : LinearIndependent ℚ (fun k => (c k : ℝ)) :=
    c.linearIndependent.map' V.subtype (Submodule.ker_subtype V)

  have hB : ∀ k j, Bm k * A j = A' j * Bm k := by
    intro k j
    have hsum : ∑ k, (c k : ℝ) • (Bm k * A j - A' j * Bm k).map (Rat.cast : ℚ → ℝ) = 0 := by
      have hmap : ∀ X Y : Matrix ι ι ℚ, (X * Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) * Y.map (Rat.cast : ℚ → ℝ) := fun X Y =>
        Matrix.map_mul (f := Rat.castHom ℝ)
      have hsub : ∀ X Y : Matrix ι ι ℚ, (X - Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) - Y.map (Rat.cast : ℚ → ℝ) := fun X Y => by
        ext; simp
      have e1 : ∑ k, (c k : ℝ) • ((Bm k).map (Rat.cast : ℚ → ℝ) * (A j).map (Rat.cast : ℚ → ℝ)) =
          P * (A j).map (Rat.cast : ℚ → ℝ) := by
        rw [hP_eq, Finset.sum_mul]
        simp only [Matrix.smul_mul]
      have e2 : ∑ k, (c k : ℝ) • ((A' j).map (Rat.cast : ℚ → ℝ) * (Bm k).map (Rat.cast : ℚ → ℝ)) =
          (A' j).map (Rat.cast : ℚ → ℝ) * P := by
        rw [hP_eq, Finset.mul_sum]
        simp only [Matrix.mul_smul]
      simp only [hsub, hmap, smul_sub, Finset.sum_sub_distrib, e1, e2, h j, sub_self]
    ext a b
    have hab := congrFun (congrFun hsum a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at hab
    have := Fintype.linearIndependent_iff.1 hli (fun k => (Bm k * A j - A' j * Bm k) a b)
      (by simpa only [hcast, mul_comm] using hab) k
    rwa [Matrix.sub_apply, sub_eq_zero] at this

  clear_value Bm
  obtain ⟨Mx, hMx⟩ : ∃ Mx : Matrix ι ι (MvPolynomial κ ℚ),
      Mx = Matrix.of fun a b => ∑ k, MvPolynomial.X k * MvPolynomial.C (Bm k a b) := ⟨_, rfl⟩
  have hev : ∀ (t : κ → ℝ),
      (MvPolynomial.aeval t : MvPolynomial κ ℚ →ₐ[ℚ] ℝ).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, t k * algebraMap ℚ ℝ (Bm k a b) := by
    intro t
    ext a b
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hMx, Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have hPof : P = Matrix.of fun a b => ∑ k, (c k : ℝ) * algebraMap ℚ ℝ (Bm k a b) := by
    refine hP_eq.trans ?_
    ext a b
    rw [Matrix.sum_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eq_ratCast]
  have hF : Mx.det ≠ 0 := by
    intro h0
    apply hP
    rw [hPof, ← hev, ← AlgHom.map_det, h0]
    exact map_zero _
  obtain ⟨q, hq⟩ : ∃ q : κ → ℚ, MvPolynomial.eval q Mx.det ≠ 0 := by
    by_contra! hall
    exact hF (MvPolynomial.funext fun x => by rw [hall x, map_zero])
  refine ⟨∑ k, q k • Bm k, ?_, fun j => ?_⟩
  · have hQ : ∑ k, q k • Bm k = Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [Matrix.sum_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
    have hevq : (MvPolynomial.eval q).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, hMx, Matrix.of_apply, Matrix.of_apply,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.algebraMap_self,
        RingHom.id_apply]
    have := RingHom.map_det (MvPolynomial.eval q) Mx
    rw [hevq] at this
    rw [hQ, ← this]
    exact hq
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul, Matrix.mul_smul, hB]

end GroundTheory.Global
end

namespace GroundTheory.Global

open GroundTheory.GroupCoh
open scoped TensorProduct

theorem finite_quotient_of_smul_mem {B : Type*} [AddCommGroup B] [Module.Finite ℤ B]
    (S : AddSubgroup B) {n : ℤ} (hn : n ≠ 0) (h : ∀ y, n • y ∈ S) : Finite (B ⧸ S) := by
  have : Module.Finite ℤ (B ⧸ S) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective S y
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • (QuotientAddGroup.mk' S x) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact h x

variable {G M M' : Type*} [Group G] [AddCommGroup M] [AddCommGroup M']

theorem cyclicHerbrand_eq_of_injective [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (φ : M →+ M') (hφ : Function.Injective φ)
    [Finite (M' ⧸ φ.range)] (hcomm : ∀ g x, φ (ρ g x) = ρ' g (φ x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ :=
  herbrandQuotient_eq_of_injective_of_finite (fA := cycSub ρ σ) (gA := normHom ρ)
    (fB := cycSub ρ' σ) (gB := normHom ρ') hφ
    (fun a => by rw [cycSub_apply, cycSub_apply, map_sub, hcomm])
    (fun a => by rw [normHom_apply, normHom_apply, map_sum]; simp only [hcomm])
    (cycSub_normHom ρ' σ) (normHom_cycSub ρ' σ)

theorem exists_injective_intertwiner_of_basis {ι : Type*} [Fintype ι]
    (ρ : Representation ℤ G M) (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x))
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M') :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  classical

  let bR := Algebra.TensorProduct.basis ℝ b
  let bR' := Algebra.TensorProduct.basis ℝ b'
  let A : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b b (ρ g)
  let A' : G → Matrix ι ι ℤ := fun g => LinearMap.toMatrix b' b' (ρ' g)
  let P : Matrix ι ι ℝ := LinearMap.toMatrix bR bR' e.toLinearMap
  have hP : P.det ≠ 0 := by
    have hid : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id :=
      LinearMap.ext fun x => by simp
    have h1 := congrArg (LinearMap.toMatrix bR bR) hid
    rw [LinearMap.toMatrix_comp bR bR' bR, LinearMap.toMatrix_id] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact right_ne_zero_of_mul_eq_one h2
  have hPA : ∀ g, P * (A g).map (Int.cast : ℤ → ℝ) = (A' g).map (Int.cast : ℤ → ℝ) * P := by
    intro g
    have hc : e.toLinearMap ∘ₗ (ρ g).baseChange ℝ = (ρ' g).baseChange ℝ ∘ₗ e.toLinearMap :=
      LinearMap.ext (he g)
    have h1 := congrArg (LinearMap.toMatrix bR bR') hc
    rw [LinearMap.toMatrix_comp bR bR bR', LinearMap.toMatrix_comp bR bR' bR',
      LinearMap.toMatrix_baseChange, LinearMap.toMatrix_baseChange, algebraMap_int_eq] at h1
    exact h1

  obtain ⟨Q, hQ, hQA⟩ := exists_rat_intertwiner (fun g => (A g).map (Int.cast : ℤ → ℚ))
    (fun g => (A' g).map (Int.cast : ℤ → ℚ)) P hP (fun g => by
      rw [Matrix.map_map, Matrix.map_map]
      convert hPA g using 3 <;> ext x <;> simp)

  obtain ⟨⟨d, hd⟩, hdQ⟩ := IsLocalization.exist_integer_multiples (R := ℤ)
    (M := nonZeroDivisors ℤ) (S := ℚ) Finset.univ (fun p : ι × ι => Q p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose D hD using fun a b => RingHom.mem_rangeS.1 (hdQ (a, b) (Finset.mem_univ _))
  let Dm : Matrix ι ι ℤ := Matrix.of D
  have hDm : Dm.map (Int.cast : ℤ → ℚ) = (d : ℚ) • Q := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, Dm, Matrix.of_apply]
    rw [← eq_intCast (algebraMap ℤ ℚ), hD a b, zsmul_eq_mul, smul_eq_mul]
  have hdet : Dm.det ≠ 0 := by
    have h1 : (Dm.det : ℚ) = (d : ℚ) ^ Fintype.card ι * Q.det := by
      rw [Int.cast_det]
      change (Dm.map (Int.cast : ℤ → ℚ)).det = _
      rw [hDm, Matrix.det_smul]
    intro h0
    rw [h0, Int.cast_zero] at h1
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd0)) hQ h1.symm
  have hmap : ∀ X Y : Matrix ι ι ℤ, (X * Y).map (Int.cast : ℤ → ℚ) =
      X.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) := fun X Y =>
    Matrix.map_mul (f := Int.castRingHom ℚ)
  have hDA : ∀ g, Dm * A g = A' g * Dm := by
    intro g
    apply Matrix.map_injective (f := (Int.cast : ℤ → ℚ)) Int.cast_injective
    show (Dm * A g).map (Int.cast : ℤ → ℚ) = (A' g * Dm).map (Int.cast : ℤ → ℚ)
    rw [hmap, hmap, hDm, Matrix.smul_mul, Matrix.mul_smul, hQA g]

  let φ : M →ₗ[ℤ] M' := Matrix.toLin b b' Dm
  refine ⟨φ, ?_, ⟨Dm.det, hdet, fun y => ?_⟩, fun g x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Matrix.repr_toLin (v₁ := b) (v₂ := b') Dm x
    rw [show Matrix.toLin b b' Dm x = 0 from hx, map_zero] at h1
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1.symm
    exact b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun h2 i)
  · refine ⟨Matrix.toLin b' b Dm.adjugate y, ?_⟩
    show (Matrix.toLin b b' Dm ∘ₗ Matrix.toLin b' b Dm.adjugate) y = _
    rw [← Matrix.toLin_mul, Matrix.mul_adjugate, map_smul, Matrix.toLin_one,
      LinearMap.smul_apply, LinearMap.id_apply]
  · have h1 : φ ∘ₗ ρ g = ρ' g ∘ₗ φ := by
      apply (LinearMap.toMatrix b b').injective
      rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b',
        LinearMap.toMatrix_toLin]
      exact hDA g
    exact LinearMap.congr_fun h1 x

variable [Module.Finite ℤ M] [Module.Free ℤ M] [Module.Finite ℤ M'] [Module.Free ℤ M']

theorem exists_injective_intertwiner_of_real_equiv (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    ∃ φ : M →ₗ[ℤ] M', Function.Injective φ ∧ (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ g x, φ (ρ g x) = ρ' g (φ x) := by
  let b := Module.Free.chooseBasis ℤ M
  let b₀ := Module.Free.chooseBasis ℤ M'
  have h1 := e.finrank_eq
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b),
    Module.finrank_eq_card_basis (Algebra.TensorProduct.basis ℝ b₀)] at h1
  exact exists_injective_intertwiner_of_basis ρ ρ' e he b
    (b₀.reindex (Fintype.equivOfCardEq h1).symm)

theorem cyclicHerbrand_eq_of_real_equiv [Fintype G] (ρ : Representation ℤ G M)
    (ρ' : Representation ℤ G M') (σ : G) (e : ℝ ⊗[ℤ] M ≃ₗ[ℝ] ℝ ⊗[ℤ] M')
    (he : ∀ g x, e ((ρ g).baseChange ℝ x) = (ρ' g).baseChange ℝ (e x)) :
    cyclicHerbrand ρ σ = cyclicHerbrand ρ' σ := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ := exists_injective_intertwiner_of_real_equiv ρ ρ' e he
  have : Finite (M' ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
  exact cyclicHerbrand_eq_of_injective ρ ρ' σ φ.toAddMonoidHom hφ hcomm

end GroundTheory.Global
