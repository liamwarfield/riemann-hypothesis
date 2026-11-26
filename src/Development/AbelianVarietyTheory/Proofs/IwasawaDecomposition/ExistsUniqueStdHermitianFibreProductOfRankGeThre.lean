module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductMeasureBasicProperties
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardQuadricSubSqLe
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.QuadricCount

lemma sum_dot {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (w : ι → k) :
    ∑ x : ι → k, ψ (x ⬝ᵥ w) = if w = 0 then ((Fintype.card k : ℂ) ^ Fintype.card ι) else 0 := by
  split_ifs with hw
  · subst hw; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    have hi' : w i ≠ 0 := hi
    have h1 : ∃ a : k, ψ (a * w i) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have := AddChar.sum_mulShift (w i) hψ
      simp [hcon, hi'] at this
    obtain ⟨a, ha⟩ := h1
    have h2 : ∑ x : ι → k, ψ (x ⬝ᵥ w) = ψ (a * w i) * ∑ x : ι → k, ψ (x ⬝ᵥ w) := by
      rw [Finset.mul_sum]
      rw [← Equiv.sum_comp (Equiv.addLeft (Pi.single i a : ι → k))]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [add_dotProduct, AddChar.map_add_eq_mul]
    have h3 : (1 - ψ (a * w i)) * ∑ x : ι → k, ψ (x ⬝ᵥ w) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (sub_eq_zero.mp h).symm ha
    · exact h

lemma gauss_normSq {k : Type} [Field k] [Fintype k] [DecidableEq k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ : AddChar k ℂ) (hψ : ψ.IsPrimitive) (S : Matrix ι ι k) (h2 : (2 : k) ≠ 0) (hS : S.IsSymm)
    (hd : S.det ≠ 0) (t : k) (ht : t ≠ 0) :
    ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))‖ ^ 2 = (Fintype.card k : ℝ) ^ Fintype.card ι := by
  have hsym : ∀ x z : ι → k, z ⬝ᵥ S.mulVec x = x ⬝ᵥ S.mulVec z := by
    intro x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq, dotProduct_comm]
  have key : (starRingEnd ℂ) (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)))
      = (Fintype.card k : ℂ) ^ Fintype.card ι := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    have e1 : ∀ x : ι → k, (starRingEnd ℂ) (ψ (t * (x ⬝ᵥ S.mulVec x))) * (∑ y : ι → k, ψ (t * (y ⬝ᵥ S.mulVec y)))
        = ∑ z : ι → k, ψ (t * (z ⬝ᵥ S.mulVec z)) * ψ (x ⬝ᵥ ((2 * t) • S.mulVec z)) := by
      intro x
      rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft x)]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      simp only [Equiv.coe_addLeft, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_smul, smul_eq_mul, hsym x z]
      ring
    simp_rw [e1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_dot ψ hψ]
    rw [Finset.sum_eq_single (0 : ι → k)]
    · simp
    · intro z _ hz
      rw [if_neg, mul_zero]
      intro h
      rcases smul_eq_zero.mp h with h | h
      · exact mul_ne_zero h2 ht h
      · exact hz (Matrix.eq_zero_of_mulVec_eq_zero hd h)
    · simp
  rw [Complex.conj_mul'] at key
  exact_mod_cast key

theorem card_quadric_sub_sq_le : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (S : Matrix ι ι k) (β : k), (2 : k) ≠ 0 → S.IsSymm → S.det ≠ 0 → (((Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card : ℝ) - (Fintype.card k : ℝ) ^ (Fintype.card ι - 1)) ^ 2 ≤ (Fintype.card k : ℝ) ^ Fintype.card ι := by
  intro k _ _ _ ι _ _ _ S β h2 hS hd
  set ψ := AddChar.FiniteField.primitiveChar_to_Complex k
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive k
  set N := (Finset.univ.filter fun x : ι → k => x ⬝ᵥ S.mulVec x = β).card with hN
  set q := Fintype.card k with hq
  set m := Fintype.card ι with hm
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hm0 : m = (m - 1) + 1 := by have : 0 < m := Fintype.card_pos; omega
  have e1 : ∑ x : ι → k, ∑ t : k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) * N := by
    simp_rw [AddChar.sum_mulShift _ hψ, sub_eq_zero]
    push_cast
    rw [← Finset.sum_filter]
    simp [hN, hq, mul_comm]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : k))] at e1
  have e2 : ∑ x : ι → k, ψ (0 * (x ⬝ᵥ S.mulVec x - β)) = (q : ℂ) ^ m := by
    simp [hq, hm]
  rw [e2] at e1
  set r : ℝ := Real.sqrt ((q : ℝ) ^ m) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (q : ℝ) ^ m := Real.sq_sqrt (by positivity)
  have e3 : ∀ t ∈ Finset.univ.erase (0 : k), ‖∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β))‖ ≤ r := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
    have : ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x - β)) = ψ (-(t * β)) * ∑ x : ι → k, ψ (t * (x ⬝ᵥ S.mulVec x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this, norm_mul, AddChar.norm_apply, one_mul, hr, ← gauss_normSq ψ hψ S h2 hS hd t ht0, Real.sqrt_sq (norm_nonneg _)]
  have e4 : ‖(q : ℂ) * N - (q : ℂ) ^ m‖ ≤ q * r := by
    rw [← e1, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ e3).trans ?_)
    rw [nsmul_eq_mul]
    gcongr
    exact Finset.card_le_univ _
  have e5 : (q : ℂ) * N - (q : ℂ) ^ m = (((q : ℝ) * ((N : ℝ) - (q : ℝ) ^ (m - 1)) : ℝ) : ℂ) := by
    conv_lhs => rw [hm0]
    push_cast
    ring
  rw [e5, Complex.norm_real, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hq0] at e4
  have e6 := le_of_mul_le_mul_left e4 hq0
  rw [← hr2, ← sq_abs]
  gcongr

end GlobalTheory.QuadricCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBound
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

noncomputable section

namespace GlobalTheory.GaugeDensity

section Gram

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {d M : ℕ} (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E)

def gram : Matrix (Fin M × Fin d) (Fin M × Fin d) F :=
  fun p q => 1 / 2 * Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)

theorem invol (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem trace_conj (h : IsCMExt F E σ) (e : E) : Algebra.trace F E (σ e) = Algebra.trace F E e :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ (Function.Involutive.bijective (invol σ h))) e

theorem gram_symm (h : IsCMExt F E σ) (hJ : IsHermND σ J) : (gram σ b J).IsSymm := by
  ext p q
  simp only [gram, Matrix.transpose_apply]
  rw [← trace_conj σ h, map_mul σ, map_mul σ, invol σ h, hJ.1]
  congr 2
  ring

theorem gram_det (h : IsCMExt F E σ) (hJ : IsHermND σ J) : (gram σ b J).det ≠ 0 := by
  classical
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨x, hx0, hx⟩
  let y : Fin M → E := fun j => ∑ l, x (j, l) • b l
  have h1 : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have := congrFun hx (i, k)
    simp only [Matrix.mulVec, dotProduct, gram, Fintype.sum_prod_type, Pi.zero_apply, mul_assoc,
      ← Finset.mul_sum] at this
    have h2 := (mul_eq_zero.1 this).resolve_left (by norm_num)
    rw [← h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, map_sum, mul_smul_comm, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => mul_comm _ _
  have h2 : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Algebra.traceForm_apply, ← invol σ h z, ← b.sum_repr (σ z), map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Algebra.smul_def, map_mul σ, σ.commutes, ← Algebra.smul_def, mul_smul_comm, map_smul,
      mul_comm, h1, smul_zero]
  have h3 : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 h2
  refine hx0 (funext fun p => ?_)
  exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun l => x (p.1, l)) (congrFun h3 p.1) p.2

variable (R : Type) [CommRing R] [Algebra F R]

theorem qR_eq (x : Fin M → R ⊗[F] E) :
    qR R σ J x = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
      ((gram σ b J).map (algebraMap F R)) *ᵥ
        (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) := by
  obtain ⟨c, hc⟩ : ∃ c : Fin M → Fin d → R, ∀ i k, (Algebra.TensorProduct.basis R b).repr (x i) k = c i k :=
    ⟨_, fun _ _ => rfl⟩
  have hx : ∀ i, x i = ∑ k, c i k ⊗ₜ[F] b k := by
    intro i
    conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr (x i)]
    simp [hc, TensorProduct.smul_tmul']
  simp only [hc]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun _ _ => rfl
  have hi : ∀ e : E, inclR (F := F) R e = (1 : R) ⊗ₜ[F] e := fun _ => rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qR, hR, Formalism.UG.hform, JR, Matrix.map_apply, hx, map_sum, hs, hi, Finset.sum_mul,
    Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, qloc_trace_tmul, dotProduct, Matrix.mulVec,
    Fintype.sum_prod_type, gram, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := Finset.univ (α := Fin d)) (t := Finset.univ (α := Fin M))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem qR_smul (c : R) (x : Fin M → R ⊗[F] E) : qR R σ J (c • x) = c ^ 2 * qR R σ J x := by
  rw [qR_eq σ (Module.finBasis F E), qR_eq σ (Module.finBasis F E)]
  simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply]
  change (c • _) ⬝ᵥ _ *ᵥ (c • _) = _
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, sq, mul_assoc]

end Gram

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {d M : ℕ} (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E)
  (v : HeightOneSpectrum (𝓞 F))

def coordLin : (Fin 1 → Fin M → Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin M × Fin d → Fv F v) where
  toFun X p := (Algebra.TensorProduct.basis (Fv F v) b).repr (X 0 p.1) p.2
  invFun y _ i := (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm fun k => y (i, k)
  map_add' X Y := by ext p; simp
  map_smul' c X := by ext p; simp
  left_inv X := by
    funext a i
    rw [Subsingleton.elim a 0]
    exact (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm_apply_apply (X 0 i)
  right_inv y := by
    funext p
    exact congrFun ((Algebra.TensorProduct.basis (Fv F v) b).equivFun.apply_symm_apply
      fun k => y (p.1, k)) p.2

def coord : (Fin 1 → Fin M → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin M × Fin d → Fv F v) :=
  { coordLin b v with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (coordLin (M := M) b v).toLinearMap
    continuous_invFun :=
      haveI := IsModuleTopology.toContinuousSMul (Fv F v) (Fv F v ⊗[F] E)
      IsModuleTopology.continuous_of_linearMap (coordLin (M := M) b v).symm.toLinearMap }

theorem latV_eq : (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) =
    {X | ∀ p, coord b v X p ∈ v.adicCompletionIntegers F} := by
  ext X
  exact ⟨fun h p => h 0 p.1 p.2, fun h a i k => by rw [Subsingleton.elim a 0]; exact h (i, k)⟩

theorem isOpen_latV : IsOpen (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) := by
  rw [latV_eq, Set.setOf_forall]
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  exact isOpen_iInter_of_finite fun p =>
    hO.preimage ((continuous_apply p).comp (coord b v).continuous)

theorem q_coord (X : Fin 1 → Fin M → Fv F v ⊗[F] E) : qR (Fv F v) σ J (X 0) =
    coord b v X ⬝ᵥ ((gram σ b J).map (algebraMap F (Fv F v))) *ᵥ coord b v X :=
  qR_eq σ b J _ _

theorem continuous_q :
    Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => qR (Fv F v) σ J (X 0) := by
  simp only [q_coord σ (Module.finBasis F E)]
  exact (coord _ v).continuous.dotProduct (continuous_const.matrix_mulVec (coord _ v).continuous)

theorem exists_sqrt (h2 : Valued.v (2 : Fv F v) = 1) (u : Fv F v) (hu : Valued.v (u - 1) < 1) :
    ∃ r : Fv F v, Valued.v r = 1 ∧ r * r = u := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have hu1 : Valued.v u = 1 := by
    have := Valuation.map_one_add_of_lt _ hu
    rwa [add_sub_cancel] at this
  obtain ⟨y, hy, hy0⟩ := (GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff v _).2 hu
  obtain ⟨s, hs⟩ := GlobalTheory.QuadFieldCriterion.exists_root_of_residual (0 : v.adicCompletionIntegers F)
    (-(1 + y)) (by
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      have : ((0 ^ 2 - 4 * -(1 + y) : v.adicCompletionIntegers F) : Fv F v) = 2 * 2 * u := by
        push_cast
        rw [← hy]
        have : ((4 : v.adicCompletionIntegers F) : Fv F v) = 4 := rfl
        rw [this]
        ring
      rw [this, map_mul, map_mul, h2, hu1, mul_one, mul_one]) 1 (by simp [hy0])
  have hs' : (s : Fv F v) * s = u := by
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) hs
    push_cast at this
    rw [← hy] at this
    linear_combination this
  refine ⟨s, ?_, hs'⟩
  have := congrArg Valued.v hs'
  rw [map_mul, hu1] at this
  exact (pow_eq_one_iff.1 (by rw [sq, this])).resolve_right two_ne_zero

theorem modu_unit (r : Fv F v) (hr : Valued.v r = 1) : modu (Fv F v) r = 1 := by
  have h0 : r ≠ 0 := by rintro rfl; simp at hr
  have h := GlobalTheory.GaugeProdFormula.modu_finite F v r h0
  have h1 : ‖r‖ = 1 := le_antisymm (Valued.toNormedField.norm_le_one_iff.2 hr.le)
    (Valued.toNormedField.one_le_norm_iff.2 hr.ge)
  rw [h1] at h
  exact_mod_cast h

theorem fib_const (hσ : IsCMExt F E σ) (h2 : Valued.v (2 : Fv F v) = 1)
    (lam : Measure (Fv F v ⊗[F] E)) (ν : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure)
    (hν : ν.IsAddHaarMeasure) (β c : Fv F v) (hβ : Valued.v β = 1) (hc : Valued.v (c - β) < 1)
    (m m' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : FibAt (Fv F v) σ J (tupMeas lam 1 M) ν β m)
    (hm' : FibAt (Fv F v) σ J (tupMeas lam 1 M) ν c m') : m' (latV b v) = m (latV b v) := by
  haveI := IsModuleTopology.toContinuousSMul (Fv F v) (Fv F v ⊗[F] E)
  have hβ0 : β ≠ 0 := by rintro rfl; simp at hβ
  obtain ⟨r, hr, hrr⟩ := exists_sqrt v h2 (c / β) (by
    rw [div_sub_one hβ0, map_div₀, hβ, div_one]; exact hc)
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  let g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E) := Matrix.diagonal fun _ => algebraMap _ _ r
  have hg : ∀ z, g *ᵥ z = r • z := fun z => by
    ext i
    simp [g, Matrix.mulVec_diagonal, Algebra.smul_def]
  have hd : g.det = algebraMap _ _ (r ^ M) := by simp [g]
  have hdu : IsUnit g.det := hd ▸ (pow_ne_zero M hr0).isUnit.map _
  have hN := (nice_ainf_fv F).2 v
  have ht := fibAt_similitude F E σ (Fv F v) hN M J J lam ν β (r * r) m g hl hν hdu
    (mul_ne_zero hr0 hr0).isUnit (fun z => by rw [hg, qR_smul, sq]) hm
  have hmd : modu (Fv F v ⊗[F] E) g.det = 1 := by
    rw [(modu_eq_modu_norm F E σ hσ (Fv F v) g.det (r ^ M * r ^ M) hdu (by
      rw [hd, map_mul]; congr 1; simp [sigR])).2]
    exact modu_unit v _ (by simp [hr])
  rw [hmd, modu_unit v _ (by simp [hr]), inv_one, mul_one, one_smul, hrr,
    div_mul_cancel₀ _ hβ0] at ht
  have hc0 : IsUnit c := by
    rw [← div_mul_cancel₀ c hβ0, ← hrr]
    exact (mul_ne_zero (mul_ne_zero hr0 hr0) hβ0).isUnit
  have hl : lrAct g (1 : Matrix (Fin 1) (Fin 1) _) = fun X => r • X := by
    funext X a
    rw [lrAct, hg, Subsingleton.elim a 0]
    ext i
    simp
  rw [← (FibBasic.fibAt_basic F E σ (Fv F v) hN M J _ ν c m' hν hc0 hm').2.2 _ ht, hl,
    Measure.map_apply (continuous_const_smul r).measurable (isOpen_latV b v).measurableSet]
  congr 1
  ext X
  simp only [latV_eq, Set.mem_preimage, Set.mem_setOf_eq, map_smul, Pi.smul_apply, smul_eq_mul,
    HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hr, one_mul]

theorem residue_eq_iff (x y : v.adicCompletionIntegers F) :
    IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔ Valued.v ((x : Fv F v) - y) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (Fv F v) _))

theorem isOpen_class (β : Fv F v) : IsOpen {c : Fv F v | Valued.v (c - β) < 1} :=
  (GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one v).preimage (continuous_id.sub continuous_const)

theorem vol_class (ν : Measure (Fv F v)) [ν.IsAddHaarMeasure]
    (hν : ν (v.adicCompletionIntegers F : Set (Fv F v)) = 1) (β : v.adicCompletionIntegers F) :
    ν.real {c | Valued.v (c - β) < 1} * (Ideal.absNorm v.asIdeal : ℝ) = 1 := by
  have h := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v (Fv F v) ν Unit
    (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm
    {fun _ => IsLocalRing.residue _ β}
  have e2 : {y : Fv F v | ∀ i, (ContinuousLinearEquiv.funUnique Unit (Fv F v) (Fv F v)).symm y i ∈
      v.adicCompletionIntegers F} = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp
  rw [e2, GlobalTheory.GaugeProdFormula.card_residue, Fintype.card_unit, pow_one, Set.ncard_singleton,
    measureReal_def (s := (v.adicCompletionIntegers F : Set (Fv F v))), hν] at h
  convert h using 3
  · ext c
    constructor
    · intro hc
      have hc1 : c ∈ v.adicCompletionIntegers F := by
        have := add_mem (show c - β ∈ v.adicCompletionIntegers F from
          (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_lt hc)) β.2
        rwa [sub_add_cancel] at this
      exact ⟨fun _ => ⟨c, hc1⟩, fun _ => rfl, funext fun _ => (residue_eq_iff v _ _).2 hc⟩
    · rintro ⟨y, h1, h2⟩
      have h3 : c = y () := h1 ()
      rw [h3]
      exact (residue_eq_iff v _ _).1 (congrFun h2 ())
  · simp

theorem vol_fibre (hσ : IsCMExt F E σ) (h2 : Valued.v (2 : Fv F v) = 1)
    (lam : Measure (Fv F v ⊗[F] E)) (ν : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure)
    (hν : ν.IsAddHaarMeasure) (β : Fv F v) (hβ : Valued.v β = 1)
    (m : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : FibAt (Fv F v) σ J (tupMeas lam 1 M) ν β m) :
    tupMeas lam 1 M (latV b v ∩ (fun X => qR (Fv F v) σ J (X 0)) ⁻¹' {c | Valued.v (c - β) < 1}) =
      m (latV b v) * ν {c | Valued.v (c - β) < 1} := by
  obtain ⟨fib, hf, -⟩ := id hm
  have hSm := (isOpen_class v β).measurableSet
  have hpm := (continuous_q σ J v).measurable hSm
  have hLm := (isOpen_latV (M := M) b v).measurableSet
  set S : Set (Fv F v) := {c | Valued.v (c - β) < 1} with hS
  have hfb : ∀ c, fib c (latV b v ∩ (fun X => qR (Fv F v) σ J (X 0)) ⁻¹' S) =
      S.indicator (fun _ => m (latV b v)) c := by
    intro c
    have hae : ∀ᵐ X ∂(fib c), qR (Fv F v) σ J (X 0) = c := by
      have := hf.1 c
      rw [Set.inter_univ] at this
      exact this
    by_cases hc : c ∈ S
    · rw [Set.indicator_of_mem hc,
        ← fib_const σ b J v hσ h2 lam ν hl hν β c hβ hc m (fib c) hm ⟨fib, hf, rfl⟩]
      refine measure_congr ?_
      filter_upwards [hae] with X hX
      exact ⟨fun h => h.1, fun h => ⟨h, show qR (Fv F v) σ J (X 0) ∈ S from hX ▸ hc⟩⟩
    · rw [Set.indicator_of_notMem hc]
      refine measure_mono_null ?_ hae
      intro X hX hX'
      have e : qR (Fv F v) σ J (X 0) = c := hX'
      exact hc (e ▸ hX.2)
  have := hf.2.1 ((latV b v ∩ (fun X => qR (Fv F v) σ J (X 0)) ⁻¹' S).indicator 1)
    (measurable_one.indicator (hLm.inter hpm))
  simp only [Measure.restrict_univ, lintegral_indicator_one (hLm.inter hpm), hfb] at this
  rw [this, lintegral_indicator hSm, setLIntegral_const]

theorem tupMeas_latV (lam : Measure (Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] (h : lam (intV b v) = 1) :
    tupMeas lam 1 M (latV b v) = 1 := by
  have e : (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) =
      Set.univ.pi fun _ => Set.univ.pi fun _ => intV b v := by
    ext X
    simp only [mem_latV_iff, Set.mem_pi, Set.mem_univ, true_implies]
  rw [e, tupMeas, Measure.pi_pi]
  simp [Measure.pi_pi, h]

theorem local_bound (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hM : 1 ≤ M)
    (h2 : Valued.v (2 : Fv F v) = 1)
    (hS : ∀ p q, algebraMap F (Fv F v) (gram σ b J p q) ∈ v.adicCompletionIntegers F)
    (hdet : Valued.v (algebraMap F (Fv F v) (gram σ b J).det) = 1)
    (lam : Measure (Fv F v ⊗[F] E)) (ν : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure)
    (hν : ν.IsAddHaarMeasure) (hl1 : lam (intV b v) = 1)
    (hν1 : ν (v.adicCompletionIntegers F : Set (Fv F v)) = 1) (β : Fv F v) (hβ : Valued.v β = 1)
    (m : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hm : FibAt (Fv F v) σ J (tupMeas lam 1 M) ν β m) :
    |(m (latV b v)).toReal - 1| * (Ideal.absNorm v.asIdeal : ℝ) ^ M ≤
      (Ideal.absNorm v.asIdeal : ℝ) := by
  classical
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  letI := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers F))
  have hd : d = 2 := by rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  haveI : (tupMeas lam 1 M).IsAddHaarMeasure := by
    haveI : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact Measure.pi.isAddHaarMeasure _
  let O := v.adicCompletionIntegers F
  let ρ := IsLocalRing.residue O
  let S₀ : Matrix (Fin M × Fin 2) (Fin M × Fin 2) O := Matrix.of fun p q => ⟨_, hS p q⟩
  let β₀ : O := ⟨β, hβ.le⟩
  have hS₀ : S₀.map O.subtype = (gram σ b J).map (algebraMap F (Fv F v)) := rfl
  have hunit : ∀ x : O, Valued.v (x : Fv F v) = 1 → ρ x ≠ 0 := fun x hx =>
    ((HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx).map ρ).ne_zero
  have hcount := GlobalTheory.QuadricCount.card_quadric_sub_sq_le _ _ (S₀.map ρ) (ρ β₀)
    (by have := hunit 2 h2; rwa [map_ofNat] at this)
    (by
      ext p q
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      congr 1
      exact Subtype.ext (congrArg (algebraMap F (Fv F v)) ((gram_symm σ b J hσ hJ).apply p q)))
    (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      refine hunit _ ?_
      rw [← hdet, RingHom.map_det, RingHom.mapMatrix_apply, ← hS₀, ← RingHom.mapMatrix_apply,
        ← RingHom.map_det]
      rfl)
  have hbox := GlobalTheory.ResidueBoxVolume.measureReal_residueBox F v _ (tupMeas lam 1 M) _ (coord b v)
    {x | x ⬝ᵥ (S₀.map ρ) *ᵥ x = ρ β₀}
  have key : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (y : Fin M × Fin 2 → O),
      (∀ i, coord b v X i = (y i : Fv F v)) →
      ((fun i => ρ (y i)) ⬝ᵥ (S₀.map ρ) *ᵥ (fun i => ρ (y i)) = ρ β₀ ↔
        Valued.v (qR (Fv F v) σ J (X 0) - β) < 1) := by
    intro X y hy
    have e1 : (fun i => ρ (y i)) ⬝ᵥ (S₀.map ρ) *ᵥ (fun i => ρ (y i)) = ρ (y ⬝ᵥ S₀ *ᵥ y) := by
      simp [dotProduct, Matrix.mulVec]
    have e2 : qR (Fv F v) σ J (X 0) = O.subtype (y ⬝ᵥ S₀ *ᵥ y) := by
      rw [q_coord σ b, ← hS₀]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hy, Matrix.map_apply]
      rfl
    rw [e1, e2, residue_eq_iff]
    rfl
  have hset : {X | ∃ y : Fin M × Fin 2 → O, (∀ i, coord b v X i = (y i : Fv F v)) ∧
      (fun i => ρ (y i)) ∈ {x | x ⬝ᵥ (S₀.map ρ) *ᵥ x = ρ β₀}} =
      latV b v ∩ (fun X => qR (Fv F v) σ J (X 0)) ⁻¹' {c | Valued.v (c - β) < 1} := by
    rw [latV_eq]
    ext X
    constructor
    · rintro ⟨y, h1, h3⟩
      exact ⟨fun i => h1 i ▸ (y i).2, (key X y h1).1 h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨fun i => ⟨_, h1 i⟩, fun _ => rfl, (key X (fun i => ⟨_, h1 i⟩) fun _ => rfl).2 h3⟩
  rw [hset, ← latV_eq, measureReal_def, measureReal_def, tupMeas_latV b v lam hl1,
    vol_fibre σ b J v hσ h2 lam ν hl hν β hβ m hm, ENNReal.toReal_mul, ENNReal.toReal_one, mul_one,
    GlobalTheory.GaugeProdFormula.card_residue, Set.ncard_eq_toFinset_card', Set.toFinset_setOf] at hbox
  have hv := vol_class v ν hν1 β₀
  rw [← Nat.card_eq_fintype_card, GlobalTheory.GaugeProdFormula.card_residue, ← hbox] at hcount
  have hq : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  have hcard : Fintype.card (Fin (n + 1) × Fin 2) = 2 * n + 1 + 1 := by simp; ring
  rw [hcard, Nat.add_sub_cancel] at hcount
  change (ν {c | Valued.v (c - β) < 1}).toReal * _ = 1 at hv
  generalize (ν {c | Valued.v (c - β) < 1}).toReal = t at hv hcount
  generalize (m (latV b v)).toReal = a at hcount ⊢
  generalize (Ideal.absNorm v.asIdeal : ℝ) = q at hq hv hcount ⊢
  have e : (a * t * q ^ (2 * n + 1 + 1) - q ^ (2 * n + 1)) ^ 2 =
      (|a - 1| * q ^ (n + 1)) ^ 2 * q ^ (2 * n) := by
    rw [mul_pow, sq_abs]
    have : a * t * q ^ (2 * n + 1 + 1) = a * q ^ (2 * n + 1) := by
      rw [pow_succ q (2 * n + 1)]; linear_combination a * q ^ (2 * n + 1) * hv
    rw [this]
    ring
  rw [e, show q ^ (2 * n + 1 + 1) = q ^ 2 * q ^ (2 * n) by ring] at hcount
  exact (pow_le_pow_iff_left₀ (by positivity) hq.le two_ne_zero).1
    (le_of_mul_le_mul_right hcount (by positivity))

end Local

theorem eventually_valued_eq_one {F : Type} [Field F] [NumberField F] {x : F} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 :=
    GlobalTheory.QNorm.finite_valuation_ne_one F (Units.mk0 x hx)
  filter_upwards [h] with v hv
  rw [← hv]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem eventually_mem {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  by_cases hx : x = 0
  · exact Filter.Eventually.of_forall fun v => by rw [hx, map_zero]; exact zero_mem _
  · exact (eventually_valued_eq_one hx).mono fun v hv => hv.le

theorem local_density_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 1 ≤ M → IsHermND σ J → β ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F (Fv F v) β) m → |(m (latV b v)).toReal - 1| * (Ideal.absNorm v.asIdeal : ℝ) ^ M ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  intro F E _ _ _ _ _ σ hσ d b s M J β hM hJ hβ
  filter_upwards [eventually_valued_eq_one (two_ne_zero (α := F)),
    eventually_valued_eq_one (gram_det σ b J hσ hJ), eventually_valued_eq_one hβ,
    Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun q =>
      eventually_mem (gram σ b J p q)] with v h2 hdet hβ' hS m hm
  rw [map_ofNat] at h2
  exact local_bound σ b J v hσ hJ hM h2 hS hdet _ _ (s.haar_lamV v) (s.haar_nuV v) (s.lamV_int v)
    (s.nuV_int v) _ hβ' m hm

end GlobalTheory.GaugeDensity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBoundStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_localDensity_standardLattice_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 1 ≤ M → IsHermND σ J → β ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F (Fv F v) β) m → |(m (latV b v)).toReal - 1| * (Ideal.absNorm v.asIdeal : ℝ) ^ M ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.GaugeDensity.local_density_bound | exact GlobalTheory.GaugeDensity.local_density_bound | (intros; apply GlobalTheory.GaugeDensity.local_density_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasure
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedProductMeasureCountable
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedProductMeasureCountable
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.AbsProd

theorem lintegral_prod_infinitePi {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (P : ∀ i, Measure (V i)) [∀ i, IsProbabilityMeasure (P i)] (S : Finset ι)
    (f : ∀ i, V i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂(Measure.infinitePi P) = ∏ i ∈ S, ∫⁻ y, f i y ∂(P i) := by
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun S (fun i (Y : ∀ i, V i) => f i (Y i))
    (ProbabilityTheory.iIndepFun_infinitePi (P := P) hf)
    (fun i => (hf i).comp (measurable_pi_apply i))]
  exact Finset.prod_congr rfl fun i _ =>
    (measurePreserving_eval_infinitePi P i).lintegral_comp (hf i)

theorem tail_split {ι : Type} [DecidableEq ι] (c : ι → ℝ) (hs : Summable fun i => |c i - 1|)
    {T S : Finset ι} (h : T ⊆ S) :
    ∏' i : {i : ι // i ∉ T}, c i.1 = (∏ i ∈ S \ T, c i) * ∏' i : {i : ι // i ∉ S}, c i.1 := by
  have key : ∀ U : Finset ι, ∏' i : {i : ι // i ∉ U}, c i.1 = ∏' i, (if i ∈ U then 1 else c i) := by
    intro U
    have := tprod_subtype {i | i ∉ U} c
    refine this.trans (tprod_congr fun i => ?_)
    by_cases hi : i ∈ U <;> simp [Set.mulIndicator, hi]
  have hm : Multipliable fun i => (if i ∈ S then 1 else c i) := by
    have h1 : Summable fun i => (if i ∈ S then (0 : ℝ) else c i - 1) := by
      refine Summable.of_norm_bounded hs fun i => ?_
      by_cases hi : i ∈ S <;> simp [hi]
    refine (Real.multipliable_one_add_of_summable h1).congr fun i => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  have hf : HasProd (fun i => if i ∈ S \ T then c i else 1) (∏ i ∈ S \ T, c i) := by
    have := hasProd_prod_of_ne_finset_one (f := fun i => if i ∈ S \ T then c i else 1)
      (s := S \ T) (L := SummationFilter.unconditional ι) (fun b hb => if_neg hb)
    rwa [Finset.prod_congr rfl (fun i hi => if_pos hi)] at this
  rw [key, key, ← hf.tprod_eq, ← hf.multipliable.tprod_mul hm]
  refine tprod_congr fun i => ?_
  by_cases hT : i ∈ T
  · simp [hT, h hT]
  · by_cases hS : i ∈ S <;> simp [hT, hS]

theorem exists_piece {ι : Type} {V : ι → Type} [∀ i, MeasurableSpace (V i)]
    (a : ∀ i, Measure (V i)) (hσ : ∀ i, SigmaFinite (a i)) (T : Finset ι) (c : ι → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hs : Summable fun i => |c i - 1|)
    (ha : ∀ i ∉ T, a i Set.univ = ENNReal.ofReal (c i)) :
    ∃ ν : Measure (∀ i, V i), SFinite ν ∧ ∀ S : Finset ι, T ⊆ S → ∀ f : ∀ i, V i → ℝ≥0∞,
      (∀ i, Measurable (f i)) → ∫⁻ Y, ∏ i ∈ S, f i (Y i) ∂ν =
        (∏ i ∈ S, ∫⁻ y, f i y ∂(a i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, c i.1) := by
  classical
  by_cases h0 : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, inferInstance, fun S hS f _ => ?_⟩
    rw [lintegral_zero_measure]
    by_cases hiS : i ∈ S
    · rw [Finset.prod_eq_zero hiS (by simp [hi]), zero_mul]
    · have h1 := ha i (fun h => hiS (hS h))
      have h2 : c i = 0 := by
        rw [hi] at h1
        exact le_antisymm (ENNReal.ofReal_eq_zero.1 h1.symm) (hc0 i)
      rw [tail_split c hs (Finset.subset_insert i S),
        Finset.prod_eq_zero (s := insert i S \ S) (i := i) (by simp [hiS]) h2]
      simp
  push Not at h0
  have hP : ∀ i, ∃ (P : Measure (V i)) (g : V i → ℝ≥0∞), IsProbabilityMeasure P ∧ Measurable g ∧
      (i ∉ T → ∀ y, g y = 1) ∧ ∀ f : V i → ℝ≥0∞, Measurable f →
        ∫⁻ y, f y ∂(a i) = (if i ∈ T then 1 else ENNReal.ofReal (c i)) * ∫⁻ y, g y * f y ∂P := by
    intro i
    haveI : NeZero (a i) := ⟨h0 i⟩
    by_cases hi : i ∈ T
    · refine ⟨(a i).toFinite, (a i).rnDeriv (a i).toFinite, inferInstance,
        Measure.measurable_rnDeriv _ _, fun h => (h hi).elim, fun f hf => ?_⟩
      rw [if_pos hi, one_mul]
      conv_lhs => rw [← Measure.withDensity_rnDeriv_eq (a i) (a i).toFinite
        (absolutelyContinuous_toFinite _)]
      rw [lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hf]
      rfl
    · haveI : IsFiniteMeasure (a i) := ⟨by rw [ha i hi]; exact ENNReal.ofReal_lt_top⟩
      refine ⟨(a i Set.univ)⁻¹ • a i, fun _ => 1, inferInstance, measurable_const,
        fun _ _ => rfl, fun f _ => ?_⟩
      rw [if_neg hi, ← ha i hi, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simpa using h0 i) (measure_ne_top _ _)]
      simp
  choose P g hP hg hg1 hint using hP
  have hG : Measurable fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i) :=
    (Finset.measurable_prod _ fun i _ => (hg i).comp (measurable_pi_apply i)).const_mul _
  refine ⟨(Measure.infinitePi P).withDensity
    (fun Y => ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)),
    inferInstance, fun S hS f hf => ?_⟩
  have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
    Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
  rw [lintegral_withDensity_eq_lintegral_mul _ hG hF]
  have h1 : ∀ Y : ∀ i, V i, ((fun Y : ∀ i, V i =>
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ T, g i (Y i)) *
      fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i)) Y =
      ENNReal.ofReal (∏' i : {i : ι // i ∉ T}, c i.1) * ∏ i ∈ S, (g i (Y i) * f i (Y i)) := by
    intro Y
    rw [Pi.mul_apply, Finset.prod_mul_distrib, mul_assoc,
      Finset.prod_subset hS (fun i _ hi => hg1 i hi (Y i))]
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_prod_infinitePi P S (fun i y => g i y * f i y) (fun i => (hg i).mul (hf i)),
    Finset.prod_congr rfl (fun i _ => hint i (f i) (hf i)), Finset.prod_mul_distrib,
    tail_split c hs hS, ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hc0 i),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => hc0 i)]
  have h2 : ∏ i ∈ S, (if i ∈ T then 1 else ENNReal.ofReal (c i)) =
      ∏ i ∈ S \ T, ENNReal.ofReal (c i) := by
    rw [← Finset.prod_subset (Finset.sdiff_subset (s := S) (t := T))
      (fun i hi hi' => if_pos (by simpa [hi] using hi'))]
    exact Finset.prod_congr rfl fun i hi => if_neg (Finset.mem_sdiff.1 hi).2
  rw [h2]
  ring

theorem exists_restricted_product : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  intro ι _ V₀ _ V _ L m₀ m h₀ hm hL hfin hs
  classical
  let a : Finset ι → ∀ i, Measure (V i) := fun T i =>
    (m i).restrict (if i ∈ T then (L i)ᶜ else L i)
  have hex := fun T : Finset ι => exists_piece (a T) (fun i => by dsimp only [a]; infer_instance) T
    (fun i => (m i (L i)).toReal) (fun i => ENNReal.toReal_nonneg) hs
    (fun i hi => by simp [a, hi, ENNReal.ofReal_toReal (hfin i)])
  choose ν hν hint using hex
  have hnull : ∀ (T : Finset ι) (i : ι) (N : Set (V i)), MeasurableSet N → a T i N = 0 →
      ν T {Y | Y i ∈ N} = 0 := by
    intro T i N hN h
    have hm' : ∀ j, Measurable (Function.update (fun j (_ : V j) => (1 : ℝ≥0∞)) i
        (N.indicator 1) j) := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self]
        exact measurable_const.indicator hN
      · rw [Function.update_of_ne hj]
        exact measurable_const
    have h1 := hint T (insert i T) (Finset.subset_insert i T) _ hm'
    rw [Finset.prod_eq_zero (Finset.mem_insert_self i T)
      (by rw [Function.update_self, lintegral_indicator_one hN, h]), zero_mul] at h1
    have hN' : MeasurableSet {Y : ∀ i, V i | Y i ∈ N} := measurable_pi_apply i hN
    rw [← lintegral_indicator_one hN', ← h1]
    refine lintegral_congr fun Y => ?_
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Function.update_of_ne hj])
      (fun h => (h (Finset.mem_insert_self i T)).elim), Function.update_self]
    rfl
  let B : Finset ι → Set (∀ i, V i) := fun S => {Y | ∀ i ∉ S, Y i ∈ L i}
  have hB : ∀ S, MeasurableSet (B S) := by
    intro S
    have : B S = ⋂ i, ⋂ (_ : i ∉ S), {Y | Y i ∈ L i} := by ext; simp [B]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurable_pi_apply i (hL i)
  have hin : ∀ T S : Finset ι, T ⊆ S → ν T (B S)ᶜ = 0 := by
    intro T S h
    have : (B S)ᶜ = ⋃ i, ⋃ (_ : i ∉ S), {Y | Y i ∈ (L i)ᶜ} := by ext; simp [B]
    rw [this]
    refine measure_iUnion_null fun i => measure_iUnion_null fun hi => hnull T i _ (hL i).compl ?_
    have hT : i ∉ T := fun h' => hi (h h')
    simp [a, hT, Measure.restrict_apply (hL i).compl]
  have hout : ∀ T S : Finset ι, ¬ T ⊆ S → ν T (B S) = 0 := by
    intro T S h
    obtain ⟨i, hT, hS⟩ := Finset.not_subset.1 h
    refine measure_mono_null (t := {Y | Y i ∈ L i}) (fun Y hY => hY i hS) (hnull T i _ (hL i) ?_)
    simp [a, hT, Measure.restrict_apply (hL i)]
  refine ⟨m₀.prod (Measure.sum ν), ?_, fun S f₀ f hf₀ hf => ?_⟩
  · refine measure_mono_null (t := Set.univ ×ˢ ⋂ S, (B S)ᶜ) (fun Y hY => ?_) ?_
    · refine ⟨trivial, Set.mem_iInter.2 fun S hS => hY ?_⟩
      exact S.eventually_cofinite_notMem.mono fun i hi => hS i hi
    · rw [Measure.prod_prod, Measure.sum_apply_eq_zero.2
        (fun T => measure_mono_null (Set.iInter_subset _ T) (hin T T subset_rfl)), mul_zero]
  · have hF : Measurable fun Y : ∀ i, V i => ∏ i ∈ S, f i (Y i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    have e : {Y : V₀ × ∀ i, V i | ∀ i ∉ S, Y.2 i ∈ L i} = Set.univ ×ˢ B S := by ext; simp [B]
    rw [e, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod_mul hf₀.aemeasurable hF.aemeasurable, mul_assoc]
    congr 1
    rw [Measure.restrict_sum _ (hB S), lintegral_sum_measure,
      tsum_eq_sum (s := S.powerset) (fun T hT => by
        rw [Measure.restrict_eq_zero.2 (hout T S (by simpa using hT)), lintegral_zero_measure])]
    have h1 : ∀ i ∈ S, ∫⁻ y, f i y ∂(m i) =
        ∫⁻ y in (L i)ᶜ, f i y ∂(m i) + ∫⁻ y in L i, f i y ∂(m i) := fun i _ => by
      rw [add_comm, lintegral_add_compl _ (hL i)]
    rw [Finset.prod_congr rfl h1, Finset.prod_add, Finset.sum_mul]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hTS : T ⊆ S := Finset.mem_powerset.1 hT
    rw [Measure.restrict_eq_self_of_ae_mem (s := B S) (hin T S hTS), hint T S hTS f hf,
      ← Finset.prod_sdiff hTS, mul_comm (∏ i ∈ S \ T, _)]
    congr 2
    · exact Finset.prod_congr rfl fun i hi => by simp [a, hi]
    · exact Finset.prod_congr rfl fun i hi => by simp [a, (Finset.mem_sdiff.1 hi).2]

end GlobalTheory.GaugeEx.AbsProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRestrictedProductMeasureCountableStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_restricted_product_measure_countable : ∀ (ι : Type) [Countable ι] (V₀ : Type) [MeasurableSpace V₀] (V : ι → Type) [∀ i, MeasurableSpace (V i)] (L : ∀ i, Set (V i)) (m₀ : Measure V₀) (m : ∀ i, Measure (V i)), SigmaFinite m₀ → (∀ i, SigmaFinite (m i)) → (∀ i, MeasurableSet (L i)) → (∀ i, m i (L i) ≠ ∞) → (Summable fun i => |(m i (L i)).toReal - 1|) → ∃ ν : Measure (V₀ × ∀ i, V i), ν {Y | ¬ ∀ᶠ i in Filter.cofinite, Y.2 i ∈ L i} = 0 ∧ ∀ (S : Finset ι) (f₀ : V₀ → ℝ≥0∞) (f : ∀ i, V i → ℝ≥0∞), Measurable f₀ → (∀ i, Measurable (f i)) → ∫⁻ Y in {Y | ∀ i ∉ S, Y.2 i ∈ L i}, f₀ Y.1 * ∏ i ∈ S, f i (Y.2 i) ∂ν = (∫⁻ y, f₀ y ∂m₀) * (∏ i ∈ S, ∫⁻ y, f i y ∂(m i)) * ENNReal.ofReal (∏' i : {i : ι // i ∉ S}, (m i.1 (L i.1)).toReal) := by
  first | exact @GlobalTheory.GaugeEx.AbsProd.exists_restricted_product | exact GlobalTheory.GaugeEx.AbsProd.exists_restricted_product | (intros; apply GlobalTheory.GaugeEx.AbsProd.exists_restricted_product <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasure
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem exists_isProd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), Conv b mi mv → ∃ ν, IsProd b ν mi mv := by
  intro F E _ _ _ _ _ d b n M mi mv hc
  obtain ⟨hi, hv, hs⟩ := hc
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  haveI : Countable (𝓞 F) := Countable.of_equiv _ (RingOfIntegers.basis F).equivFun.symm.toEquiv
  haveI : Countable (Ideal (𝓞 F)) := by
    have hsurj : Function.Surjective (fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) :=
      fun I => (IsNoetherian.noetherian I)
    exact hsurj.countable
  haveI : Countable (HeightOneSpectrum (𝓞 F)) :=
    Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
      (fun _ _ h => HeightOneSpectrum.ext h)
  obtain ⟨hint, -⟩ := GlobalTheory.T.integralPointsFinitePlaceTensor_properties F E (AlgHom.id F E) d b
  obtain ⟨hemb, hrange, -, -⟩ := GlobalTheory.T.measurableEmbedding_adelicTuple_localComponents F E d b n M
  have hlat : ∀ v, (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) =
      Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => intV b v := by
    intro v
    ext Y
    rw [mem_latV_iff]
    simp
  have hcpt : ∀ v, IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => (hint v).1
  have hmeas : ∀ v, MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
    intro v
    rw [hlat]
    exact MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ => (hint v).2.measurableSet
  have hsi : SigmaFinite mi := inferInstance
  have hsv : ∀ v, SigmaFinite (mv v) := fun v => by
    haveI := hv v
    infer_instance
  obtain ⟨ν, hν0, hν⟩ := GlobalTheory.T.exists_restricted_product_measure_countable (HeightOneSpectrum (𝓞 F)) _ _ (fun v => latV b v) mi mv hsi hsv hmeas
    (fun v => by haveI := hv v; exact (hcpt v).measure_lt_top.ne) hs
  set e := (fun X : (Fin n → Fin M → AF F ⊗[F] E) =>
    (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) with he
  have hmap : (ν.comap e).map e = ν := by
    rw [hemb.map_comap, hrange]
    exact Measure.restrict_eq_self_of_ae_mem hν0
  refine ⟨ν.comap e, ⟨hi, hv, hs⟩, fun S fi fv hfi hfv => ?_⟩
  have h := hν S fi fv hfi hfv
  rw [← hmap, hemb.restrict_map, hemb.lintegral_map] at h
  exact h

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRestrictedProductTupleMeasureStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isRestrictedProductTupleMeasure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), Conv b mi mv → ∃ ν, IsProd b ν mi mv := by
  first | exact @GlobalTheory.GaugeEx.exists_isProd | exact GlobalTheory.GaugeEx.exists_isProd | (intros; apply GlobalTheory.GaugeEx.exists_isProd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThre
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isAddHaarMeasure_tupMeas_of_lc {S : Type} [AddCommGroup S] [TopologicalSpace S]
    [IsTopologicalAddGroup S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S] (lam : Measure S) (h : lam.IsAddHaarMeasure) (n M : ℕ) :
    (tupMeas lam n M).IsAddHaarMeasure := by
  unfold tupMeas
  haveI : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := inferInstance
  infer_instance

theorem setOf_isUnit_ainf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine (Pi.isUnit_iff (x := c)).trans (forall_congr' fun w => isUnit_iff_ne_zero)

theorem existsUnique_isStdX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 3 ≤ M → IsHermND σ J → β ≠ 0 → ∃! ν, IsStdX s σ J β ν := by
  intro F E _ _ _ _ _ σ hσ d b s M J β hM hJ hβ
  have hM1 : 1 ≤ M := by omega
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have uI : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have uV : ∀ v, IsUnit (algebraMap F (Fv F v) β) := fun v => (isUnit_iff_ne_zero.2 hβ).map _
  have bI := fun m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Ainf F) nI M J (tupMeas s.lamI 1 M) s.nuI _ m s.haar_nuI uI
  have bV := fun v m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Fv F v) (nV v) M J (tupMeas (s.lamV v) 1 M) (s.nuV v) _ m
    (s.haar_nuV v) (uV v)
  obtain ⟨mi, hmi⟩ : ∃ mi, FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi := by
    obtain ⟨fib, hfib⟩ := GlobalTheory.T.exists_fibreFamily_hermitianLength_infiniteAdeles F E σ hσ M J (tupMeas s.lamI 1 M) s.nuI hM1 hJ
      (isAddHaarMeasure_tupMeas_of_lc _ s.haar_lamI 1 M) s.haar_nuI
    exact ⟨_, fib, by rw [setOf_isUnit_ainf]; exact hfib, rfl⟩
  have hex : ∀ v, ∃ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) m := by
    intro v
    obtain ⟨-, fib, hfib⟩ := GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM1 hJ
      (tupMeas (s.lamV v) 1 M) (isAddHaarMeasure_tupMeas_of_lc _ (s.haar_lamV v) 1 M) (s.nuV v)
      (s.haar_nuV v)
    refine ⟨_, fib, ?_, rfl⟩
    simp only [isUnit_iff_ne_zero]
    exact hfib
  choose mv hmv using hex
  have hconv : Conv b mi mv := by
    refine ⟨(bI mi hmi).2.1, fun v => (bV v _ (hmv v)).2.1, ?_⟩
    have hs := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).2
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [GlobalTheory.T.eventually_localDensity_standardLattice_bound F E σ hσ d b s M J β hM1 hJ hβ] with v hv
    have h := hv _ (hmv v)
    have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
    set a : ℝ := |(mv v (latV b v)).toReal - 1|
    have ha : 0 ≤ a := abs_nonneg _
    have hq0 : 0 < q := by linarith
    have h3 : a * q ^ 3 ≤ q := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hM) ha).trans h
    have h2 : a * q ^ 2 ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hq0
      calc a * q ^ 2 * q = a * q ^ 3 := by ring
        _ ≤ 1 * q := by rw [one_mul]; exact h3
    rw [Real.norm_of_nonneg ha, Real.rpow_neg hq0.le, Real.rpow_two, ← one_div,
      le_div_iff₀ (by positivity)]
    exact h2
  obtain ⟨ν, hν⟩ := GlobalTheory.T.exists_isRestrictedProductTupleMeasure F E d b 1 M mi mv hconv
  refine ⟨ν, ⟨mi, mv, hmi, hmv, hν⟩, ?_⟩
  rintro ν' ⟨mi', mv', hmi', hmv', hν'⟩
  obtain rfl : mi' = mi := (bI mi hmi).2.2 _ hmi'
  obtain rfl : mv' = mv := funext fun v => (bV v _ (hmv v)).2.2 _ (hmv' v)
  exact (GlobalTheory.T.restrictedProductMeasure_basic_properties F E d b 1 M ν _ _ hν).2.2.1 _ hν'

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThreStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 3 ≤ M → IsHermND σ J → β ≠ 0 → ∃! ν, IsStdX s σ J β ν := by
  first | exact @GlobalTheory.GaugeEx.existsUnique_isStdX | exact GlobalTheory.GaugeEx.existsUnique_isStdX | (intros; apply GlobalTheory.GaugeEx.existsUnique_isStdX <;> assumption)
end
