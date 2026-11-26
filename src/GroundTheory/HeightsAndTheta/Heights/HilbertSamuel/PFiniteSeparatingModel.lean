module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUnitApprox
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

namespace FiniteSeparatingModel

variable {σ : Type} {e : ℕ}

theorem aeval_eval₂ (ℓ : Fin e → MvPolynomial σ ℚ) (Q : Polynomial (MvPolynomial (Fin e) ℚ))
    (g : MvPolynomial σ ℚ) (z : σ → ℂ) :
    aeval z (Q.eval₂ (aeval ℓ).toRingHom g) =
      Q.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z g) := by
  have hc : (aeval (R := ℚ) z).toRingHom.comp (aeval (R := ℚ) ℓ).toRingHom =
      (aeval fun j => aeval z (ℓ j)).toRingHom := by
    apply MvPolynomial.ringHom_ext <;> intro <;> simp
  have := Polynomial.hom_eval₂ Q (aeval (R := ℚ) ℓ).toRingHom (aeval (R := ℚ) z).toRingHom g
  rw [hc] at this
  exact this

theorem exists_monic_coeff_zero_ne {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) {f : MvPolynomial σ ℚ} (hf : f ∉ P)
    {p : Polynomial (MvPolynomial (Fin e) ℚ)} (hp : p.Monic) (hpf : p.eval₂ (aeval ℓ).toRingHom f ∈ P) :
    ∃ q : Polynomial (MvPolynomial (Fin e) ℚ),
      q.Monic ∧ q.eval₂ (aeval ℓ).toRingHom f ∈ P ∧ q.coeff 0 ≠ 0 := by
  obtain ⟨q, hpq, hdvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hdvd
  refine ⟨q, ?_, ?_, fun h => hdvd (Polynomial.X_dvd_iff.mpr h)⟩
  · rw [hpq] at hp
    exact (Polynomial.monic_X.pow _).of_mul_monic_left hp
  · rw [hpq, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow] at hpf
    exact (hP.mem_or_mem hpf).resolve_left fun h => hf (hP.mem_of_pow_mem _ h)


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_minpoly {P : Ideal (MvPolynomial σ ℚ)} (hP : P.IsPrime)
    (ℓ : Fin e → MvPolynomial σ ℚ) (hinj : ∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0)
    (hint : ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) (u : MvPolynomial σ ℚ) :
    ∃ G : Polynomial (MvPolynomial (Fin e) ℚ), G.Monic ∧ G.eval₂ (aeval ℓ).toRingHom u ∈ P ∧
      ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q := by
  let φ : MvPolynomial (Fin e) ℚ →+* MvPolynomial σ ℚ ⧸ P :=
    (Ideal.Quotient.mk P).comp (aeval ℓ).toRingHom
  let _ : Algebra (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) := φ.toAlgebra
  have key : ∀ Q : Polynomial (MvPolynomial (Fin e) ℚ),
      Polynomial.aeval (Ideal.Quotient.mk P u) Q = Ideal.Quotient.mk P (Q.eval₂ (aeval ℓ).toRingHom u) :=
    fun Q => by rw [Polynomial.aeval_def, Polynomial.hom_eval₂]; rfl
  have hφ : Function.Injective (algebraMap (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    exact hinj q (Ideal.Quotient.eq_zero_iff_mem.mp hq)
  have : Module.IsTorsionFree (MvPolynomial (Fin e) ℚ) (MvPolynomial σ ℚ ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  obtain ⟨p, hpm, hp⟩ := hint u
  have hu : IsIntegral (MvPolynomial (Fin e) ℚ) (Ideal.Quotient.mk P u) :=
    ⟨p, hpm, by rw [← Polynomial.aeval_def, key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hp⟩
  refine ⟨minpoly _ (Ideal.Quotient.mk P u), minpoly.monic hu, ?_, fun Q hQ => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← key]
    exact minpoly.aeval _ _
  · exact minpoly.isIntegrallyClosed_dvd hu (by rw [key]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ)

theorem exists_separating [Fintype σ] (S : Finset (σ → ℂ)) (x : σ → ℂ) :
    ∃ u : MvPolynomial σ ℚ, ∀ z ∈ S, aeval z u = aeval x u → z = x := by
  classical
  let k : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let q : (σ → ℂ) → Polynomial ℂ :=
    fun z => ∑ i, Polynomial.C (z i - x i) * Polynomial.X ^ (k i : ℕ)
  have hq : ∀ z, z ≠ x → q z ≠ 0 := by
    intro z hz h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
    have h1 := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r (k i : ℕ)) h
    simp only [q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at h1
    rw [Finset.sum_eq_single i] at h1
    · rw [if_pos rfl] at h1
      exact hi (sub_eq_zero.mp h1)
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (k.injective (Fin.ext h'.symm))
    · simp
  let Q : Polynomial ℂ := ∏ z ∈ S.erase x, q z
  have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun z hz => hq z (Finset.ne_of_mem_erase hz)
  obtain ⟨c, hc⟩ : ∃ c : ℚ, Q.eval (c : ℂ) ≠ 0 := by
    by_contra h
    push Not at h
    apply Set.infinite_range_of_injective (Rat.cast_injective (α := ℂ))
    refine (Q.roots.toFinset.finite_toSet).subset ?_
    rintro _ ⟨c, rfl⟩
    simp [Polynomial.mem_roots hQ, h c]
  refine ⟨∑ i, C (c ^ (k i : ℕ)) * X i, fun z hz hzu => ?_⟩
  by_contra hzx
  have hev : aeval z (∑ i, C (c ^ (k i : ℕ)) * X i) - aeval x (∑ i, C (c ^ (k i : ℕ)) * X i) =
      (q z).eval (c : ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, aeval_C, aeval_X, q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    push_cast
    ring
  rw [hzu, sub_self] at hev
  rw [Polynomial.eval_prod] at hc
  exact Finset.prod_ne_zero_iff.mp hc z (Finset.mem_erase.mpr ⟨hzx, hz⟩) hev.symm

end FiniteSeparatingModel

theorem FiniteSeparatingModel.proof (hN : NoetherProjection.Statement)
    (hL : RootsLiftToZeros.Statement) : FiniteSeparatingModel.Statement := by
  classical
  intro σ _ P f x hP hf _
  obtain ⟨e, ℓ, hinj, hint⟩ := hN σ P hP.ne_top
  choose p hpm hp using hint
  let yx : Fin e → ℂ := fun j => aeval x (ℓ j)
  let S : Finset (σ → ℂ) := Fintype.piFinset fun i =>
    ((p (X i)).map (aeval yx).toRingHom).roots.toFinset
  have hS : ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) → (fun j => aeval z (ℓ j)) = yx → z ∈ S := by
    intro z hz hzl
    rw [Fintype.mem_piFinset]
    intro i
    rw [Multiset.mem_toFinset, Polynomial.mem_roots ((hpm _).map _).ne_zero, Polynomial.IsRoot,
      Polynomial.eval_map, ← hzl]
    have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  obtain ⟨u, hu⟩ := FiniteSeparatingModel.exists_separating S x
  obtain ⟨G, hGm, hGu, hGdvd⟩ :=
    FiniteSeparatingModel.exists_minpoly hP ℓ hinj (fun g => ⟨p g, hpm g, hp g⟩) u
  obtain ⟨q, -, hqf, hq0⟩ :=
    FiniteSeparatingModel.exists_monic_coeff_zero_ne hP ℓ hf (hpm f) (hp f)
  refine ⟨e, ℓ, u, G, q.coeff 0, 1, hGm, hq0, one_ne_zero,
    fun i => ⟨p (X i), hpm _, fun z hz => ?_⟩, fun z hz => ?_, fun z hz hc hfz => ?_,
    fun y t _ ht => hL σ P e ℓ u G (fun g => ⟨p g, hpm g, hp g⟩) hGdvd y t ht,
    fun z hz hzl hzu => hu z (hS z hz hzl) hzu⟩
  · have := hz _ (hp (X i))
    rwa [FiniteSeparatingModel.aeval_eval₂, aeval_X] at this
  · have := hz _ hGu
    rwa [FiniteSeparatingModel.aeval_eval₂] at this
  · apply hc
    have := hz _ hqf
    rw [FiniteSeparatingModel.aeval_eval₂, hfz, Polynomial.eval₂_at_zero] at this
    exact this

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial TensorProduct

noncomputable section

theorem IndependentModBaseChange.proof : IndependentModBaseChange.Statement := by
  intro σ P r g hg
  let θ : MvPolynomial σ ℂ →ₐ[ℂ] ℂ ⊗[ℤ] (MvPolynomial σ ℤ ⧸ P) :=
    (Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)).comp
      (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm.toAlgHom
  have hθ : ∀ p : MvPolynomial σ ℤ,
      θ (MvPolynomial.map (Int.castRingHom ℂ) p) = (1 : ℂ) ⊗ₜ Ideal.Quotient.mk P p := by
    intro p
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) p =
        MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p) := by
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
      congr 1
    rw [h1]
    change Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (Ideal.Quotient.mkₐ ℤ P)
      ((MvPolynomial.algebraTensorAlgEquiv ℤ ℂ).symm (MvPolynomial.algebraTensorAlgEquiv ℤ ℂ ((1 : ℂ) ⊗ₜ p))) = _
    rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.map_tmul]
    rfl
  have hle : ∀ a ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ)), θ a = 0 := by
    have hker : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker θ := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hp, tmul_zero]
    exact fun a ha => hker ha
  let ψ := Ideal.Quotient.liftₐ _ θ hle
  have key : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i)) :=
    Module.Flat.linearIndependent_one_tmul hg
  have hfun : (ψ.toLinearMap ∘ fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i))) = fun i => (1 : ℂ) ⊗ₜ[ℤ] Ideal.Quotient.mk P (g i) := by
    funext i
    exact hθ (g i)
  rw [← hfun] at key
  exact key.of_comp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

theorem UnitApprox.proof : UnitApprox.Statement := by
  intro F _ _ u hconj hsum
  classical
  let uw : InfinitePlace F → ℝ := fun w => u w.embedding
  have hu_mk : ∀ sg, u sg = uw (InfinitePlace.mk sg) := by
    intro sg
    rcases embedding_mk_eq sg with h | h
    · simp only [uw, h]
    · simp only [uw, h, hconj]
  have hsum' : ∑ w : InfinitePlace F, (mult w : ℝ) * uw w = 0 := by
    rw [← hsum, ← Finset.sum_fiberwise Finset.univ (fun sg => InfinitePlace.mk sg) u]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => uw w), Finset.sum_const, nsmul_eq_mul,
      card_filter_mk_eq]
    intro sg hsg
    rw [Finset.mem_filter] at hsg
    rw [hu_mk, hsg.2]
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  let R : ℝ := ∑ i, ‖b i‖
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  refine ⟨Fintype.card (InfinitePlace F) * R, fun n => ?_⟩
  let v : logSpace F := fun w => n * ((mult w.val : ℝ) * uw w.val)
  have hfl : ((ZSpan.floor b v : _) : logSpace F) ∈ unitLattice F := by
    rw [← (basisUnitLattice F).ofZLatticeBasis_span ℝ (unitLattice F)]
    exact (ZSpan.floor b v).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.mp hfl
  refine ⟨Additive.toMul x, ?_⟩
  set ε := Additive.toMul x with hε
  have hfr : ‖v - (ZSpan.floor b v : logSpace F)‖ ≤ R := by
    simpa [ZSpan.fract_apply] using ZSpan.norm_fract_le b v
  let e : InfinitePlace F → ℝ := fun w =>
    mult w * (Real.log (w ((ε : 𝓞 F) : F)) - n * uw w)
  have he_ne : ∀ w (hw : w ≠ w₀), |e w| ≤ R := by
    intro w hw
    have h1 := norm_le_pi_norm (v - (ZSpan.floor b v : logSpace F)) ⟨w, hw⟩
    rw [← hx] at h1
    have h2 : (logEmbedding F).toIntLinearMap x ⟨w, hw⟩
        = mult w * Real.log (w ((ε : 𝓞 F) : F)) := rfl
    rw [Pi.sub_apply, h2, Real.norm_eq_abs] at h1
    have h3 : e w = -(v ⟨w, hw⟩ - mult w * Real.log (w ((ε : 𝓞 F) : F))) := by
      simp only [e, v]; ring
    rw [h3, abs_neg]
    rw [← hx] at hfr
    linarith
  have he_sum : ∑ w, e w = 0 := by
    have h := sum_mult_mul_log ε
    have h2 : ∑ w : InfinitePlace F, (mult w : ℝ) * (n * uw w)
        = n * ∑ w, (mult w : ℝ) * uw w := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    simp only [e, mul_sub, Finset.sum_sub_distrib, h2, hsum', mul_zero, sub_zero]
    exact h
  have he : ∀ w, |e w| ≤ Fintype.card (InfinitePlace F) * R := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have h := Finset.add_sum_erase Finset.univ e (Finset.mem_univ w₀)
      rw [he_sum] at h
      have h3 : e w₀ = -∑ w ∈ Finset.univ.erase w₀, e w := by linarith
      rw [h3, abs_neg]
      calc |∑ w ∈ Finset.univ.erase w₀, e w| ≤ ∑ w ∈ Finset.univ.erase w₀, |e w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w ∈ Finset.univ.erase w₀, R :=
            Finset.sum_le_sum fun w hw => he_ne w (Finset.ne_of_mem_erase hw)
        _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
          exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (he_ne w hw).trans (le_mul_of_one_le_left hR0 hcard)
  intro sg
  have hm : (1 : ℝ) ≤ mult (InfinitePlace.mk sg) := one_le_mult
  have h4 : |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ |e (InfinitePlace.mk sg)| := by
    simp only [e, abs_mul, hu_mk sg, InfinitePlace.apply, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) hm
  exact h4.trans (he _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDoubleComplexVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem DoubleComplexVanish.proof : DoubleComplexVanish.Statement := by
  intro C _ P δ κ R hδP hκP hδδ hδκ hκκ hsurj hex hzero hacyc

  have triv : ∀ p n, R ≤ p → ∀ x ∈ P p (n + 1), (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    rintro p n hp x - ⟨y, hy, rfl⟩
    rw [hzero (p + 1) (n + 1) (by omega) y hy, map_zero]
    exact ⟨0, zero_mem _, map_zero _, 0, zero_mem _, map_zero _⟩
  have claim : ∀ k p n, R ≤ p + k → ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 →
      (∃ y ∈ P (p + 1) (n + 1), κ p (n + 1) y = x) →
      ∃ w ∈ P p n, δ p n w = x ∧ ∃ w' ∈ P (p + 1) n, κ p n w' = w := by
    intro k
    induction k with
    | zero => exact fun p n hp x hx _ hy => triv p n (by omega) x hx hy
    | succ k ih =>
      intro p n hp x hx hdx hy0
      by_cases hRp : R ≤ p
      · exact triv p n hRp x hx hy0
      obtain ⟨y, hy, hyx⟩ := hy0
      have hdy : δ (p + 1) (n + 1) y ∈ P (p + 1) (n + 2) := hδP _ _ y hy
      have hk : κ p (n + 2) (δ (p + 1) (n + 1) y) = 0 := by
        rw [← hδκ p (n + 1) y hy, hyx, hdx]
      obtain ⟨w, hw, hwe, w', hw', hw'e⟩ :=
        ih (p + 1) (n + 1) (by omega) _ hdy (hδδ _ _ y hy) (hex p (n + 2) _ hdy hk)
      have hdyw : δ (p + 1) (n + 1) (y - w) = 0 := by rw [map_sub, hwe, sub_self]
      obtain ⟨v, hv, hve⟩ := hacyc (p + 1) (by omega) (by omega) n (y - w) (sub_mem hy hw) hdyw
      refine ⟨κ p n v, hκP _ _ v hv, ?_, v, hv, rfl⟩
      rw [hδκ p n v hv, hve, map_sub, hyx, ← hw'e, hκκ p (n + 1) w' hw', sub_zero]
  intro n x hx hdx
  obtain ⟨w, hw, hwe, -⟩ := claim R 0 n (by omega) x hx hdx (hsurj (n + 1) x hx)
  exact ⟨w, hw, hwe⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjectiveSpaceIncrementHyp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Objects

variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]


variable {ι}

end Objects

section Support

variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]

end Support

section Cycle

variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]

end Cycle

section Statements

def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

end Statements

section Examples

variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]

end Examples

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolySandwich
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial Filter

theorem PolySandwich.leadingCoeff_nonneg_of_eventually (f : ℚ[X])
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.leadingCoeff := by
  by_contra h
  push Not at h
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · obtain ⟨n, hn⟩ := hf.exists
    rw [eq_C_of_natDegree_eq_zero h0, eval_C] at hn
    have : f.leadingCoeff = f.coeff 0 := by rw [leadingCoeff, h0]
    linarith
  · have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
    have ht := (f.tendsto_atBot_of_leadingCoeff_nonpos hdeg h.le).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn1, hn2⟩ := (hf.and (ht.eventually (eventually_lt_atBot 0))).exists
    simp only [Function.comp] at hn2
    linarith

theorem PolySandwich.coeff_nonneg_of_eventually (f : ℚ[X]) (E : ℕ) (hE : f.natDegree ≤ E)
    (hf : ∀ᶠ n : ℕ in atTop, 0 ≤ f.eval (n : ℚ)) : 0 ≤ f.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt]
  · rw [← heq]
    exact PolySandwich.leadingCoeff_nonneg_of_eventually f hf

theorem PolySandwich.natDegree_shift (p : ℚ[X]) (c : ℚ) : (p.comp (X + C c)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem PolySandwich.coeff_shift (p : ℚ[X]) (c : ℚ) (E : ℕ) (hE : p.natDegree ≤ E) :
    (p.comp (X + C c)).coeff E = p.coeff E := by
  rcases hE.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt hlt,
      coeff_eq_zero_of_natDegree_lt (by rwa [PolySandwich.natDegree_shift])]
  · subst heq
    have h1 : (p.comp (X + C c)).leadingCoeff = p.leadingCoeff := by
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow,
        mul_one]
    rw [leadingCoeff, PolySandwich.natDegree_shift] at h1
    exact h1

theorem PolySandwich.proof : PolySandwich.Statement := by
  intro D c p q hq hev
  set g : ℚ[X] := p.comp (X + C (c : ℚ)) with hg
  have h1 : ∀ᶠ n : ℕ in atTop, 0 ≤ (q - p).eval (n : ℚ) :=
    hev.mono fun n hn => by rw [eval_sub]; linarith [hn.1]
  have h2 : ∀ᶠ n : ℕ in atTop, 0 ≤ (g - q).eval (n : ℚ) :=
    hev.mono fun n hn => by
      rw [eval_sub, hg, eval_comp, eval_add, eval_X, eval_C]; linarith [hn.2]
  have hgdeg : g.natDegree = p.natDegree := PolySandwich.natDegree_shift p c

  have key : ∀ E : ℕ, p.natDegree ≤ E → q.natDegree ≤ E → p.coeff E = q.coeff E := by
    intro E hp hqE
    have a := PolySandwich.coeff_nonneg_of_eventually (q - p) E
      ((natDegree_sub_le _ _).trans (max_le hqE hp)) h1
    have b := PolySandwich.coeff_nonneg_of_eventually (g - q) E
      ((natDegree_sub_le _ _).trans (max_le (hgdeg ▸ hp) hqE)) h2
    rw [coeff_sub] at a b
    rw [hg, PolySandwich.coeff_shift p c E hp] at b
    linarith
  have hpD : p.natDegree ≤ D := by
    by_contra hlt
    push Not at hlt
    have e := key p.natDegree le_rfl (hq.trans hlt.le)
    rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt hlt)] at e
    have hp0 : p = 0 := leadingCoeff_eq_zero.mp e
    rw [hp0, natDegree_zero] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  exact ⟨hpD, key D hpD hq⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
