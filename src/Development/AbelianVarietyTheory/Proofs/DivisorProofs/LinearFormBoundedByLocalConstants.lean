module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFubiniStudyDensityEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOrbitConjCompactModCentralizerUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpolyStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstants
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.LinFormBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem nnnorm_sum_le (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι) (x : ι → Fv F v) {c : ℝ≥0}
    (h : ∀ i ∈ s, ‖x i‖₊ ≤ c) : ‖∑ i ∈ s, x i‖₊ ≤ c := by
  rw [← absFin_tmul_one (E := F) F v, TensorProduct.sum_tmul]
  exact absFin_sum_le F v _ _ fun i hi => (absFin_tmul_one (E := F) F v (x i)).trans_le (h i hi)

theorem eventually_nnnorm_evFin_le_one (a : AF F) : ∀ᶠ v in Filter.cofinite, ‖evFin F v a‖₊ ≤ 1 := by
  refine (eventually_absFin_le_one (E := F) F (a ⊗ₜ[F] (1 : F))).mono fun v hv => ?_
  rwa [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    absFin_tmul_one] at hv

theorem exists_bound {n m : ℕ} (f : Matrix (Fin n) (Fin m) (AF F ⊗[F] E) →ₗ[AF F] AF F) :
    ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧
      ∀ X v, ‖evFin F v (f X)‖₊ ≤
        K v * Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  let B := Algebra.TensorProduct.basis (AF F) b.traceDual

  let y : Fin n × Fin m × s → AF F := fun q => f (Matrix.single q.1 q.2.1 (B q.2.2))
  let K : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (Finset.univ.sup fun q => ‖evFin F v (y q)‖₊)
  have hdec : ∀ X : Matrix (Fin n) (Fin m) (AF F ⊗[F] E),
      f X = ∑ q : Fin n × Fin m × s, B.repr (X q.1 q.2.1) q.2.2 * y q := by
    intro X
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← B.sum_repr (X i j)]
    have : Matrix.single i j (∑ k, B.repr (X i j) k • B k) = ∑ k, B.repr (X i j) k • Matrix.single i j (B k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← Matrix.singleLinearMap_apply (R := AF F), map_sum, map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp only [map_smul, smul_eq_mul, y]
  refine ⟨K, ?_, fun v => le_max_left _ _, fun X v => ?_⟩
  · have h := eventually_all.2 fun q => eventually_nnnorm_evFin_le_one (y q)
    refine (eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun q _ => ?_))
    exact hv' q
  · have hsup : ∀ p : Fin n × Fin m, absFin F v (compFin F E v (X p.1 p.2)) ≤
        Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)) :=
      fun p => Finset.le_sup (f := fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)))
        (Finset.mem_univ p)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec X, map_sum]
    refine nnnorm_sum_le v _ _ fun q _ => ?_
    rw [map_mul, nnnorm_mul, mul_comm]
    refine mul_le_mul' ?_ ?_
    · exact (Finset.le_sup (f := fun q => ‖evFin F v (y q)‖₊) (Finset.mem_univ q)).trans (le_max_right _ _)
    · rw [← HeightProper.repr_map b.traceDual (evFin F v) (X q.1 q.2.1) q.2.2]
      refine (HeightProper.nnnorm_repr_le_absFin b hb' v _ q.2.2).trans ?_
      have hc : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (X q.1 q.2.1) = compFin F E v (X q.1 q.2.1) :=
        rfl
      rw [hc]
      exact hsup (q.1, q.2.1)

end GlobalTheory.LinFormBound

theorem GlobalTheory.LinFormBound.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) :=
  fun f => GlobalTheory.LinFormBound.exists_bound f
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormBoundedByLocalConstantsStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_form_bounded_by_local_constants : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
  first | exact @GlobalTheory.LinFormBound.main | exact GlobalTheory.LinFormBound.main | (intros; apply GlobalTheory.LinFormBound.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipClosed

theorem isClosed_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁) (hx : H'.x ≠ 0) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι

  set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS
  obtain ⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have hcu : IsUnit (x k) := by
    have : x k = inclR (F := F) (AF F) (H'.x k) := rfl
    rw [this]; exact (IsUnit.mk0 _ hk).map _
  set c : (AE F E)ˣ := hcu.unit
  have hc : (c : AE F E) = x k := hcu.unit_spec
  have hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x := by
    intro v w
    constructor
    · rintro ⟨a, rfl⟩
      congr 2
      simp only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    · intro h; exact ⟨_, h⟩
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hSc : IsClosed S := by
    have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x} :=
      isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
    have h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun z => ?_
      simp_rw [hline]
      have hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z) := hm.matrix_mulVec continuous_const
      have hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹) :=
        ((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const
      exact isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))
    exact h1.inter h2
  have hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S := by
    refine ⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
    · rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
      obtain ⟨a, ha⟩ := hv2 z
      obtain ⟨b, hb⟩ := hu2 z
      refine ⟨b + a, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]
    · exact ⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩
    · rintro u ⟨hu1, hu2⟩
      have e1 : mat u⁻¹ *ᵥ x = x := by
        conv_lhs => rw [← hu1]
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      refine ⟨e1, fun z => ?_⟩
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨-a, ?_⟩
      have : mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  obtain ⟨H, hH⟩ := hsub
  have : unip σ W H' = H := by
    apply le_antisymm
    · rw [unip, Subgroup.closure_le]; exact hH.symm ▸ subset_rfl
    · intro g hg
      have : g ∈ S := hH ▸ hg
      exact Subgroup.subset_closure this
  rw [this, hH]; exact hSc

end GlobalTheory.UnipClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzeroStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_closed_nonzero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), H'.x ≠ 0 → IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  first | exact @GlobalTheory.UnipClosed.isClosed_unip | exact GlobalTheory.UnipClosed.isClosed_unip | (intros; apply GlobalTheory.UnipClosed.isClosed_unip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomial
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.SelfRecipFactor

theorem isSelfRecip_of_dvd_ell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]),
    P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P →
      GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  intro E _ _ _ n P hP Q hQm hQi hQP
  obtain ⟨hPm, -, -, hroots⟩ := hP
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hP0 : P ≠ 0 := hPm.ne_zero
  have hnorm : ∀ z : ℂ, (Q.map τ).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    apply hroots τ z
    rw [mem_roots (Polynomial.map_ne_zero hP0)]
    obtain ⟨R, rfl⟩ := hQP
    have hz' : eval z (Q.map τ) = 0 := hz
    simp [IsRoot, Polynomial.map_mul, eval_mul, hz']
  have hQ0 : Q.coeff 0 ≠ 0 := by
    intro h0
    have h : (Q.map τ).IsRoot 0 := by
      rw [IsRoot.def, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hnorm 0 h
    simp at this
  set d := Q.natDegree with hd
  set c : E →+* E := (IsCMField.complexConj E : E →+* E) with hc
  have hτc : τ.comp c = (starRingEnd ℂ).comp τ := by
    ext x
    exact IsCMField.complexEmbedding_complexConj E τ x
  have hcQ0 : c (Q.coeff 0) ≠ 0 := by
    simpa using hQ0
  set S := GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.sharp E d Q with hS
  have hSdef : S = C (c (Q.coeff 0))⁻¹ * reflect d (Q.map c) := rfl
  have hdegc : (Q.map c).natDegree = d := natDegree_map c
  have hSm : S.Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one d
    · rw [hSdef]
      refine (natDegree_C_mul_le _ _).trans ?_
      refine natDegree_reflect_le.trans ?_
      rw [hdegc, max_self]
    · rw [hSdef, coeff_C_mul, coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_map]
      exact inv_mul_cancel₀ hcQ0
  have hSdeg : S.natDegree ≤ d := by
    rw [hSdef]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine natDegree_reflect_le.trans ?_
    rw [hdegc, max_self]

  have hdeg : 0 < (Q.map τ).degree := by
    rw [degree_map]; exact degree_pos_of_irreducible hQi
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz1 : ‖z‖ = 1 := hnorm z hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz1; simp at hz1
  have hzinv : z⁻¹ = (starRingEnd ℂ) z := Complex.inv_eq_conj hz1
  have hQz : eval₂ τ z Q = 0 := by
    have : eval z (Q.map τ) = 0 := hz
    rwa [eval_map] at this
  have hSz : eval₂ τ z S = 0 := by
    letI : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
    have key := eval₂_reflect_mul_pow τ (z⁻¹) d (Q.map c) hdegc.le
    rw [invOf_eq_inv, inv_inv, eval₂_map, hτc, hzinv, ← Polynomial.hom_eval₂, hQz, map_zero] at key
    have hr : eval₂ τ z (reflect d (Q.map c)) = 0 := by
      rcases mul_eq_zero.1 key with h | h
      · exact h
      · exact absurd h (pow_ne_zero _ ((_root_.map_ne_zero _).2 hz0))
    rw [hSdef, eval₂_mul, hr, mul_zero]
  have hdvd : Q ∣ S := by
    by_contra h
    obtain ⟨a, b, hab⟩ := (hQi.coprime_iff_not_dvd).2 h
    have := congrArg (eval₂ τ z) hab
    rw [eval₂_add, eval₂_mul, eval₂_mul, hQz, hSz, eval₂_one] at this
    simp at this
  refine ⟨hQm, hQi, rfl, hQ0, ?_⟩
  exact (eq_of_monic_of_dvd_of_natDegree_le hQm hSm hdvd hSdeg).symm

end GlobalTheory.SelfRecipFactor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomialStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isConjSelfReciprocal_of_dvd_elliptic_polynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∀ Q : E[X], Q.Monic → Irreducible Q → Q ∣ P → GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField.IsSelfRecip E Q.natDegree Q := by
  first | exact @GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell | exact GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell | (intros; apply GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentraliz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentraliz
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ Ω := by
  intro E _ _ _ hE n w y hy
  obtain ⟨Ω, hΩ, hsub⟩ := GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic E hE n w y hy
  refine ⟨Ω, hΩ, fun t ht => ?_⟩
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a.1.val * y.1.val =
        y.1.val * a.1.val :=
      by
        have h0 : a * y = y * a := ha
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hb' : b.1.val * y.1.val =
        y.1.val * b.1.val :=
      by
        have h0 : b * y = y * b := hb
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have := GlobalTheory.T.commute_of_commute_of_charpoly_separable' _ n _ _ _ hy ha' hb'
    exact Subtype.ext (Units.ext this)
  have := cptPart_subset_of_comm _ hc ht
  exact hsub t this.1 this.2

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem conj_map_eq {G : Type} [Group G] (x : G) (K : Subgroup G) :
    (K.map (MulAut.conj x).toMonoidHom : Set G) = (fun k => x * k * x⁻¹) '' (K : Set G) := by
  ext g
  simp [Subgroup.coe_map, MulAut.conj_apply]

theorem locFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  intro E _ _ _ hE n w y hy K' hK'
  obtain ⟨hK'o, -, -⟩ := hK'
  obtain ⟨Ω, hΩ, hsub⟩ := bound E hE n w y hy
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨htT, htK⟩ := Subgroup.mem_inf.1 ht
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hc : IsCompact ((KL n w).map (MulAut.conj x).toMonoidHom : Set (UL n w)) := by
      rw [conj_map_eq]
      exact (isCompact_KL n w).image ((continuous_const.mul continuous_id).mul continuous_const)
    refine hc.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (Subgroup.zpowers_le.2 htK) hc.isClosed
  · have hP : cptPart (twCent (MonoidHom.id _) y) ≤ twCent (MonoidHom.id _) y :=
      (Subgroup.closure_le _).2 (fun t ht => ht.1)
    have hU : IsOpen ((K'.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (UL n w)) := by
      rw [conj_map_eq]
      exact ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK'o
    have h := relIndex_ne_zero_of_subset_cpt _ _ hU Ω hΩ hsub
    have e : (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf
        (cptPart (twCent (MonoidHom.id _) y)) =
        (K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y)) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hP z.2, h⟩⟩
    unfold Subgroup.relIndex at h ⊢
    rwa [e]
  · intro C hC
    obtain ⟨Ω', hΩ', horb⟩ := GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary E hE n w y hy C hC
    obtain ⟨s, hs⟩ := hΩ'.elim_finite_subcover (fun g : Ω' => (g : UL n w) • (K' : Set (UL n w)))
      (fun g => hK'o.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K'.one_mem, mul_one x⟩⟩)
    refine (s.finite_toSet.image
      (fun g : Ω' => DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) y) K' (g : UL n w))).subset ?_
    intro q hq
    obtain ⟨t, ht, ω, hω, heq⟩ := horb _ hq
    have := hs hω
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, k, hk, hik⟩ := this
    refine ⟨i, hi, ?_⟩
    conv_rhs => rw [← Quotient.out_eq q]
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨t, ht, k, hk, ?_⟩
    rw [heq, ← hik]
    simp only [smul_eq_mul, mul_assoc]

end GlobalTheory.LocFinU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentralizStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  first | exact @GlobalTheory.LocFinU.locFin | exact GlobalTheory.LocFinU.locFin | (intros; apply GlobalTheory.LocFinU.locFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizer
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.CptTorus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem twCent_commute (hE : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) {g : GLw n w}
    (hg : g ∈ twCent (thL n w) y) : Commute g (nrmL n w y) := by
  have hinv : ∀ x, thL n w (thL n w x) = x := (GlobalTheory.T.localTwist_continuous_involution_integral_properties E hE n w).2.1
  have hg' : g * y = y * thL n w g := hg
  unfold nrmL
  split_ifs with hs
  · have ht : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    rw [ht] at hg'
    exact hg'
  · have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hs]
    rw [ht] at hg' hinv
    show g * (y * thetaGL n (cj w) y) = (y * thetaGL n (cj w) y) * g
    calc g * (y * thetaGL n (cj w) y) = (g * y) * thetaGL n (cj w) y := by rw [mul_assoc]
      _ = y * (thetaGL n (cj w) g * thetaGL n (cj w) y) := by rw [hg', mul_assoc]
      _ = y * thetaGL n (cj w) (g * y) := by rw [map_mul]
      _ = y * thetaGL n (cj w) (y * thetaGL n (cj w) g) := by rw [hg']
      _ = (y * thetaGL n (cj w) y) * g := by rw [map_mul, hinv, mul_assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w),
    (nrmL n w y).val.charpoly.Separable →
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  intro E _ _ _ hE n w y hs
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨twCent_commute hE n w y ht, htc⟩

end GlobalTheory.CptTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizerStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_ge_compactPart_twistedCentralizer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  first | exact @GlobalTheory.CptTorus.main | exact GlobalTheory.CptTorus.main | (intros; apply GlobalTheory.CptTorus.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenBasisSameVec
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdryUnit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates

theorem exists_eigEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] {a : OAct O G} {a' : OAct O G'}
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R : Type} [CommRing R] (x : Sp R ⟶ S')
    (x' : Sp R ⟶ S) (hx : x' = x ≫ f) :
    ∃ e : (epsAt x ⟶ G') ≃ (epsAt x' ⟶ G), (∀ v, (e v).left = v.left ≫ φ) ∧
      ∀ (χ : O →+* R) (n : ℕ) (v : Fin n → (epsAt x ⟶ G')),
        IsEigenBasis a' x χ v ↔ IsEigenBasis a x' χ (fun i => e (v i)) := by
  subst hx
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsAt x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsAt x ⟶ G'), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (sc c))
  refine ⟨e.toEquiv, he, fun χ n v => ?_⟩
  have hP : ∀ v : epsAt x ⟶ G', IsEigenTangent a' x χ v ↔ IsEigenTangent a (x ≫ f) χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ G')).symm
      refine (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans ?_
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
    · have E : e (v ≫ a'.act c) = e v ≫ a.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
      rw [hR, E]
  have pr : ∀ u : Fin n → (epsAt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin n → R) (w : epsAt x ⟶ G'), IsCombination x c (fun i => (v i).left) w ↔
      IsCombination (x ≫ f) c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_eigenBasis_sameVec (Y : Model Xo c (RingHom.id c.F)) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) :
    ∃ v : Fin n → (epsAt ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _) ⟶ Y.t.G),
      IsEigenBasis Y.t.act _ (chr c τ (algebraMap c.F S)) v ∧
      ∀ i : Fin n, ∃ j : Fin (Dw.mult τ), (j : ℕ) = i ∧ SameVec Y y (y.u τ j) (v i).left := by
  subst hn
  obtain ⟨e₀, he₀, hb₀⟩ := exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act (ptF y) y.x
    (pullback.lift_fst _ _ _).symm
  obtain ⟨e, he, hb⟩ := exists_eigEquiv Y.m.cart Y.m.act (ptF y) ((ptF y ≫ Y.jQ) ≫ pullback.fst _ _)
    (Category.assoc _ _ _)
  let u : Fin (Dw.mult τ) → (epsAt y.x ⟶ Xo.univ.t.G) := fun i => Over.homMk (y.u τ i) (y.tan τ i).1
  have hu : IsEigenBasis Xo.univ.t.act y.x (chr c τ (algebraMap c.F S)) u := by
    refine ⟨fun i => ⟨(y.tan τ i).2, fun a => y.eig τ i a⟩, fun w hw => ?_⟩
    refine (existsUnique_congr fun a => ⟨?_, ?_⟩).1 (y.basis τ w.left ⟨Over.w w, hw.1⟩ fun a => hw.2 a)
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, Over.OverMorphism.ext h2.symm⟩
    · rintro ⟨u', h1, h2⟩
      exact ⟨u', h1, congrArg (fun z => z.left) h2.symm⟩
  have hw := (hb₀ (chr c τ (algebraMap c.F S)) _ fun i => e₀.symm (u i)).2
    ((funext fun i => e₀.apply_symm_apply (u i) : (fun i => e₀ (e₀.symm (u i))) = u).symm ▸ hu)
  refine ⟨fun i => e (e₀.symm (u i)), (hb _ _ _).1 hw, fun i => ⟨i, rfl, (e₀.symm (u i)).left,
    ⟨Over.w _, (hw.1 i).1⟩, ?_, (he _).symm⟩⟩
  rw [← he₀, Equiv.apply_symm_apply]
  rfl

theorem exists_matches (Y : Model Xo c (RingHom.id c.F)) (V : (Xo.XF c).Opens) (τ : Psi H) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S) (hy : ∀ s, ptF y s ∈ (V : Set (Xo.XF c))) :
    ∃ a : Framed Y V τ.1 S (algebraMap c.F S), Matches Y V τ y a := by
  obtain ⟨v, hv, ev⟩ := exists_eigenBasis_sameVec Y y τ.1 Dw.p (if_pos τ.2)
  obtain ⟨w, hw, ew⟩ := exists_eigenBasis_sameVec Y y (conjEmb τ.1) Dw.q (if_neg (conj_not_mem τ))
  refine ⟨⟨ptF y ≫ Y.jQ, by rw [Category.assoc, Y.jQ_over, ptF, pullback.lift_snd], ?_, v, w, hv, hw⟩,
    rfl, ev, ew⟩
  rintro _ ⟨z, rfl⟩
  exact subset_closure ⟨ptF y z, hy z, by simp⟩

end GlobalTheory.BdryUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensor
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.SBBlocks

theorem isClosed_support_of_isLocallyConstant {Z : Type} [TopologicalSpace Z] {f : Z → ℂ}
    (hf : IsLocallyConstant f) : IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
  rw [this]; exact (hf.isOpen_fiber 0).isClosed_compl

theorem mem_SB_of_support_subset {Z : Type} [TopologicalSpace Z] {f : Z → ℂ} {C : Set Z}
    (hf : IsLocallyConstant f) (hC : IsCompact C) (hs : Function.support f ⊆ C) : f ∈ SB Z :=
  ⟨hf, HasCompactSupport.intro' (hC.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf) hs)
    (isClosed_support_of_isLocallyConstant hf) fun _ hx => Function.notMem_support.1 hx⟩

theorem prod_decomp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X × Y → ℂ)
    (hh : h ∈ SB (X × Y)) :
    ∃ (m : ℕ) (a : Fin m → X → ℂ) (b : Fin m → Y → ℂ), (∀ j, a j ∈ SB X) ∧ (∀ j, b j ∈ SB Y) ∧
      ∀ x y, h (x, y) = ∑ j, a j x * b j y := by
  classical
  obtain ⟨hlc, hcs⟩ := hh
  have hK : IsCompact (tsupport h) := hcs.isCompact
  have hK1 : IsCompact (Prod.fst '' tsupport h) := hK.image continuous_fst
  have hK2 : IsCompact (Prod.snd '' tsupport h) := hK.image continuous_snd
  have hzero : ∀ x y, h (x, y) ≠ 0 → x ∈ Prod.fst '' tsupport h ∧ y ∈ Prod.snd '' tsupport h :=
    fun x y hne => ⟨⟨(x, y), subset_tsupport h hne, rfl⟩, ⟨(x, y), subset_tsupport h hne, rfl⟩⟩
  let s : Y → X → ℂ := fun y x => h (x, y)
  have hs : IsLocallyConstant s := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    have key : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ Prod.fst '' tsupport h, h (x, y) = h (x, y₀) := by
      refine hK1.eventually_forall_of_forall_eventually (P := fun y x => h (x, y) = h (x, y₀)) ?_
      intro x _
      have h1 : IsLocallyConstant (fun z : Y × X => h (z.2, z.1)) := hlc.comp_continuous continuous_swap
      have h2 : IsLocallyConstant (fun z : Y × X => h (z.2, y₀)) :=
        hlc.comp_continuous (continuous_snd.prodMk continuous_const)
      filter_upwards [h1.eventually_eq (y₀, x), h2.eventually_eq (y₀, x)] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    funext x
    by_cases hx : x ∈ Prod.fst '' tsupport h
    · exact hy x hx
    · show h (x, y) = h (x, y₀)
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩),
        image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩)]
  have hsSB : ∀ y, s y ∈ SB X := fun y =>
    mem_SB_of_support_subset (hlc.comp_continuous (continuous_id.prodMk continuous_const)) hK1
      (fun x hx => (hzero x y hx).1)
  have hsne : ∀ y, s y ≠ 0 → y ∈ Prod.snd '' tsupport h := fun y hy => by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hy
    exact (hzero x y hx).2
  obtain ⟨t, ht⟩ := hK2.elim_finite_subcover (fun φ : X → ℂ => s ⁻¹' {φ}) (fun φ => hs.isOpen_fiber φ)
    (fun y _ => Set.mem_iUnion.2 ⟨s y, rfl⟩)
  let t' := t.filter (fun φ => φ ≠ 0 ∧ φ ∈ SB X)
  let bb : (X → ℂ) → Y → ℂ := fun φ y => if s y = φ then 1 else 0
  have hbSB : ∀ φ ∈ t', bb φ ∈ SB Y := by
    intro φ hφ
    have hφ0 : φ ≠ 0 := (Finset.mem_filter.1 hφ).2.1
    refine mem_SB_of_support_subset (hs.comp fun v => if v = φ then (1 : ℂ) else 0) hK2 ?_
    intro y hy
    have : s y = φ := by
      by_contra hne
      exact hy (if_neg hne)
    exact hsne y (this ▸ hφ0)
  have hsum : ∀ x y, h (x, y) = ∑ φ ∈ t', φ x * bb φ y := by
    intro x y
    have e1 : ∑ φ ∈ t', φ x * bb φ y = ∑ φ ∈ t', if s y = φ then φ x else 0 :=
      Finset.sum_congr rfl fun φ _ => by simp only [bb]; split_ifs <;> simp
    rw [e1, Finset.sum_ite_eq]
    split_ifs with hin
    · rfl
    · show s y x = 0
      by_contra hne
      have hy0 : s y ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
      apply hin
      obtain ⟨φ, hφ, hyφ⟩ := Set.mem_iUnion₂.1 (ht (hsne y hy0))
      have : s y = φ := hyφ
      exact Finset.mem_filter.2 ⟨this ▸ hφ, hy0, hsSB y⟩
  refine ⟨t'.card, fun j => (t'.equivFin.symm j : X → ℂ), fun j => bb (t'.equivFin.symm j),
    fun j => (Finset.mem_filter.1 (t'.equivFin.symm j).2).2.2, fun j => hbSB _ (t'.equivFin.symm j).2, ?_⟩
  intro x y
  rw [hsum x y, ← Finset.sum_coe_sort t']
  exact (Equiv.sum_comp t'.equivFin.symm (fun φ : t' => (φ : X → ℂ) x * bb φ y)).symm

theorem sum_prod_blocks {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (g : (κ ⊕ κ' → Af F) → ℂ) (hg : g ∈ SB (κ ⊕ κ' → Af F)) :
    ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧
      (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  let e : (κ ⊕ κ' → Af F) ≃ₜ (κ → Af F) × (κ' → Af F) := Homeomorph.sumArrowHomeomorphProdArrow
  have hh : g ∘ e.symm ∈ SB ((κ → Af F) × (κ' → Af F)) :=
    ⟨hg.1.comp_continuous e.symm.continuous, hg.2.comp_homeomorph e.symm⟩
  obtain ⟨m, a, b, ha, hb, hab⟩ := prod_decomp _ hh
  refine ⟨m, a, b, ha, hb, fun x x' => ?_⟩
  rw [← hab]
  show g _ = g (e.symm (x, x'))
  congr 1

end GlobalTheory.SBBlocks
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatSumSplitTensorStatement
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_sum_split_tensor : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → Af F) → ℂ), g ∈ SB (κ ⊕ κ' → Af F) → ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧ (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  first | exact @GlobalTheory.SBBlocks.sum_prod_blocks | exact GlobalTheory.SBBlocks.sum_prod_blocks | (intros; apply GlobalTheory.SBBlocks.sum_prod_blocks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_eq_integral_chart_of_support : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld)
    (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) →
    A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  intro M _ _ _ _ _ _ n A α i K hα hK hKs h0
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set r : A.ι → V n → ℝ := fun j v => (dens (A.loc α j v)).re with hr
  have dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

  have hc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      r j (A.e j y) = ‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2 * r k (A.e k y) := by
    intro j k y hj hk
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    have h2 := A.loc_crd α (⟨(k, y), hk⟩ : A.Pt)
    have h3 := hα.compat (⟨(j, y), hj⟩ : A.Pt) ⟨(k, y), hk⟩ rfl
    simp only [hr]
    erw [h1, h2, h3, dens_pull]
    rw [Complex.re_ofReal_mul]
    rfl

  have hz : ∀ j y, y ∈ (A.e j).source → y ∉ K → r j (A.e j y) = 0 := by
    intro j y hj hy
    have h1 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
    simp only [hr]
    erw [h1, h0 _ hy, dens_zero]
    rfl

  have hpart : ∀ ε : ℤˣ, A.part α ε univ =
      ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    set ρ : A.ι → M → ENNReal := fun j y => ENNReal.ofReal (((ε : ℤ) : ℝ) * r j (A.e j y)) with hρ
    have hp : A.part α ε = ChartGlue.glueMeas A.e ρ := rfl
    have hρc : ∀ j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
        ρ j y = ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) * ρ k y := by
      intro j k y hj hk
      simp only [hρ]
      rw [hc j k y hj hk, ← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    have hcompl : ChartGlue.glueMeas A.e ρ Kᶜ = 0 := by
      have key : ChartGlue.glueMeas A.e ρ ≤ (ChartGlue.glueMeas A.e ρ).restrict K := iSup_le fun j => by
        have e : ChartGlue.chartMeas (A.e j) (ρ j) Kᶜ = 0 := by
          rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
          refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
            ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
          rintro _ ⟨y, hy, rfl⟩
          simp only [hρ, (A.e j).left_inv hy.1, hz j y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero, Pi.zero_apply]
        rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
        exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j) (ρ j)) j)
      refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
      rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
    rw [hp, ← measure_add_measure_compl hKm, hcompl, add_zero,
      ChartGlue.glueMeas_apply A.e ρ A.holo hρc i hKm hKs, ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs]
    refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _ hKm hKs) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [hρ, (A.e i).left_inv (hKs hy)]

  have hBc : IsCompact (A.e i '' K) := hK.image_of_continuousOn ((A.e i).continuousOn.mono hKs)
  have hBt : A.e i '' K ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hKs hy)
  have hH0 : ∀ v ∉ A.e i '' K, r i v = 0 := by
    intro v hv
    by_cases ht : v ∈ (A.e i).target
    · have hs := (A.e i).map_target ht
      have hnK : (A.e i).symm v ∉ K := fun hk => hv ⟨_, hk, (A.e i).right_inv ht⟩
      have := hz i _ hs hnK
      rwa [(A.e i).right_inv ht] at this
    · have hl : A.loc α i v = 0 := by
        unfold loc
        exact dif_neg ht
      simp only [hr, hl, dens_zero, Complex.zero_re]
  have hcon : ContinuousOn (r i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hHc : Continuous (r i) := continuous_iff_continuousAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact hcon.continuousAt ((A.e i).open_target.mem_nhds ht)
    · have : r i =ᶠ[𝓝 v] fun _ => 0 := by
        filter_upwards [hBc.isClosed.isOpen_compl.mem_nhds (fun h => ht (hBt h))] with w hw
        exact hH0 w hw
      exact continuousAt_const.congr this.symm
  have hHi : Integrable (r i) := hHc.integrable_of_hasCompactSupport (HasCompactSupport.intro hBc hH0)
  have hl : ∀ ε : ℤˣ, ∫⁻ v in A.e i '' K, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) =
      ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * r i v) := by
    intro ε
    rw [← lintegral_indicator hBc.measurableSet]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ A.e i '' K
    · rw [Set.indicator_of_mem hv]
    · rw [Set.indicator_of_notMem hv, hH0 v hv, mul_zero, ENNReal.ofReal_zero]
  have e1 := hpart 1
  have e2 := hpart (-1)
  rw [hl] at e1 e2
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  simp only [GlobalTheory.CxForm.HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hHi).symm

end GlobalTheory.CxForm.HolAtlas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChartStatement
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld) (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) → A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  exact @GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support
end
end
