module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
noncomputable section

namespace MassDataIdxRed

open Matrix

theorem isUnit_of_map {R S : Type} [CommRing R] [IsLocalRing R] [Field S] (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (h : IsUnit (π r)) : IsUnit r := by
  by_contra hr
  have hk : RingHom.ker π = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective π hπ)
  have hm : r ∈ RingHom.ker π := by
    rw [hk]; exact (IsLocalRing.mem_maximalIdeal r).2 hr
  rw [RingHom.mem_ker] at hm
  rw [hm] at h
  exact not_isUnit_zero h

def glRed {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S) :
    GL ι R →* GL ι S :=
  Units.map (π.mapMatrix : Matrix ι ι R →+* Matrix ι ι S).toMonoidHom

theorem glRed_coe {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S] (π : R →+* S)
    (A : GL ι R) : ((glRed π A : GL ι S) : Matrix ι ι S) = (A : Matrix ι ι R).map π := rfl

theorem glRed_surjective {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hloc : ∀ r, IsUnit (π r) → IsUnit r) :
    Function.Surjective (glRed (ι := ι) π) := by
  intro B
  choose f hf using hπ
  set A0 : Matrix ι ι R := (B : Matrix ι ι S).map f with hA0def
  have hA0 : A0.map π = (B : Matrix ι ι S) := by
    ext i j; simp [A0, hf]
  have hdet : IsUnit A0.det := by
    apply hloc
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA0]
    exact (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  refine ⟨Matrix.nonsingInvUnit A0 hdet, ?_⟩
  apply Units.ext
  rw [glRed_coe]
  exact hA0

theorem glRed_eq_one_iff {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (A : GL ι R) :
    glRed π A = 1 ↔ ∀ i j, ((A : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [← Units.val_inj, glRed_coe, Units.val_one]
  constructor
  · intro h i j
    have hij := congrFun (congrFun h i) j
    rw [Matrix.map_apply] at hij
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    ext i j
    have hij := h i j
    rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Matrix.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end MassDataIdxRed
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CongSpanSingleIff
noncomputable section

namespace MassDataIdxFrA

variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]

def IntVec (v : ι → F) : Prop := ∀ i, v i ∈ O

def CongSpan (S : Set (ι → F)) (v : ι → F) : Prop :=
  ∃ w ∈ Submodule.span O S, ∃ z : ι → F, IntVec O z ∧ v = w + (γ : F) • z



section Mat

open Matrix

variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem congSpan_zero (S : Set (ι → F)) : CongSpan O γ S 0 := by
  exact ⟨0, zero_mem _, 0, fun _ => zero_mem _, by simp⟩

theorem congSpan_neg (S : Set (ι → F)) (v : ι → F) : CongSpan O γ S (-v) ↔ CongSpan O γ S v := by
  have key : ∀ x, CongSpan O γ S x → CongSpan O γ S (-x) := by
    rintro x ⟨w, hw, z, hz, rfl⟩
    exact ⟨-w, neg_mem hw, -z, fun i => neg_mem (hz i), by rw [smul_neg, neg_add]⟩
  exact ⟨fun h => by simpa using key _ h, key v⟩

end Mat

end MassDataIdxFrA
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GenOfTwo
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.QuadRoot
noncomputable section

namespace MassDataIdxEmb

open Metric

theorem quad_root {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c0 c1 : K) (h1 : ‖c1‖ = 1) (h0 : ‖c0‖ < 1) :
    ∃ x : K, x * x + c1 * x + c0 = 0 := by
  have hnorm : ∀ x : K, ‖x‖ ≤ ‖c0‖ → ‖c1 + x‖ = 1 := by
    intro x hx
    have hne : ‖c1‖ ≠ ‖x‖ := by rw [h1]; exact (lt_of_le_of_lt hx h0).ne'
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, h1]
    exact max_eq_left (hx.trans h0.le)
  have hne0 : ∀ x : K, ‖x‖ ≤ ‖c0‖ → c1 + x ≠ 0 := fun x hx h => by
    have h' := hnorm x hx
    rw [h, norm_zero] at h'
    exact zero_ne_one h'
  set f : K → K := fun x => -c0 / (c1 + x) with hf
  have hmaps : Set.MapsTo f (closedBall 0 ‖c0‖) (closedBall 0 ‖c0‖) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    simp only [hf, norm_div, norm_neg, hnorm x hx, div_one, le_refl]
  haveI : IsClosed (closedBall (0 : K) ‖c0‖) := isClosed_closedBall
  haveI : CompleteSpace (closedBall (0 : K) ‖c0‖) := IsClosed.completeSpace_coe
  haveI : Nonempty (closedBall (0 : K) ‖c0‖) := ⟨⟨0, mem_closedBall_self (norm_nonneg _)⟩⟩
  have hcon : ContractingWith ⟨‖c0‖, norm_nonneg _⟩ (hmaps.restrict f _ _) := by
    refine ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact h0),
      LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha := mem_closedBall_zero_iff.1 a.2
    have hb := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    show ‖f a - f b‖ ≤ ‖c0‖ * ‖(a : K) - b‖
    have he : f a - f b = c0 * ((a : K) - b) / ((c1 + a) * (c1 + b)) := by
      simp only [hf]
      field_simp [hne0 _ ha, hne0 _ hb]
      ring
    rw [he, norm_div, norm_mul, norm_mul, hnorm _ ha, hnorm _ hb, mul_one, div_one]
  obtain ⟨x0, hx0e⟩ : ∃ x0 : closedBall (0 : K) ‖c0‖, hmaps.restrict f _ _ x0 = x0 :=
    ⟨_, hcon.fixedPoint_isFixedPt⟩
  have hfix : f (x0 : K) = x0 := congrArg Subtype.val hx0e
  refine ⟨(x0 : K), ?_⟩
  have hx0 := hne0 _ (mem_closedBall_zero_iff.1 x0.2)
  simp only [hf] at hfix
  rw [div_eq_iff hx0] at hfix
  linear_combination -hfix

end MassDataIdxEmb
end
end

noncomputable section

namespace MassDataIdxEmb

open NumberField IsDedekindDomain Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mem_iff_algebraMap_mem_of_liesOver (P : Ideal (𝓞 E)) (q : Ideal (𝓞 F)) [P.LiesOver q]
    (c : 𝓞 F) : c ∈ q ↔ algebraMap (𝓞 F) (𝓞 E) c ∈ P := by
  rw [Ideal.over_def P q]
  exact Iff.rfl

private theorem exists_mem_not_mem_of_ne_of_isMaximal {R : Type*} [CommRing R] (Q Q' : Ideal R)
    [hQ : Q.IsMaximal] [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') : ∃ a ∈ Q, a ∉ Q' := by
  by_contra h
  push Not at h
  exact hne (hQ.eq_of_le hQ'.ne_top (fun x hx => h x hx))

theorem gen_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E)) [hQ : Q.IsMaximal]
    [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    ∃ a : 𝓞 E, ∃ c0 c1 : 𝓞 F, (∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a) ∧
      a * a + algebraMap (𝓞 F) (𝓞 E) c1 * a + algebraMap (𝓞 F) (𝓞 E) c0 = 0 ∧
      minpoly (𝓞 F) a = X ^ 2 + C c1 * X + C c0 ∧ (minpoly (𝓞 F) a).natDegree = 2 ∧
      c0 ∈ p.asIdeal ∧ c1 ∉ p.asIdeal := by
  obtain ⟨a, ha, ha'⟩ := exists_mem_not_mem_of_ne_of_isMaximal Q Q' hne
  have hnot : ∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a := by
    intro c hc
    apply ha'
    have hcQ : c ∈ p.asIdeal := (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal c).2 (by rw [hc]; exact ha)
    rw [← hc]
    exact (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal c).1 hcQ
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hle : (minpoly (𝓞 F) a).natDegree ≤ 2 := by
    have h : (minpoly F (algebraMap (𝓞 E) E a)).natDegree ≤ Module.finrank F E := by
      apply minpoly.natDegree_le
    rw [hfield, (minpoly.monic hint_r).natDegree_map, h2] at h
    exact h
  have hpos : 0 < (minpoly (𝓞 F) a).natDegree := minpoly.natDegree_pos hint_r
  have hne1 : (minpoly (𝓞 F) a).natDegree ≠ 1 := by
    intro h1
    have hX := (minpoly.monic hint_r).eq_X_add_C h1
    have hev := minpoly.aeval (𝓞 F) a
    rw [hX] at hev
    simp only [map_add (f := _), aeval_X, aeval_C] at hev
    apply hnot (-(minpoly (𝓞 F) a).coeff 0)
    rw [map_neg]
    linear_combination -hev
  have hdeg : (minpoly (𝓞 F) a).natDegree = 2 := by omega
  have hP : minpoly (𝓞 F) a =
      X ^ 2 + C ((minpoly (𝓞 F) a).coeff 1) * X + C ((minpoly (𝓞 F) a).coeff 0) := by
    refine (minpoly.monic hint_r).as_sum.trans ?_
    rw [hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one,
      zero_add]
    ring
  have hev := minpoly.aeval (𝓞 F) a
  rw [hP] at hev
  simp only [map_add (f := _), map_mul, map_pow, aeval_X, aeval_C] at hev
  have heq : a * a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
      algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) = 0 := by
    linear_combination hev
  have hc0 : (minpoly (𝓞 F) a).coeff 0 ∈ p.asIdeal := by
    refine (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal _).2 ?_
    have h : algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) =
        -(a * (a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1))) := by
      linear_combination heq
    rw [h]
    exact neg_mem (Q.mul_mem_right _ ha)
  have hc1 : (minpoly (𝓞 F) a).coeff 1 ∉ p.asIdeal := by
    intro h
    have h1 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 h
    have h0 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 hc0
    have haa : a * a ∈ Q' := by
      have h' : a * a = -(algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
          algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0)) := by
        linear_combination heq
      rw [h']
      exact neg_mem (add_mem (Q'.mul_mem_right _ h1) h0)
    rcases hQ'.isPrime.mem_or_mem haa with h | h <;> exact ha' h
  exact ⟨a, _, _, hnot, heq, hP, hdeg, hc0, hc1⟩

private theorem finitePlace_embedding_eq_algebraMap (p : HeightOneSpectrum (𝓞 F)) (k : F) :
    FinitePlace.embedding p k = algebraMap F (p.adicCompletion F) k := rfl

private theorem norm_algebraMap_adicCompletion_lt_one_of_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∈ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ < 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_lt_one_iff_mem F p c).2 hc

private theorem norm_algebraMap_adicCompletion_eq_one_of_not_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∉ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ = 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_eq_one_iff_notMem F p c).2 hc

theorem emb_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E))
    [Q.IsMaximal] [Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    Nonempty (E →ₐ[F] p.adicCompletion F) := by
  obtain ⟨a, c0, c1, -, -, hP, hdeg, hc0, hc1⟩ := gen_of_two h2 p Q Q' hne
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hbint : IsIntegral F (algebraMap (𝓞 E) E a) := IsIntegral.of_finite F _
  have htop : IntermediateField.adjoin F {algebraMap (𝓞 E) E a} = ⊤ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq, hfield,
      (minpoly.monic hint_r).natDegree_map, hdeg, h2]
  obtain ⟨x, hx⟩ := quad_root
    (algebraMap (𝓞 F) (p.adicCompletion F) c0) (algebraMap (𝓞 F) (p.adicCompletion F) c1)
    (norm_algebraMap_adicCompletion_eq_one_of_not_mem p c1 hc1) (norm_algebraMap_adicCompletion_lt_one_of_mem p c0 hc0)
  have hroot : aeval x (minpoly F (algebraMap (𝓞 E) E a)) = 0 := by
    rw [hfield, aeval_map_algebraMap F, hP]
    simp only [map_add (f := _), map_mul, map_pow, aeval_X, aeval_C]
    linear_combination hx
  have hpb : aeval x (minpoly F (IntermediateField.adjoin.powerBasis hbint).gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact hroot
  let e : ↥(IntermediateField.adjoin F {algebraMap (𝓞 E) E a}) ≃ₐ[F] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  exact ⟨((IntermediateField.adjoin.powerBasis hbint).lift x hpb).comp e.symm.toAlgHom⟩

end MassDataIdxEmb
end
end
