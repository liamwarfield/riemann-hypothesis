module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.EllipticCharpolySelfReciprocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBounds
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem exists_nat_mul_integral_of_valuation_le : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  intro E _ _ γ hγ
  have hfin : {u : Pl E | ¬ γ u ≤ 1}.Finite := Filter.eventually_cofinite.1 hγ
  let S : Finset (Pl E) := hfin.toFinset
  let k : Pl E → ℕ := fun u => (WithZero.log (γ u)).toNat
  let N : Pl E → ℕ := fun u => Ideal.absNorm u.asIdeal
  refine ⟨∏ u ∈ S, N u ^ k u, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro u _
    apply pow_ne_zero
    simp only [N, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  · intro x hx
    have hval : ∀ u : Pl E, u.valuation E x * u.valuation E ((∏ w ∈ S, N w ^ k w : ℕ) : E) ≤ 1 := by
      intro u
      have hcast : (((∏ w ∈ S, N w ^ k w : ℕ) : E)) =
          algebraMap (𝓞 E) E ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) := (map_natCast _ _).symm
      rw [hcast, HeightOneSpectrum.valuation_of_algebraMap]
      by_cases hu : γ u ≤ 1
      · calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ 1 * 1 := mul_le_mul' ((hx u).trans hu) (u.intValuation_le_one _)
          _ = 1 := one_mul 1
      · have huS : u ∈ S := by
          simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hu
        have hmem : ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E) ∈ u.asIdeal ^ k u := by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w => N w ^ k w) huS
          rw [hc, Nat.cast_mul]
          apply Ideal.mul_mem_right
          rw [Nat.cast_pow]
          exact Ideal.pow_mem_pow (Ideal.absNorm_mem u.asIdeal) _
        have hle := (u.intValuation_le_pow_iff_mem _ (k u)).2 hmem
        have h0 : γ u ≠ 0 := by
          intro h; exact hu (h ▸ zero_le')
        calc u.valuation E x * u.intValuation ((∏ w ∈ S, N w ^ k w : ℕ) : 𝓞 E)
            ≤ γ u * WithZero.exp (-(k u : ℤ)) := mul_le_mul' (hx u) hle
          _ = WithZero.exp (WithZero.log (γ u) + -(k u : ℤ)) := by
              rw [WithZero.exp_add, WithZero.exp_log h0]
          _ ≤ 1 := by
              rw [← WithZero.exp_zero, WithZero.exp_le_exp]
              have := Int.self_le_toNat (WithZero.log (γ u))
              simp only [k]
              omega
    obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E
      (((∏ w ∈ S, N w ^ k w : ℕ) : E) * x) (fun u => by rw [map_mul, mul_comm]; exact hval u)
    exact ⟨a, by rw [← ha]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonIntegerDenominatorOfValuationBoundsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds : ∀ (E : Type) [Field E] [NumberField E] (γ : Pl E → WithZero (Multiplicative ℤ)), (∀ᶠ u in cofinite, γ u ≤ 1) → ∃ d : ℕ, d ≠ 0 ∧ ∀ x : E, (∀ u : Pl E, u.valuation E x ≤ γ u) → ∃ a : 𝓞 E, (a : E) = d * x := by
  first | exact @GlobalTheory.exists_nat_mul_integral_of_valuation_le | exact GlobalTheory.exists_nat_mul_integral_of_valuation_le | (intros; apply GlobalTheory.exists_nat_mul_integral_of_valuation_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConj
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem exists_mem_section_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S →
    ∀ u : Pl E, u ∉ S → ∃ w ∈ S, ∀ x : E, u.valuation E x = w.valuation E (IsCMField.complexConj E x) := by
  intro E _ _ _ S hS u hu
  obtain ⟨w, ⟨hwS, hwu⟩, -⟩ := hS u
  refine ⟨w, hwS, ?_⟩
  have hr : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr (IsCMField.complexConj_ne_one E) u w).1 hwu
    with h | h
  · exact absurd (h ▸ hwS) hu
  · intro x
    exact (h x).symm

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemSectionConjStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_section_valuation_eq_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Set (Pl E)), IsSection S → ∀ u : Pl E, u ∉ S → ∃ w ∈ S, ∀ x : E, u.valuation E x = w.valuation E (IsCMField.complexConj E x) := by
  first | exact @GlobalTheory.BCT.exists_mem_section_conj | exact GlobalTheory.BCT.exists_mem_section_conj | (intros; apply GlobalTheory.BCT.exists_mem_section_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFiel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFiel
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_roots_norm_one_coeff_denom_finite : ∀ (E : Type) [Field E] [NumberField E] (n d : ℕ), d ≠ 0 → {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k}.Finite := by
  intro E _ _ n d hd
  set T := {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k} with hT
  set B : ℝ := max 1 1 ^ n * (n.choose (n / 2) : ℝ) with hB
  set S : Set E := {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B} with hS
  have hSf : S.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ ((d : ℝ) * B)
  let F : E[X] → (Fin (n+1) → E) := fun P k => (d : E) * P.coeff k
  have hpi : (Set.pi Set.univ (fun _ : Fin (n+1) => S)).Finite := Set.Finite.pi (fun _ => hSf)
  have himg : F '' T ⊆ Set.pi Set.univ (fun _ : Fin (n+1) => S) := by
    rintro _ ⟨P, ⟨hm, hn, hr, hc⟩, rfl⟩ k _
    obtain ⟨a, ha⟩ := hc k
    refine ⟨?_, fun φ => ?_⟩
    · show IsIntegral ℤ ((d : E) * P.coeff k)
      rw [← ha]; exact a.isIntegral_coe
    · have hbd := Polynomial.coeff_bdd_of_roots_le (B := 1) (d := n) φ hm (IsAlgClosed.splits _) hn.le
        (fun z hz => (hr φ z hz).le) k
      rw [Polynomial.coeff_map] at hbd
      show ‖φ ((d : E) * P.coeff k)‖ ≤ (d : ℝ) * B
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)
  have hinj : Set.InjOn F T := by
    rintro P ⟨-, hP, -⟩ Q ⟨-, hQ, -⟩ hPQ
    ext k
    by_cases hk : k < n + 1
    · have := congrFun hPQ ⟨k, hk⟩
      simp only [F] at this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd) this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  exact Set.Finite.of_finite_image (hpi.subset himg) hinj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMonicUnitRootsBoundedDenominatorNumberFielStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_monic_unitRoots_bounded_denominator_numberField : ∀ (E : Type) [Field E] [NumberField E] (n d : ℕ), d ≠ 0 → {P : E[X] | P.Monic ∧ P.natDegree = n ∧ (∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) ∧ ∀ k, ∃ a : 𝓞 E, (a : E) = d * P.coeff k}.Finite := by
  first | exact @GlobalTheory.monic_roots_norm_one_coeff_denom_finite | exact GlobalTheory.monic_roots_norm_one_coeff_denom_finite | (intros; apply GlobalTheory.monic_roots_norm_one_coeff_denom_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGL
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptBound

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_le_exp (w : Pl E) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound_of_isCompact (w : Pl E) {S : Set (w.adicCompletion E)} (hS : IsCompact S) :
    ∃ γ : WithZero (Multiplicative ℤ), ∀ x ∈ S, Valued.v x ≤ γ := by
  have hcov : S ⊆ ⋃ m : ℕ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)} := by
    intro x _
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    rcases eq_or_ne (Valued.v x) 0 with h | h
    · exact ⟨0, by rw [h]; exact zero_le'⟩
    · refine ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
      conv_lhs => rw [← WithZero.exp_log h]
      rw [WithZero.exp_le_exp]
      exact Int.self_le_toNat _
  have hdir : Directed (· ⊆ ·) (fun m : ℕ => {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp (m : ℤ)}) :=
    Monotone.directed_le fun a b hab y (hy : _ ≤ _) =>
      (show _ ≤ _ from hy.trans (WithZero.exp_le_exp.2 (by exact_mod_cast hab)))
  obtain ⟨m, hm⟩ := hS.elim_directed_cover _ (fun m => isOpen_le_exp w _) hcov hdir
  exact ⟨_, fun x hx => hm hx⟩

theorem charpoly_coeff_eq {R : Type} [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    M.charpoly.coeff k = MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (MvPolynomial.map (Int.castRingHom R) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
  rw [MvPolynomial.eval_map]
  have h := Matrix.charpoly.univ_map_eval₂Hom (Fin n) (Int.castRingHom R) (fun ij : Fin n × Fin n => M ij.1 ij.2)
  have hM : Matrix.of (Function.curry fun ij : Fin n × Fin n => M ij.1 ij.2) = M := by
    ext i j; rfl
  rw [hM] at h
  rw [← h, Polynomial.coeff_map]
  rfl

end GlobalTheory.CptBound

namespace GlobalTheory.BCT

open GlobalTheory.CptBound

theorem charpoly_det_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C,
      (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  intro E _ _ _ n w C hC
  have hent : Continuous fun y : GLw n w => fun ij : Fin n × Fin n => y.val ij.1 ij.2 :=
    continuous_pi fun ij => Units.continuous_val.matrix_elem ij.1 ij.2
  have hco : ∀ k, Continuous fun y : GLw n w => y.val.charpoly.coeff k := by
    intro k
    have e : (fun y : GLw n w => y.val.charpoly.coeff k) = fun y : GLw n w =>
        MvPolynomial.eval (fun ij : Fin n × Fin n => y.val ij.1 ij.2)
          (MvPolynomial.map (Int.castRingHom (w.adicCompletion E)) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) :=
      funext fun y => charpoly_coeff_eq n y.val k
    rw [e]
    exact (MvPolynomial.continuous_eval _).comp hent
  have hdet : Continuous fun y : GLw n w => (y⁻¹ : GLw n w).val.det :=
    Units.continuous_coe_inv.matrix_det
  set S : Set (w.adicCompletion E) :=
    (⋃ k ∈ Finset.range (n + 1), (fun y : GLw n w => y.val.charpoly.coeff k) '' C) ∪
      ((fun y : GLw n w => (y⁻¹ : GLw n w).val.det) '' C) with hS
  have hSc : IsCompact S :=
    ((Finset.range (n + 1)).isCompact_biUnion fun k _ => hC.image (hco k)).union (hC.image hdet)
  obtain ⟨γ, hγ⟩ := exists_bound_of_isCompact w hSc
  refine ⟨γ, fun y hy => ⟨fun k => ?_, hγ _ (Or.inr ⟨y, hy, rfl⟩)⟩⟩
  by_cases hk : k < n + 1
  · exact hγ _ (Or.inl (Set.mem_biUnion (Finset.mem_range.2 hk) ⟨y, hy, rfl⟩))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega), map_zero]
    exact zero_le'

end GlobalTheory.BCT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffDetInvValuationBoundedOfIsCompactGLStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (C : Set (GLw n w)), IsCompact C → ∃ γ : WithZero (Multiplicative ℤ), ∀ y ∈ C, (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ γ := by
  first | exact @GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | exact GlobalTheory.BCT.charpoly_det_bounded_of_isCompact | (intros; apply GlobalTheory.BCT.charpoly_det_bounded_of_isCompact <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.FiniteEllipticCharpolysSupport
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinPolySupp

theorem int_pts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (y : GLw n w), y ∈ GlobalTheory.LFun.KGL w (n := n) → (∀ k, Valued.v (y.val.charpoly.coeff k) ≤ 1) ∧ Valued.v (y⁻¹ : GLw n w).val.det ≤ 1 := by
  intro E _ _ _ n w y hy
  obtain ⟨M, rfl⟩ := hy
  have hint : ∀ z : Ov E w, Valued.v (z : w.adicCompletion E) ≤ 1 := fun z =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 z.2
  refine ⟨fun k => ?_, ?_⟩
  · have : (bc (Ov E w).subtype M).val = (M.val).map (Ov E w).subtype := rfl
    rw [this, Matrix.charpoly_map, coeff_map]; exact hint _
  · rw [← map_inv]
    have : (bc (Ov E w).subtype M⁻¹).val = ((M⁻¹).val).map (Ov E w).subtype := rfl
    rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact hint _
end GlobalTheory.FinPolySupp

namespace GlobalTheory.FinPolySupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem val_alg (w : Pl E) (x : E) : Valued.v (algebraMap E (w.adicCompletion E) x) = w.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem pl_ext {u u' : Pl E} (h : ∀ x : E, u.valuation E x = u'.valuation E x) : u = u' := by
  apply HeightOneSpectrum.ext
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), h]

theorem transfer {n : ℕ} (w : Pl E) (y : GLw n w) (P : E[X]) (hP : y.val.charpoly = atPl w P)
    (γ : WithZero (Multiplicative ℤ))
    (h1 : ∀ k, Valued.v (y.val.charpoly.coeff k) ≤ γ) (h2 : Valued.v (y⁻¹ : GLw n w).val.det ≤ γ) :
    (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  have hc : ∀ k, algebraMap E (w.adicCompletion E) (P.coeff k) = y.val.charpoly.coeff k := by
    intro k; rw [hP, atPl, coeff_map]
  refine ⟨fun k => ?_, ?_⟩
  · rw [← val_alg, hc]; exact h1 k
  · rw [← val_alg, map_inv₀, hc]
    have hdet : y.val.det = (-1) ^ Fintype.card (Fin n) * y.val.charpoly.coeff 0 :=
      Matrix.det_eq_sign_charpoly_coeff _
    have hmul : (y⁻¹ : GLw n w).val.det * y.val.det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    have hinv : (y⁻¹ : GLw n w).val.det = (y.val.det)⁻¹ := eq_inv_of_mul_eq_one_left hmul
    have hv : Valued.v y.val.det = Valued.v (y.val.charpoly.coeff 0) := by
      rw [hdet, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul]
    rw [hinv, map_inv₀, hv] at h2
    rw [map_inv₀]; exact h2

theorem bound_at (n : ℕ) (w : Pl E) (f : UL n w → ℂ) (hf : HasCompactSupport f) :
    ∃ γ : WithZero (Multiplicative ℤ), (f = (KL n w : Set (UL n w)).indicator 1 → γ = 1) ∧
      ∀ P : E[X], (∃ y : UL n w, f y ≠ 0 ∧ y.1.val.charpoly = atPl w P) →
        (∀ k, w.valuation E (P.coeff k) ≤ γ) ∧ w.valuation E (P.coeff 0)⁻¹ ≤ γ := by
  by_cases hind : f = (KL n w : Set (UL n w)).indicator 1
  · refine ⟨1, fun _ => rfl, ?_⟩
    rintro P ⟨y, hy, hP⟩
    have hyK : y ∈ KL n w := by
      by_contra hn
      apply hy
      rw [hind]
      exact Set.indicator_of_notMem hn _
    have hy1 : y.1 ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf).1 hyK
    obtain ⟨h1, h2⟩ := int_pts E n w y.1 hy1
    exact transfer w y.1 P hP 1 h1 h2
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.charpoly_coeff_det_inv_valuation_bounded_of_isCompact_GL E n w (Subtype.val '' tsupport f) (hf.image continuous_subtype_val)
    refine ⟨γ, fun h => absurd h hind, ?_⟩
    rintro P ⟨y, hy, hP⟩
    obtain ⟨h1, h2⟩ := hγ y.1 ⟨y, subset_tsupport f hy, rfl⟩
    exact transfer w y.1 P hP γ h1 h2

theorem conj_coeff (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (k : ℕ) :
    IsCMField.complexConj E (P.coeff k) = if k ≤ n then P.coeff (n - k) * (P.coeff 0)⁻¹ else 0 := by
  obtain ⟨h0, hcsr⟩ := GlobalTheory.T.elliptic_charpoly_self_reciprocal E n P hP
  have hdeg : (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).natDegree = n := by
    rw [natDegree_map_eq_of_injective (RingHom.injective _)]; exact hP.2.1
  have key : ∀ j ≤ n, IsCMField.complexConj E (P.coeff 0) * P.coeff j =
      IsCMField.complexConj E (P.coeff (n - j)) := by
    intro j hj
    have := congrArg (fun Q => Q.coeff j) hcsr
    simp only [coeff_C_mul, coeff_reverse, hdeg, coeff_map] at this
    rw [revAt_le hj] at this
    exact this
  have hc0 : IsCMField.complexConj E (P.coeff 0) = (P.coeff 0)⁻¹ := by
    have := key 0 (Nat.zero_le _)
    have hn : P.coeff n = 1 := by rw [← hP.2.1]; exact hP.1
    rw [Nat.sub_zero, hn, map_one] at this
    exact eq_inv_of_mul_eq_one_left this
  split_ifs with hk
  · have := key (n - k) (Nat.sub_le n k)
    rw [Nat.sub_sub_self hk, hc0] at this
    rw [← this]; field_simp
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hP.2.1]; omega), map_zero]

theorem finpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ _ n S hS f hcpt hev
  choose γ hγ1 hγ using fun w => bound_at n w (f w) (hcpt w)
  have hpart := GlobalTheory.T.exists_mem_section_valuation_eq_conj E S hS
  let p : Pl E → Pl E := fun u => if h : u ∈ S then u else (hpart u h).choose
  have hpS : ∀ u, u ∉ S → p u ∈ S ∧ ∀ x : E, u.valuation E x = (p u).valuation E (IsCMField.complexConj E x) := by
    intro u hu; simp only [p, dif_neg hu]; exact (hpart u hu).choose_spec
  let Γ : Pl E → WithZero (Multiplicative ℤ) := fun u => if u ∈ S then γ u else γ (p u) * γ (p u)
  have hB : {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}.Finite := Filter.eventually_cofinite.1 hev
  have hΓ : ∀ᶠ u in cofinite, Γ u ≤ 1 := by
    rw [Filter.eventually_cofinite]
    have hsub : {u | ¬ Γ u ≤ 1} ⊆ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1} ∪
        {u | u ∉ S ∧ p u ∈ {w | ¬ f w = (KL n w : Set (UL n w)).indicator 1}} := by
      intro u hu
      by_cases huS : u ∈ S
      · left; intro hf; apply hu; simp [Γ, huS, hγ1 u hf]
      · right; refine ⟨huS, fun hf => hu ?_⟩; simp [Γ, huS, hγ1 _ hf]
    refine (hB.union ?_).subset hsub
    refine Set.Finite.of_finite_image (f := p) (hB.subset ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩; exact hu.2
    · intro u hu u' hu' he
      apply pl_ext; intro x
      rw [(hpS u hu.1).2, (hpS u' hu'.1).2, he]
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_common_integer_denominator_of_valuation_bounds E Γ hΓ
  refine (GlobalTheory.T.finite_monic_unitRoots_bounded_denominator_numberField E n d hd0).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP.1, hP.2.1, hP.2.2.2, fun k => hd _ fun u => ?_⟩
  by_cases huS : u ∈ S
  · simp only [Γ, if_pos huS]; exact (hγ u P (hPS u huS)).1 k
  · simp only [Γ, if_neg huS]
    obtain ⟨hpu, hv⟩ := hpS u huS
    obtain ⟨hb1, hb2⟩ := hγ (p u) P (hPS _ hpu)
    rw [hv, conj_coeff n P hP k]
    split_ifs
    · rw [map_mul]; exact mul_le_mul' (hb1 _) hb2
    · rw [map_zero]; exact zero_le'

end GlobalTheory.FinPolySupp
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.FiniteEllipticCharpolysSupportStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.finite_elliptic_charpolys_support : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ f : ∀ w : Pl E, UL n w → ℂ, (∀ w, HasCompactSupport (f w)) → (∀ᶠ w in (cofinite : Filter (Pl E)), f w = (KL n w : Set (UL n w)).indicator 1) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y : UL n w, f w y ≠ 0 ∧ y.1.val.charpoly = atPl w P}.Finite := by
  first | exact @GlobalTheory.FinPolySupp.finpoly | (intros; apply GlobalTheory.FinPolySupp.finpoly <;> assumption)
end
