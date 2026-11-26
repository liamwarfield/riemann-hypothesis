module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepExistenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorDefiniteUnitaryConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorDefiniteUnitaryConjugate
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem exists_nat_denom {ι : Type} [Fintype ι] (a : ι → Af E) :
    ∃ d : ℕ, 0 < d ∧ ∀ (k : ι) (w : Pl E),
      (d : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
  choose N hN h using fun k => GlobalTheory.AdeleDenom.exists_nat_mul_integral E (a k)
  refine ⟨∏ k, N k, Finset.prod_pos fun k _ => hN k, fun k w => ?_⟩
  have h' : (N k : w.adicCompletion E) * pLoc E w (a k) ∈ w.adicCompletionIntegers E := by
    have := h k w
    rwa [show ((N k : Af E) * a k) w = pLoc E w ((N k : Af E) * a k) from rfl, map_mul, map_natCast] at this
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) h'

theorem cLoc_val (k : finU (E := E) (n := n)) (w : Pl E) (i j : Fin n) :
    (cLoc w (k : UA E n)).val i j = pLoc E w ((FinPart.pU k).val i j) := rfl

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU (E := E) (n := n), ∃ d : ℕ, 0 < d ∧ ∀ g : finU (E := E) (n := n), (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  intro E _ _ _ n S hS x
  obtain ⟨D₁, hD₁, h₁⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x).val k.1 k.2
  obtain ⟨D₂, hD₂, h₂⟩ := exists_nat_denom (E := E) (ι := Fin n × Fin n) fun k => (FinPart.pU x⁻¹).val k.1 k.2
  have key : ∀ (h : finU (E := E) (n := n)) (w : Pl E), cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) →
      ∀ i j, ((D₁ * D₂ : ℕ) : w.adicCompletion E) * (cLoc w (h : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
    intro h w hk i j
    have e : (h : UA E n) = (x : UA E n) * ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n) * ((x⁻¹ : finU (E := E) (n := n)) : UA E n) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e1 : (D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₁ (i, a) w
    have e2 : (D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j ∈ w.adicCompletionIntegers E := by
      rw [cLoc_val]; exact h₂ (b, j) w
    have e3 := GlobalTheory.BCT.LocCpt.entry_mem_of_mem_KGL hk a b
    have e4 : ((D₁ * D₂ : ℕ) : w.adicCompletion E) * ((cLoc w (x : UA E n)).val i a *
        (cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n)).val a b * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j) =
        ((D₁ : w.adicCompletion E) * (cLoc w (x : UA E n)).val i a) * (cLoc w ((x⁻¹ * h * x : finU (E := E) (n := n)) : UA E n)).val a b *
        ((D₂ : w.adicCompletion E) * (cLoc w ((x⁻¹ : finU (E := E) (n := n)) : UA E n)).val b j) := by
      push_cast; ring
    rw [e4]
    exact mul_mem (mul_mem e1 e3) e2
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, fun g hg w i j => ?_⟩
  rcases GlobalTheory.BCT.LocCpt.mem_or_conj_mem hS w with hw | hw
  · exact key g w (hg w hw) i j
  · have hinv : cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((x⁻¹ * g⁻¹ * x : finU (E := E) (n := n)) : UA E n) ∈
        GlobalTheory.LFun.KGL (conjSrc (GlobalTheory.SplitPts.conjE E) w) (n := n) := by
      have : (x⁻¹ * g⁻¹ * x : finU (E := E) (n := n)) = (x⁻¹ * g * x)⁻¹ := by group
      rw [this, Subgroup.coe_inv, map_inv]
      exact (GlobalTheory.LFun.KGL _ (n := n)).inv_mem (hg _ hw)
    have h1 := key g⁻¹ _ hinv j i
    have e2 : (cLoc w (g : UA E n)).val i j = conjLoc (GlobalTheory.SplitPts.conjE E) w
        ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) ((g⁻¹ : finU (E := E) (n := n)) : UA E n)).val j i) := by
      rw [GlobalTheory.BCT.LocCpt.cLoc_eq_invT]
      show ((GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w)
        (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) (g : UA E n)))⁻¹).val j i = _
      rw [← map_inv, ← map_inv, Subgroup.coe_inv]
      rfl
    rw [e2, ← map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) (D₁ * D₂), ← map_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, (conjLoc_spec _ w).2.2]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h1

end GlobalTheory.BCT.StabDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorDefiniteUnitaryConjugateStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ x : finU (E := E) (n := n), ∃ d : ℕ, 0 < d ∧ ∀ g : finU (E := E) (n := n), (∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n)) → ∀ (w : Pl E) (i j : Fin n), (d : w.adicCompletion E) * (cLoc w (g : UA E n)).val i j ∈ w.adicCompletionIntegers E := by
  first | exact @GlobalTheory.BCT.StabDenom.exists_denom | exact GlobalTheory.BCT.StabDenom.exists_denom | (intros; apply GlobalTheory.BCT.StabDenom.exists_denom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNumberFieldBddDenomConjNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNumberFieldBddDenomConjNormLeOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NumFin

theorem finite_bdd_denom_conj_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  intro E _ _ d hd
  have hd0 : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  set S := {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} with hS
  have hF := NumberField.Embeddings.finite_of_norm_le E ℂ (d : ℝ)
  have himg : (fun z : E => (d : E) * z) '' S ⊆ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ)} := by
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E ((d : E) * z) fun w => by
        have h := hz1 w
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
        convert h using 2
        rw [← map_natCast (algebraMap E (w.adicCompletion E)) d, ← map_mul]
        rfl
      show IsIntegral ℤ ((d : E) * z)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
      calc (d : ℝ) * ‖φ z‖ ≤ (d : ℝ) * 1 := by gcongr; exact hz2 φ
        _ = d := mul_one _
  have hinj : Set.InjOn (fun z : E => (d : E) * z) S := fun a _ b _ h => mul_left_cancel₀ hd0 h
  exact Set.Finite.of_finite_image (hF.subset himg) hinj

end GlobalTheory.NumFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNumberFieldBddDenomConjNormLeOneStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ), 0 < d → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1}.Finite := by
  first | exact @GlobalTheory.NumFin.finite_bdd_denom_conj_le_one | exact GlobalTheory.NumFin.finite_bdd_denom_conj_le_one | (intros; apply GlobalTheory.NumFin.finite_bdd_denom_conj_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLe
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

theorem norm_emb_entry_le_one (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n)
    (τ : E →+* ℂ) (i j : Fin n) : ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  set M : Matrix (Fin n) (Fin n) E := (γ : GL (Fin n) E).val with hM
  have h : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom M * 1 * M = 1 := γ.2
  rw [Matrix.mul_one] at h
  have hjj : ∑ k, IsCMField.complexConj E (M k j) * M k j = 1 := by
    have := congrFun₂ h j j
    simpa [Formalism.UG.cT, Matrix.mul_apply] using this
  have hτ : ∑ k, ((Complex.normSq (τ (M k j)) : ℝ) : ℂ) = 1 := by
    have := congrArg τ hjj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsCMField.complexEmbedding_complexConj, Complex.normSq_eq_conj_mul_self]
  have hR : ∑ k, Complex.normSq (τ (M k j)) = 1 := by exact_mod_cast hτ
  have hle : Complex.normSq (τ (M i j)) ≤ 1 := by
    rw [← hR]
    exact Finset.single_le_sum (f := fun k => Complex.normSq (τ (M k j))) (fun k _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i)
  have hsq : ‖τ (M i j)‖ ^ 2 ≤ 1 := by rw [Complex.sq_norm]; exact hle
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hsq

end GlobalTheory.BCT.FinPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEmbeddingEntryDefiniteUnitaryRationalPointLeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n) (τ : E →+* ℂ) (i j : Fin n), ‖τ ((γ : GL (Fin n) E).val i j)‖ ≤ 1 := by
  first | exact @GlobalTheory.BCT.FinPart.norm_emb_entry_le_one | exact GlobalTheory.BCT.FinPart.norm_emb_entry_le_one | (intros; apply GlobalTheory.BCT.FinPart.norm_emb_entry_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.StabFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cLoc_finPt (γ : UE E n) (w : Pl E) (i j : Fin n) :
    (cLoc w ((finPt γ : finU (E := E) (n := n)) : UA E n)).val i j = algebraMap E (w.adicCompletion E) ((γ : GL (Fin n) E).val i j) :=
  congrArg (fun g : GL (Fin n) (Af E) => pLoc E w (g.val i j)) (GlobalTheory.BCT.FinPart.pU_finPt γ)

theorem cLoc_conj_mem_KGL {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (hK : IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K') (x g : finU (E := E) (n := n))
    (hg : g ∈ (globLev S K').map (MulAut.conj x).toMonoidHom) :
    ∀ w ∈ S, cLoc w ((x⁻¹ * g * x : finU (E := E) (n := n)) : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro w hw
  obtain ⟨k, hk, e⟩ := Subgroup.mem_map.1 hg
  have e' : x⁻¹ * g * x = k := by
    rw [← e]
    simp [MulAut.conj_apply, mul_assoc]
  rw [e']
  have hk' : ∀ u ∈ S, ∃ a ∈ K' u, (a : GLw n u) = cLoc u k.1 := by
    simpa [globLev, Subgroup.mem_iInf] using hk
  obtain ⟨a, ha, hae⟩ := hk' w hw
  rw [← hae]
  exact Subgroup.mem_subgroupOf.1 ((hK.1 w).2.1 ha)

end GlobalTheory.BCT.StabFin


open GlobalTheory.BCT.StabFin in
theorem GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  intro E _ _ _ _ n _ S hS K' hK x
  obtain ⟨d, hd, hC⟩ := GlobalTheory.T.exists_bounded_denominator_definiteUnitary_conjugate E n S hS x
  haveI : Finite {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) * algebraMap E (w.adicCompletion E) z ∈
      w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1} := (GlobalTheory.T.finite_numberField_bdd_denom_conj_norm_le_one E d hd).to_subtype
  have hrat := (GlobalTheory.BCT.FinPart.finPt_props E n).2.2
  let γ : ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) → UE E n :=
    fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose
  have hγ : ∀ g, finPt (γ g) = g.1 := fun g => ((hrat g.1).1 (Subgroup.mem_inf.1 g.2).1).choose_spec
  refine Finite.of_injective (β := Fin n → Fin n → {z : E | (∀ w : HeightOneSpectrum (𝓞 E), (d : w.adicCompletion E) *
      algebraMap E (w.adicCompletion E) z ∈ w.adicCompletionIntegers E) ∧ ∀ τ : E →+* ℂ, ‖τ z‖ ≤ 1})
    (fun g i j => ⟨((γ g : UE E n) : GL (Fin n) E).val i j, fun w => by
        have := hC g.1 (cLoc_conj_mem_KGL hK x g.1 (Subgroup.mem_inf.1 g.2).2) w i j
        rwa [← hγ g, cLoc_finPt] at this,
      fun τ => GlobalTheory.T.norm_embedding_entry_definiteUnitaryRationalPoint_le_one E n (γ g) τ i j⟩) fun g g' e => ?_
  have e1 : γ g = γ g' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg Subtype.val (congrFun (congrFun e i) j)
  apply Subtype.ext
  rw [← hγ g, ← hγ g', e1]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevelStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  first | exact @GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev | exact GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev | (intros; apply GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmHomGramMatrixDetNeZeroDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmHomGramMatrixDetNeZeroDefinite
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem exists_isGram_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, h⟩ := GlobalTheory.FlatCM.GramExists.exists_isGram E H K ρ σ₁ p 0 X
  exact ⟨gP, gQ, h, (GlobalTheory.GramAt.gram_det X h).1⟩

end GlobalTheory.FlatCM.HomLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmHomGramMatrixDetNeZeroDefiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  first | exact @GlobalTheory.FlatCM.HomLat.exists_isGram_det_ne_zero | exact GlobalTheory.FlatCM.HomLat.exists_isGram_det_ne_zero | (intros; apply GlobalTheory.FlatCM.HomLat.exists_isGram_det_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPow
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.FlatCM.RosatiCoord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {σ₁ : K →+* ℂ} {A B : PAT H (Sp (𝓞 K))}

theorem weilEq_prod_snd {I₀ : Type} (f : A.t.G ⟶ B.t.G) (hf : IsMonHom f)
    (G : I₀ → (A.t.G ⟶ B.t.G)) (hG : ∀ i, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (G i)) (r : I₀ → 𝓞 E)
    (h : ∀ i, WeilEq B.t.PP.L f (G i) A.t.PP.L (A.t.act.act (r i)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    {T : Finset I₀} (hT : T.Nonempty) :
    WeilEq B.t.PP.L f (∏ i ∈ T, G i) A.t.PP.L (A.t.act.act (∑ i ∈ T, r i)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => simpa using h a
  | cons a s has hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    have hs' : GlobalTheory.Serre.IsLinearHom A.t.act B.t.act (∏ i ∈ s, G i) :=
      Finset.prod_induction _ (GlobalTheory.Serre.IsLinearHom A.t.act B.t.act) (fun f g hf hg => hf.mul hg)
        (GlobalTheory.Serre.IsLinearHom.one _ _) fun i _ => hG i
    exact GlobalTheory.T.weilPairingCompatible_add_second_position_complex E H K σ₁ A B f (G a) _ hf (hG a).isMonHom hs'.isMonHom _ _ (h a) ih

theorem exists_mul_eq_gram_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p q X gP gQ hG n x f hn hf hfx a
  have hφ : ∀ b, GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act (phiP X b) := fun b => X.lin (Sum.inl b)
  obtain ⟨r, hr⟩ := GlobalTheory.FlatCM.GramExists.exists_weilEq_entry E H K ρ σ₁ (X.A true) X.B 1 0 X.ρ_sq rfl X.typeP
    (phiP X a) f (hφ a) hf
  have h1 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun _ : ℕ => f) (fun _ => hf) (fun _ => r) (fun _ => hr)
    (Finset.nonempty_range_iff.2 hn.ne')
  rw [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hfx] at h1
  have h2 := weilEq_prod_snd (phiP X a) (hφ a).isMonHom (fun b => (X.A true).t.act.act (x b) ≫ phiP X b)
    (fun b => (GlobalTheory.Serre.IsLinearHom.act _ _).comp (hφ b)) (fun b => gP a b * H.bar (x b))
    (fun b => GlobalTheory.T.weilPairingCompatible_scalar_second_position_conj E H K σ₁ (X.A true) X.B _ _ (hφ a).isMonHom (hφ b).isMonHom _ (x b) (hG.1 a b))
    (T := Finset.univ) ⟨a, Finset.mem_univ a⟩
  exact ⟨r, GlobalTheory.T.scalar_eq_of_weilPairing_eq_principalCMTriple E H K ρ σ₁ (X.A true) X.ρ_sq X.typeP _ _ fun k u v e hk hu hv =>
    (h1 k u v e hk hu hv).symm.trans (h2 k u v e hk hu hv)⟩

end GlobalTheory.FlatCM.RosatiCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRosatiCoordinatesDivisibleOfPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p q) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin q) (Fin q) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ → ∀ (n : ℕ) (x : Fin p → 𝓞 E) (f : (X.A true).t.G ⟶ X.B.t.G), 0 < n →
    GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f →
    f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ GlobalTheory.FlatCM.phiP X a) →
    ∀ a, ∃ y : 𝓞 E, (n : 𝓞 E) * y = ∑ b, gP a b * H.bar (x b) := by
  first | exact @GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum | exact GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum | (intros; apply GlobalTheory.FlatCM.RosatiCoord.exists_mul_eq_gram_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFg
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

theorem lat_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, hG, hdet⟩ := GlobalTheory.T.exists_cmHomGramMatrix_det_ne_zero_definite E H hH K ρ σ₁ p X
  set N : 𝓞 E := H.bar.symm gP.det with hNdef
  have hN0 : N ≠ 0 := fun h => hdet (by simpa [hNdef] using congrArg H.bar h)
  have hN : (N : E) ≠ 0 := by exact_mod_cast hN0
  have key : ∀ c ∈ GlobalTheory.FlatCM.HomLat.coords X, ∀ b, ∃ z : 𝓞 E, (z : E) = (N : E) * c b := by
    rintro c ⟨n, hn, x, hx, f, hf, hfx⟩ b
    choose y hy using GlobalTheory.T.exists_rosatiCoordinates_divisible_of_pow E H hH K ρ σ₁ p 0 X gP gQ hG n x f hn hf hfx
    have hmv : gP.mulVec (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * y a := by
      funext a; simp [Matrix.mulVec, dotProduct, hy]
    have hadj : gP.det • (fun b => H.bar (x b)) = fun a => (n : 𝓞 E) * gP.adjugate.mulVec y a := by
      have := congrArg gP.adjugate.mulVec hmv
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec] at this
      rw [this]; funext a; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    have hb := congrArg H.bar.symm (congrFun hadj b)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply, map_natCast] at hb
    refine ⟨H.bar.symm (gP.adjugate.mulVec y b), ?_⟩
    have hnE : ((n : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hn.ne'
    apply mul_left_cancel₀ hnE
    have h2 : ((N : 𝓞 E) : E) * ((x b : 𝓞 E) : E) =
        (n : E) * ((H.bar.symm (gP.adjugate.mulVec y b) : 𝓞 E) : E) := by
      rw [hNdef]; exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hb
    push_cast
    rw [← h2, hx b]; ring
  let incl : (Fin p → 𝓞 E) →ₗ[𝓞 E] (Fin p → E) :=
    LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)
  let scal : (Fin p → E) →ₗ[𝓞 E] (Fin p → E) := N • LinearMap.id
  have hscal : Function.Injective scal := by
    intro v w h
    funext i
    have := congrFun h i
    simp only [scal, LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, Algebra.smul_def] at this
    exact mul_left_cancel₀ hN this
  apply Submodule.fg_of_fg_map_injective scal hscal
  refine Submodule.FG.of_le (T := LinearMap.range incl) ?_ ?_
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map incl
  · rw [GlobalTheory.FlatCM.HomLat.lat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    choose z hz using key c hc
    refine ⟨z, ?_⟩
    funext b
    simp [incl, scal, hz, Algebra.smul_def]

end GlobalTheory.FlatCM.HomLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLinearHomCoordinateLatticeFgStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLinearHomCoordinateLattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    (GlobalTheory.FlatCM.HomLat.lat X).FG := by
  first | exact @GlobalTheory.FlatCM.HomLat.lat_fg | exact GlobalTheory.FlatCM.HomLat.lat_fg | (intros; apply GlobalTheory.FlatCM.HomLat.lat_fg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpace
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameRead.ExPhi

theorem res_eq {ι : Type} {n : ℕ} {lam : ι → DomWeight n} {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) :
    res n (lamW τ) = fun a => (lam τ).natW a + lamW τ (n - 1) := by
  funext a
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) a.2
  have h1 := h τ a
  have h2 := h τ ⟨n - 1, by omega⟩
  have h3 : (lam τ).w ⟨n - 1, by omega⟩ ≤ (lam τ).w a := (lam τ).anti (by
    rw [Fin.le_def]; have := a.2; simp only; omega)
  simp only [res, DomWeight.natW, DomWeight.detShift, dif_pos hn] at h2 ⊢
  omega

theorem liftPol_mem {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} {n : ℕ} {lam : ι → DomWeight n}
    {lamW : ι → ℕ → ℕ} {c : ι → ℤ} (h : Shift lam lamW c) (τ : ι) (x : MvPolynomial (Fin n × Fin n) K)
    (hx : x ∈ nablaSq K n (lam τ)) : liftPol e0 (lamW τ (n - 1)) x ∈ dualWeyl C n n (res n (lamW τ)) := by
  rw [res_eq h τ]
  exact GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl C n _ _ _ (dualWeylMap K C e0 n n _ x hx)

theorem ssB_span (K : Type) [Field K] {n : ℕ} (ν : Fin n → ℕ) :
    Submodule.span K (Set.range (ssB K ν)) = dualWeyl K n n ν :=
  (Formalism.GradedWeylDivisibility.sSBasis K n n ν).choose_spec.1.2.1

theorem ssB_mem (K : Type) [Field K] {n : ℕ} (l : DomWeight n) (j : ssIdx n n l.natW) : ssB K l.natW j ∈ nablaSq K n l := by
  unfold nablaSq
  rw [← ssB_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem detPol_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : detPol R n ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [detPol, RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (Matrix.of fun a s => X (a, s)) = (1 : Matrix (Fin n) (Fin n) R) := by
    ext a s; simp
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem linInd_map {F K σ ι : Type} [Field F] [Field K] (e : F →+* K) {v : ι → MvPolynomial σ F}
    (hv : LinearIndependent F v) : LinearIndependent K (fun i => MvPolynomial.map e (v i)) := by
  classical
  letI : Algebra F K := e.toAlgebra
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul] at h1 ⊢
    change ∑ x ∈ s, c x * e ((v x).coeff m) = 0 at h1
    change ∑ x ∈ s, (B.repr (c x)) j * (v x).coeff m = 0
    have h2 := congrArg (fun x => B.repr x j) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zero, Finsupp.finsetSum_apply, Finsupp.coe_zero, Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : c i * e (AddMonoidAlgebra.coeff (v i) m) = AddMonoidAlgebra.coeff (v i) m • c i := by
      rw [Algebra.smul_def, mul_comm]; rfl
    rw [h3, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

def semiConstr {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M] [Fintype I]
    (e : K →+* C) (b : Module.Basis I K V) (t : I → M) : V →ₛₗ[e] M where
  toFun v := ∑ i, e (b.repr v i) • t i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum, mul_smul]

theorem semiConstr_basis {K C V M I : Type} [Field K] [Field C] [AddCommGroup V] [Module K V] [AddCommGroup M] [Module C M]
    [Fintype I] (e : K →+* C) (b : Module.Basis I K V) (t : I → M) (i : I) : semiConstr e b t (b i) = t i := by
  classical
  change ∑ j, e (b.repr (b i) j) • t j = t i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj.symm]
  · simp

def mulMap (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) :
    NablaT C n lamW →ₗ[C] Pol C ι n :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra C ι (Pol C ι n)).compLinearMap fun τ =>
    (blockEmb C τ).toLinearMap ∘ₗ (dualWeyl C n n (res n (lamW τ))).subtype)

theorem mulMap_tprod (C : Type) [Field C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ)
    (y : ∀ τ, dualWeyl C n n (res n (lamW τ))) :
    mulMap C n lamW (PiTensorProduct.tprod C y) = ten fun τ => (y τ : MvPolynomial (Fin n × Fin n) C) := by
  simp [mulMap, ten]

theorem ten_liftPol {K C : Type} [Field K] [Field C] (e0 : K →+* C) {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ)
    (x : ι → MvPolynomial (Fin n × Fin n) K) :
    (ten fun τ => liftPol e0 (k τ) (x τ)) = (ten fun τ => detPol C n ^ k τ) * MvPolynomial.map e0 (ten x) := by
  simp only [ten, liftPol, map_mul, map_prod, Finset.prod_mul_distrib, blockEmb, map_rename]

theorem ten_det_ne_zero (C : Type) [Field C] {ι : Type} [Fintype ι] {n : ℕ} (k : ι → ℕ) :
    (ten fun τ => detPol C n ^ k τ) ≠ 0 := by
  unfold ten
  refine Finset.prod_ne_zero_iff.2 fun τ _ => ?_
  intro h
  have hinj : Function.Injective (blockEmb C (k := n) (n := n) τ) :=
    rename_injective _ fun a b hab => (Prod.mk.inj hab).2
  exact pow_ne_zero _ (detPol_ne_zero C n) (hinj (h.trans (map_zero _).symm))

theorem exists_phi (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (h : Shift lam lamW c) :
    ∃ Φ : VV K lam →ₛₗ[e0] NablaT C n lamW, IsPhi e0 lam lamW Φ ∧ LinearIndependent C fun i => Φ (bVV K lam i) := by
  classical
  let u : ∀ τ, ssIdx n n (lam τ).natW → dualWeyl C n n (res n (lamW τ)) := fun τ j =>
    ⟨liftPol e0 (lamW τ (n - 1)) (ssB K (lam τ).natW j), liftPol_mem e0 h τ _ (ssB_mem K _ j)⟩
  let t : VVIdx lam → NablaT C n lamW := fun i => PiTensorProduct.tprod C fun τ => u τ (i τ)
  refine ⟨semiConstr e0 (bVV K lam) t, ?_, ?_⟩
  · intro x v hx hv
    haveI : ∀ τ, Fintype (ssIdx n n (lam τ).natW) := fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).fintype
    have hex : ∀ τ, ∃ a : ssIdx n n (lam τ).natW → K, ∑ j, a j • ssB K (lam τ).natW j = x τ := fun τ => by
      have h1 := hx τ
      unfold nablaSq at h1
      rw [← ssB_span] at h1
      exact (Submodule.mem_span_range_iff_exists_fun K).1 h1
    choose a ha using hex
    have hv' : v = ∑ i : VVIdx lam, (∏ τ, a τ (i τ)) • bVV K lam i := by
      apply Subtype.ext
      rw [hv]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Submodule.coe_sum, Submodule.coe_smul, bVV_coe, bVVfun, ten, ← ha, map_sum, map_smul]
      rw [Finset.prod_univ_sum]
      simp only [Finset.prod_smul]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext i; simp
    refine ⟨fun τ => ∑ j, e0 (a τ j) • u τ j, fun τ => ?_, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [Submodule.coe_sum, Submodule.coe_smul, u, liftPol, ← ha, map_sum, Finset.mul_sum, smul_eq_C_mul, map_mul, map_C]
        refine Finset.sum_congr rfl fun j _ => by ring
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [MultilinearMap.map_sum, hv', map_sum]
        simp only [LinearMap.map_smulₛₗ, semiConstr_basis, MultilinearMap.map_smul_univ, map_prod]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext i; simp
  · simp only [semiConstr_basis]
    refine LinearIndependent.of_comp (mulMap C n lamW) ?_
    have h1 := linInd_map e0 (bVVfun_spec K lam).1
    have h2 := h1.map' (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1)))
      (LinearMap.ker_eq_bot.2 (mul_right_injective₀ (ten_det_ne_zero C _)))
    have h3 : (mulMap C n lamW ∘ t) = (LinearMap.mulLeft C (ten fun τ => detPol C n ^ lamW τ (n - 1))) ∘
        fun i => MvPolynomial.map e0 (bVVfun K lam i) := by
      funext i
      simp only [Function.comp, t, mulMap_tprod, u, ten_liftPol, LinearMap.mulLeft_apply, bVVfun]
    exact h3 ▸ h2

end GlobalTheory.FrameRead.ExPhi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualWeylTensorLiftCoefficientSpaceStatement
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualWeylTensor_lift_coefficientSpace : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ), Shift lam lamW c → ∃ Φ : VV K lam →ₛₗ[e0] NablaT C n lamW, IsPhi e0 lam lamW Φ ∧ LinearIndependent C fun i => Φ (bVV K lam i) := by
  first | exact @GlobalTheory.FrameRead.ExPhi.exists_phi | exact GlobalTheory.FrameRead.ExPhi.exists_phi | (intros; apply GlobalTheory.FrameRead.ExPhi.exists_phi <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantsJetsLocalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantsJetsLocalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem dual_isLocalRing [IsLocalRing W] : IsLocalRing (DualNumber W) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

theorem fstHom_isLocalHom : IsLocalHom (TrivSqZeroExt.fstHom W W W).toRingHom :=
  ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩

abbrev red (W : Type) [CommRing W] : Sp W ⟶ Sp (DualNumber W) := spMap (TrivSqZeroExt.fstHom W W W).toRingHom

theorem red_closedPoint [IsLocalRing W] :
    letI := dual_isLocalRing (W := W)
    (red W).base (IsLocalRing.closedPoint W) = IsLocalRing.closedPoint (DualNumber W) := by
  letI := dual_isLocalRing (W := W)
  haveI := fstHom_isLocalHom (W := W)
  rw [Spec.map_base]
  exact IsLocalRing.comap_closedPoint _

theorem top_le_of_red [IsLocalRing W] {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U) : ⊤ ≤ y ⁻¹ᵁ U := by
  letI := dual_isLocalRing (W := W)
  rw [Scheme.preimage_eq_top_of_closedPoint_mem y (U := U) ?_]
  have := h (show IsLocalRing.closedPoint W ∈ (⊤ : (Sp W).Opens) from trivial)
  rw [← red_closedPoint]
  exact this

theorem valR_fst {X : Scheme.{0}} (y : Sp (DualNumber W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (f : Γ(X, U)) :
    (valR y U f).fst = valR (red W ≫ y) U f := by
  have h' : ⊤ ≤ (red W ≫ y) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage]; exact fun p _ => h trivial
  unfold valR
  rw [dif_pos h, dif_pos h', ← Scheme.Hom.appLE_comp_appLE (red W) y U ⊤ ⊤ h le_top]
  have n := congrArg (fun q => q.hom ((y.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.fstHom W W W).toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
  rw [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [show (red W).appLE ⊤ ⊤ le_top = (red W).appTop from (Scheme.Hom.app_eq_appLE _).symm]
  exact n.symm

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

open TrivSqZeroExt

variable {W : Type} [CommRing W]

theorem epsLift_fst {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (fst (baseOver (Sp W)) A).left = (epsR W).hom := by
  rw [epsLift, ← Over.comp_left, lift_fst]; rfl

theorem epsLift_snd {A : Over (Sp W)} [GrpObj A] (u : epsR W ⟶ A) :
    epsLift u ≫ (snd (baseOver (Sp W)) A).left = u.left := by
  rw [epsLift, ← Over.comp_left, lift_snd]

theorem red_epsLift {A : Over (Sp W)} [GrpObj A] (v v' : epsR W ⟶ A) (hv : IsTangent v) (hv' : IsTangent v') :
    red W ≫ epsLift v = red W ≫ epsLift v' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, ← Over.fst_left, epsLift_fst, epsLift_fst]
  · rw [Category.assoc, Category.assoc, ← Over.snd_left, epsLift_snd, epsLift_snd]
    exact hv.trans hv'.symm

theorem red_epsLift_snd {A : Over (Sp W)} [GrpObj A] (v : epsR W ⟶ A) (hv : IsTangent v) :
    (red W ≫ epsLift v) ≫ (snd (baseOver (Sp W)) A).left = 𝟙 (Sp W) ≫ eSec A := by
  rw [Category.assoc, epsLift_snd, Category.id_comp]
  exact hv

open Classical in
theorem exists_jets [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) {I : Type}
    (t : I → LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W))))) {g : ℕ} (v : Fin g → (epsR W ⟶ P.A))
    (hv : ∀ j, IsTangent (v j)) :
    ∃ (i₀ : P.L.ι) (c : Fin g → W) (ϑ : I → W) (J : I → Fin g → W),
      ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ ∧
      ∀ i j, valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl (ϑ i) + TrivSqZeroExt.inr (J i j + c j * ϑ i)) := by
  have hL := P.isLB
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((eSec P.A : Sp W ⟶ P.A.left).base (IsLocalRing.closedPoint W))
  have htop : ⊤ ≤ (𝟙 (Sp W) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ := by
    rw [Category.id_comp, Scheme.preimage_eq_top_of_closedPoint_mem (eSec P.A : Sp W ⟶ P.A.left) hi₀]
  have hρt : ⊤ ≤ (𝟙 (Sp W)) ⁻¹ᵁ ((P.L.pull (eSec P.A)).U fun _ => i₀) := fun p _ =>
    Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      exact this
  set u := valR (𝟙 (Sp W)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val with hu_def
  have hu : IsUnit u := by
    rw [hu_def, valR, dif_pos hρt]
    exact ((ρ.s _).isUnit.map _).map _
  set ui := Ring.inverse (u ^ k)
  have hui : u ^ k * ui = 1 := Ring.mul_inverse_cancel _ (hu.pow k)
  have hch : ∀ j, ⊤ ≤ (epsLift (v j)) ⁻¹ᵁ ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) := fun j =>
    top_le_of_red _ _ fun p _ => Set.mem_iInter.2 fun _ => by
      have := htop (show p ∈ (⊤ : (Sp W).Opens) from trivial)
      rw [← red_epsLift_snd (v j) (hv j)] at this
      exact this
  refine ⟨i₀, 0, fun i => if hn : Nonempty (Fin g) then
      ui * (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst else 0,
    fun i j => ui * (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).snd, htop, fun i j => ?_⟩
  have hn : Nonempty (Fin g) := ⟨j⟩
  simp only [dif_pos hn]
  have hf : (valR (epsLift (v hn.some)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀)
        ((t i).f fun _ => i₀)).fst =
      (valR (epsLift (v j)) ((LPow P.A P.L (k : ℤ) (Over.mk (𝟙 (Sp W)))).U fun _ => i₀) ((t i).f fun _ => i₀)).fst := by
    rw [valR_fst _ _ (hch _), valR_fst _ _ (hch _), red_epsLift _ _ (hv _) (hv j)]
  rw [hf]
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]
  · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, add_zero, Pi.zero_apply, zero_mul,
      smul_eq_mul, MulOpposite.smul_eq_mul_unop, zero_add, MulOpposite.unop_op]
    rw [← _root_.mul_assoc, hui, _root_.one_mul]

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow.JetEx

variable {W : Type} [CommRing W]

theorem exists_symLift_tr [IsNoetherianRing W] [IsLocalRing W] (P : PolAV (Sp W)) (ρ : LB.Gen (P.L.pull (eSec P.A)))
    (hρ : ρ.IsGen) (m : ℕ) (hm : Odd m) (hmu : IsUnit (m : W))
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))) (x : Over.mk (𝟙 (Sp W)) ⟶ P.A)
    (hx : x ^ (m ^ 2) = 1) :
    ∃ (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))
      (t : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (Over.mk (𝟙 (Sp W))))),
      SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧ Tr P ρ m th U t := by
  have hLaw : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL := P.isLB
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp W, ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    exact (by rw [Nat.cast_pow]; exact hmu.pow 2 : IsUnit ((m ^ 2 : ℕ) : W)).map e
  obtain ⟨hex, -⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex (IsLocalRing.closedPoint W)
  have hVt : V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem (𝟙 (Sp W)) hV
  subst hVt
  let h : T ⟶ overRes (T := T) ⊤ := Over.homMk T.left.topIso.inv (by
    show T.left.topIso.inv ≫ (⊤ : T.left.Opens).ι ≫ T.hom = T.hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp])
  have hh : h ≫ overResι (T := T) ⊤ = 𝟙 T := Over.OverMorphism.ext T.left.toIso_inv_ι
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull hL h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P m
  have e₁ : (snd T P.A).left ≫ (mulA P.A m).left = (snd T P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α₁, hα₁, -⟩ := exists_gen hL (φ' := ![(snd T P.A).left, (snd T P.A ^ m).left])
    (ε' := ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow m 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd T P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨α, hα, hn⟩ := GlobalTheory.NormTheta.exists_normalised hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) (by simp) α₁ hα₁
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A θ.pt) (translPt P.A θ.pt) (lift_snd _ _)
    ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
  exact ⟨θ, t, hθ, α, s₁, hα, hn, hs₁, ht⟩

end GlobalTheory.MBLow.JetEx

namespace GlobalTheory.MBLow

theorem exists_thJet_local : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (x : KeyIn W)
    (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → IsUnit (m : W) → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ x.P.A)),
    (∀ i, pt i ^ (m ^ 2) = 1) → ∃ ϑ J, ThJet x hg m pt ϑ J := by
  intro W _ _ _ _ x g hg m hm hmu I pt hpt
  choose U t hUt using fun i =>
    JetEx.exists_symLift_tr x.P x.rig x.rig_gen m hm hmu (TrSec.thSec x.P x.th) (pt i) (hpt i)
  obtain ⟨i₀, c, ϑ, J, htop, hval⟩ :=
    JetEx.exists_jets x.P x.rig (m ^ 2) t (fun j => x.v (j.cast hg.symm)) (fun j => x.basis.1 _)
  exact ⟨ϑ, J, TrSec.thSec x.P x.th, TrSec.projectionPullbackSectionBaseProduct_isInverseImage x.P x.th, U, t, i₀, c, fun i => hUt i, htop, hval⟩

end GlobalTheory.MBLow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantsJetsLocalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstantsJets_localDomain : ∀ (W : Type) [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsLocalRing W] (x : KeyIn W) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → IsUnit (m : W) → ∀ (I : Type) (pt : I → (baseOver (Sp W) ⟶ x.P.A)), (∀ i, pt i ^ (m ^ 2) = 1) → ∃ ϑ J, ThJet x hg m pt ϑ J := by
  first | exact @GlobalTheory.MBLow.exists_thJet_local | exact GlobalTheory.MBLow.exists_thJet_local | (intros; apply GlobalTheory.MBLow.exists_thJet_local <;> assumption)
end
end
