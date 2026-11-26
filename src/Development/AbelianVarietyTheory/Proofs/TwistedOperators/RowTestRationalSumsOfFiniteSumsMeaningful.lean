module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OppositePathLocalTotalTensorMemCoefficientField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReprMemOfCoeff
noncomputable section

open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRat

theorem exists_proj (K' : Subfield ℂ) : ∃ φ : ℂ →ₗ[K'] ℂ, (∀ x : K', φ x = x) ∧ ∀ x, φ x ∈ K' := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' ℂ)
    (LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K' ℂ))
  refine ⟨(Algebra.linearMap K' ℂ).comp g, fun x => ?_, fun x => (g x).2⟩
  have h := congrArg (fun f => f x) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  show algebraMap K' ℂ (g (Algebra.linearMap K' ℂ x)) = algebraMap K' ℂ x
  rw [h]

theorem val_eq_sum_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) (v : VV ℂ lam) :
    v.1 = ∑ a, (bVV ℂ lam).repr v a • bVVfun ℂ lam a := by
  conv_lhs => rw [← (bVV ℂ lam).sum_repr v]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul, bVV_coe]

theorem coeff_mem_of_repr {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ a, (bVV ℂ lam).repr v a ∈ Set.range κ) (m : ι × Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ := by
  rw [val_eq_sum_repr, coeff_sum, ← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun a _ => ?_
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
  rw [coeff_smul, hP, coeff_map, smul_eq_mul]
  obtain ⟨x, hx⟩ := h a
  exact ⟨x * P.coeff m, by simp [hx]⟩

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open _root_.Formalism.L2.DIV MvPolynomial

theorem repr_mem_of_coeff {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L]
    (κ : L →+* ℂ) (v : VV ℂ lam) (h : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (a : VVIdx lam) :
    (bVV ℂ lam).repr v a ∈ Set.range κ := by
  set K' := κ.fieldRange
  obtain ⟨φ, hφ1, hφ2⟩ := exists_proj K'
  set c := fun a => (bVV ℂ lam).repr v a
  have hK : ∀ a m, AddMonoidAlgebra.coeff (bVVfun ℂ lam a) m ∈ K' := fun a m => by
    obtain ⟨P, hP⟩ := bVVfun_int ℂ lam a
    rw [hP, coeff_map]
    exact ⟨((AddMonoidAlgebra.coeff P m : ℤ) : L), by simp⟩
  have key : ∑ b, (c b - φ (c b)) • bVVfun ℂ lam b = 0 := by
    ext m
    have e1 : AddMonoidAlgebra.coeff v.1 m = ∑ b, c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      rw [val_eq_sum_repr, coeff_sum]; simp [c]
    have e2 : φ (AddMonoidAlgebra.coeff v.1 m) = AddMonoidAlgebra.coeff v.1 m := hφ1 ⟨_, RingHom.mem_fieldRange.2 (h m)⟩
    have e3 : φ (AddMonoidAlgebra.coeff v.1 m) = ∑ b, φ (c b) * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : c b * AddMonoidAlgebra.coeff (bVVfun ℂ lam b) m = (⟨_, hK b m⟩ : K') • c b := by
        rw [Subfield.smul_def, smul_eq_mul, mul_comm]
      rw [this, map_smul, Subfield.smul_def, smul_eq_mul, mul_comm]
    rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e3, e2, sub_self]
  have hz := Fintype.linearIndependent_iff.1 (bVVfun_spec ℂ lam).1 _ key a
  rw [sub_eq_zero] at hz
  have hc : c a ∈ K' := by rw [hz]; exact hφ2 _
  exact RingHom.mem_fieldRange.1 hc

end GlobalTheory.RowRat

namespace GlobalTheory.RowRat
open _root_.Formalism.L2.DIV MvPolynomial

theorem coeff_map_mem {ι : Type} [Fintype ι] {n n' : ℕ} {σ : ι → Formalism.BasicNotions.DomWeight n} {σ' : ι → Formalism.BasicNotions.DomWeight n'} {L : Type} [Field L] (κ : L →+* ℂ)
    (f : VV ℂ σ →ₗ[ℂ] VV ℂ σ') (hf : ∀ a b, (bVV ℂ σ').repr (f (bVV ℂ σ b)) a ∈ Set.range κ) (v : VV ℂ σ)
    (hv : ∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) (m : ι × Fin n' × Fin n' →₀ ℕ) :
    AddMonoidAlgebra.coeff (f v).1 m ∈ Set.range κ := by
  refine coeff_mem_of_repr σ' κ _ (fun a => ?_) m
  have e : f v = ∑ b, (bVV ℂ σ).repr v b • f (bVV ℂ σ b) := by
    conv_lhs => rw [← (bVV ℂ σ).sum_repr v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [← RingHom.coe_fieldRange]
  refine Subfield.sum_mem _ fun b _ => ?_
  exact Subfield.mul_mem _ (RingHom.mem_fieldRange.2 (repr_mem_of_coeff σ κ v hv b)) (RingHom.mem_fieldRange.2 (hf a b))

end GlobalTheory.RowRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedFlipTensorValuesMemCoeffField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedFlipTensorValuesMemCoeffField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest

theorem term_datum_mem_range : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  by_cases h0 : (ch.S.term t Φ β w).datum X Y = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hlc := GlobalTheory.T.flatIntegrand_flippedTensor_locallyConstant_compactSupport ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w X Y
  have hT := GlobalTheory.T.oppositePathLocalTotalTensor_mem_coefficientField ch large₂ F CF b hS hIs hSc hF t Φ hSum w.1 w.2
  have hM := GlobalTheory.T.movedTensorFactor_mem_coeffField ch large₂ F CF b hS hIs hSc hF t Φ hSum β hβ w _ hT
  show flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) _ X Y ∈ _
  refine GlobalTheory.T.integral_unfolding_variables_mem_fieldRange (unitVol w.1) (isUnitVol_unitVol w.1) D.what₂.embLL _ hlc.1 hlc.2 fun e => ?_
  simp only [flatIntegrand]
  by_cases hm : moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) (Tflip ch.W ch.S.B t Φ w)
      (fill one_le_sLen X Y e) = 0
  · rw [hm, zero_mul]; exact ⟨0, map_zero _⟩
  obtain ⟨a, ha⟩ := hM (fill one_le_sLen X Y e)
  obtain ⟨c, hc⟩ := hF.phases t Φ β hβ w X Y e h0 hm
  refine ⟨a * c⁻¹, ?_⟩
  rw [map_mul, map_inv₀, ha, hc, AddChar.map_neg_eq_inv, Circle.coe_inv]

end GlobalTheory.RowTest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedFlipTensorValuesMemCoeffFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) X Y, (ch.S.term t Φ β w).datum X Y ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.term_datum_mem_range | exact GlobalTheory.RowTest.term_datum_mem_range | (intros; apply GlobalTheory.RowTest.term_datum_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coeff

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem coeff_bVV_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (i : VVIdx lam) (m) :
    AddMonoidAlgebra.coeff ((bVV ℂ lam i : VV ℂ lam) : Pol ℂ ι n) m ∈ A := by
  obtain ⟨P, hP⟩ := bVVfun_int ℂ lam i
  rw [bVV_coe, hP, coeff_map]
  exact intCast_mem A _

theorem coeff_mem_of_repr_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ i, (bVV ℂ lam).repr v i ∈ A) (m) : AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A := by
  have e := congrArg (fun x : VV ℂ lam => AddMonoidAlgebra.coeff (x : Pol ℂ ι n) m) ((bVV ℂ lam).sum_repr v)
  simp only [Submodule.coe_sum, Submodule.coe_smul, coeff_sum, coeff_smul, smul_eq_mul] at e
  rw [← e]
  exact sum_mem fun i _ => mul_mem (h i) (coeff_bVV_mem A lam i m)

theorem repr_mem_of_coeff_mem (A : Subfield ℂ) (lam : ι → DomWeight n) (v : VV ℂ lam)
    (h : ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A) (i : VVIdx lam) : (bVV ℂ lam).repr v i ∈ A := by
  classical
  choose P hP using fun j => bVVfun_int ℂ lam j
  let s : A →+* ℂ := A.subtype
  let b' : VVIdx lam → MvPolynomial (ι × Fin n × Fin n) A := fun j => map (Int.castRingHom A) (P j)
  have hb' : ∀ j, map s (b' j) = ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) := fun j => by
    rw [bVV_coe, hP, map_map]
    congr 1
  obtain ⟨v', hv'⟩ : ∃ v' : MvPolynomial (ι × Fin n × Fin n) A, map s v' = (v : Pol ℂ ι n) := by
    obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := s)).2 (fun c hc => by
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
      exact ⟨⟨_, h m⟩, rfl⟩)
    exact ⟨F', hF'⟩
  have hliC : LinearIndependent ℂ fun j => ((bVV ℂ lam j : VV ℂ lam) : Pol ℂ ι n) :=
    (bVV ℂ lam).linearIndependent.map' (VV ℂ lam).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent A b' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have e := congrArg (map s) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zero, smul_eq_C_mul, map_mul, map_C, hb'] at e
    have e' : ∑ k, (s (g k)) • ((bVV ℂ lam k : VV ℂ lam) : Pol ℂ ι n) = 0 := by
      simpa only [smul_eq_C_mul] using e
    have := Fintype.linearIndependent_iff.1 hliC (fun k => s (g k)) e' j
    exact Subtype.ext this
  have hspan : v' ∈ Submodule.span A (Set.range b') := by
    by_contra hn
    have hopt : LinearIndependent A (fun o : Option (VVIdx lam) => Option.casesOn' o v' b') :=
      (linearIndependent_option' (x := v') (v := b')).2 ⟨hli, hn⟩
    have hC := Formalism.L2.Col.linearIndependent_map s _ hopt
    have hC' : LinearIndependent ℂ (fun o : Option (VVIdx lam) =>
        Option.casesOn' o (map s v') fun j => map s (b' j)) := by
      convert hC using 1
      funext o
      cases o <;> rfl
    obtain ⟨-, hnot⟩ := (linearIndependent_option' (x := map s v') (v := fun j => map s (b' j))).1 hC'
    apply hnot
    rw [hv']
    have hvs := congrArg (fun x : VV ℂ lam => (x : Pol ℂ ι n)) ((bVV ℂ lam).sum_repr v)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hvs
    rw [← hvs]
    exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hb' j⟩)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 hspan
  have hvc : v = ∑ j, (s (c j)) • bVV ℂ lam j := by
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv', ← hc, map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, ← hb', smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  rw [hvc, (bVV ℂ lam).repr_sum_self]
  exact (c i).2

theorem coeff_map_mem {ι' : Type} [Fintype ι'] {n' : ℕ} (A : Subfield ℂ) (lam : ι → DomWeight n)
    (mu : ι' → DomWeight n') (f : VV ℂ lam →ₗ[ℂ] VV ℂ mu)
    (hf : ∀ a b, LinearMap.toMatrix (bVV ℂ lam) (bVV ℂ mu) f a b ∈ A) (v : VV ℂ lam)
    (hv : ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A) (m) : AddMonoidAlgebra.coeff ((f v : VV ℂ mu) : Pol ℂ ι' n') m ∈ A := by
  classical
  refine coeff_mem_of_repr_mem A mu (f v) (fun a => ?_) m
  rw [← LinearMap.toMatrix_mulVec_repr (bVV ℂ lam) (bVV ℂ mu) f v, Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hf a b) (repr_mem_of_coeff_mem A lam v hv b)

theorem coeff_rhoVr_mem {E : Type} [Field E] (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) (A : Subfield ℂ)
    (hA : ∀ τ x, emb τ x ∈ A) (γE : GL (Fin n) E) (v : VV ℂ lam) (hv : ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ ι n) m ∈ A) (m) :
    AddMonoidAlgebra.coeff ((rhoVr emb lam γE v : VV ℂ lam) : Pol ℂ ι n) m ∈ A := by
  classical
  let R₀ : Subring (Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, AddMonoidAlgebra.coeff F m ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (AddMonoidAlgebra.coeff F' m).2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show AddMonoidAlgebra.coeff (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Pol ℂ ι n)) m ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end Coeff

theorem chainTo_preserves {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (k : ∀ j, V j →ₗ[ℂ] V (j + 1))
    (P : ∀ j, V j → Prop) (hk : ∀ j v, P j v → P (j + 1) (k j v)) : ∀ N v, P 0 v → P N (GlobalTheory.FunObj.chainTo k N v)
  | 0, _, hv => hv
  | N + 1, v, hv => hk N _ (chainTo_preserves k P hk N v hv)

end GlobalTheory.RowTest.ColField

namespace GlobalTheory.RowTest.ColField

open MvPolynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem colMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, AddMonoidAlgebra.coeff u.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.colMap d (ch.S.ptTop c) u).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ _ β hβ τ hτ d hd c u hu
  let K : Subfield ℂ := D.what₂.embLL.fieldRange
  have memK : ∀ z : ℂ, z ∈ K ↔ z ∈ Set.range D.what₂.embLL := fun z => Iff.rfl
  have hE : ∀ (σ : D.what₂.Tau) (x : D.host.E), tauE D σ x ∈ K := fun σ x =>
    ⟨labLL D σ x, GlobalTheory.Mem.R3.BrgRead.embLL_labLL_eq σ x⟩
  have hrat := (hF.isRatAt hβ hτ hd c).1
  have hu' : ∀ m, AddMonoidAlgebra.coeff (u : Pol ℂ D.what₂.Tau (ch.G.V (.top 0)).rank) m ∈ K := fun m => (memK _).2 (hu m)
  have h0 := coeff_rhoVr_mem (tauE D) (wt ch.G (.top 0)) K hE (ch.S.N.fr (.top 0))⁻¹ u hu'
  have hchain := chainTo_preserves (V := fun j => VV ℂ (wt ch.G (.top j)))
    (fun j => if h : j < D.R.m then ch.S.Z.kkMap 1 (d.1 ⟨j, h⟩) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) else 0)
    (fun j v => ∀ m, AddMonoidAlgebra.coeff (v : Pol ℂ D.what₂.Tau (ch.G.V (.top j)).rank) m ∈ K) (fun j v hv => by
      by_cases h : j < D.R.m
      · simp only [dif_pos h]
        exact coeff_map_mem K _ _ _ (fun a b => (memK _).2 (hrat ⟨j, h⟩ a b)) v hv
      · simp only [dif_neg h, LinearMap.zero_apply, ZeroMemClass.coe_zero,
          AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
        exact fun _ => zero_mem K) D.R.m _ h0
  intro m
  exact (memK _).1 (hchain m)

end GlobalTheory.RowTest.ColField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopRowNormalisedKernelChainPreservesCoeffsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (u : VV ℂ (wt ch.G (.top 0))), (∀ m, AddMonoidAlgebra.coeff u.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.colMap d (ch.S.ptTop c) u).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowTest.ColField.colMap_coeff_mem | exact GlobalTheory.RowTest.ColField.colMap_coeff_mem | (intros; apply GlobalTheory.RowTest.ColField.colMap_coeff_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRange
open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowFun

theorem coeff_mem_of_mul_eq {s : Type} (K' : Subfield ℂ) (f P Q : MvPolynomial s ℂ) (hP : P ≠ 0)
    (hPK : ∀ m, AddMonoidAlgebra.coeff P m ∈ K') (hQ : ∀ m, AddMonoidAlgebra.coeff Q m ∈ K') (h : f * P = Q) :
    ∀ m, AddMonoidAlgebra.coeff f m ∈ K' := by
  classical
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.RowRat.exists_proj K'
  let g : MvPolynomial s ℂ := ∑ m ∈ f.support, monomial m (φ (AddMonoidAlgebra.coeff f m))
  have hg : ∀ m, AddMonoidAlgebra.coeff g m = φ (AddMonoidAlgebra.coeff f m) := by
    intro m
    simp only [g, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [notMem_support_iff.mp hm, map_zero]
  have key : g * P = f * P := by
    ext m
    have hfix : AddMonoidAlgebra.coeff (f * P) m = φ (AddMonoidAlgebra.coeff (f * P) m) := by
      rw [h]; exact (hφ1 ⟨_, hQ m⟩).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hfix, coeff_mul, coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hg]
    have hs := φ.map_smul (⟨AddMonoidAlgebra.coeff P x.2, hPK _⟩ : K') (AddMonoidAlgebra.coeff f x.1)
    rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul] at hs
    rw [mul_comm, ← hs, mul_comm]
  have hgf : g = f := mul_right_cancel₀ hP key
  intro m
  rw [← hgf, hg]
  exact hφ2 _

theorem coeff_funOf_mem_range {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type}
    [Field L] (κ : L →+* ℂ) (hR : GlobalTheory.FunObj.ReadOK σ) (F : VV ℂ σ)
    (hF : ∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) :
    ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  classical
  have hf := hR.1 F
  unfold GlobalTheory.FunObj.IsFunForm at hf
  let G : MvPolynomial (ι × Fin n × Fin n) L :=
    ∑ m ∈ (F.1 : MvPolynomial (ι × Fin n × Fin n) ℂ).support,
      monomial m (Function.invFun κ (AddMonoidAlgebra.coeff F.1 m))
  have hG : MvPolynomial.map κ G = F.1 := by
    ext m
    rw [coeff_map]
    simp only [G, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
    split_ifs with hm
    · exact Function.invFun_eq (hF m)
    · simp [notMem_support_iff.mp hm]
  have hmem : ∀ (p : MvPolynomial (ι × Fin n × Fin n) L) m,
      AddMonoidAlgebra.coeff (MvPolynomial.map κ p) m ∈ κ.fieldRange := fun p m => by
    rw [coeff_map]; exact RingHom.mem_fieldRange_self κ _
  have hmem_eq₁ : MvPolynomial.map κ (∏ τ, Formalism.L2.Ker.frDet L n τ ^ ∑ a, (σ τ).natW a)
      = ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ ∑ a, (σ τ).natW a := by
    simp only [map_prod, map_pow, GlobalTheory.BrRat.map_frDet]
  have hmem_eq₂ : MvPolynomial.map κ (GlobalTheory.FunObj.dualSubst L ι n G *
      ∏ τ, Formalism.L2.Ker.frDet L n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat)
      = GlobalTheory.FunObj.dualSubst ℂ ι n F.1 *
      ∏ τ, Formalism.L2.Ker.frDet ℂ n τ ^ (-(σ τ).dual.detShift - (σ τ).detShift).toNat := by
    simp only [map_mul, map_prod, map_pow, GlobalTheory.BrRat.map_frDet, GlobalTheory.BrRat.map_dualSubst, hG]
  intro m
  have := coeff_mem_of_mul_eq κ.fieldRange _ _ _
    (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (GlobalTheory.FunObj.funFrDet_ne_zero τ))
    (fun m => by
      rw [← hmem_eq₁]; exact hmem _ m)
    (fun m => by
      rw [← hmem_eq₂]; exact hmem _ m) hf m
  exact RingHom.mem_fieldRange.mp this

end GlobalTheory.RowFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CovariantVectorToFunctionFormCoeffMemRangeStatement
open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} (σ : ι → Formalism.BasicNotions.DomWeight n) {L : Type} [Field L] (κ : L →+* ℂ), GlobalTheory.FunObj.ReadOK σ → ∀ (F : VV ℂ σ), (∀ m, AddMonoidAlgebra.coeff F.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff (GlobalTheory.FunObj.funOf σ F).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowFun.coeff_funOf_mem_range | exact GlobalTheory.RowFun.coeff_funOf_mem_range | (intros; apply GlobalTheory.RowFun.coeff_funOf_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRange
open Formalism.L2.DIV MvPolynomial

namespace GlobalTheory.RowRho

theorem coeff_rhoVr_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  classical
  intro ι _ n E _ emb L _ κ hA0 lam γE v hv0 m
  set A : Subfield ℂ := κ.fieldRange with hAdef
  have hA : ∀ τ x, emb τ x ∈ A := fun τ x => RingHom.mem_fieldRange.2 (hA0 τ x)
  have hv : ∀ m, AddMonoidAlgebra.coeff (v : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A := fun m => RingHom.mem_fieldRange.2 (hv0 m)
  rw [← RingHom.coe_fieldRange]
  show AddMonoidAlgebra.coeff ((rhoVr emb lam γE v : VV ℂ lam) : Formalism.L2.DIV.Pol ℂ ι n) m ∈ A
  let R₀ : Subring (Formalism.L2.DIV.Pol ℂ ι n) := (MvPolynomial.map A.subtype).range
  have memR : ∀ F : Formalism.L2.DIV.Pol ℂ ι n, F ∈ R₀ ↔ ∀ m, AddMonoidAlgebra.coeff F m ∈ A := by
    intro F
    constructor
    · rintro ⟨F', rfl⟩ m
      rw [coeff_map]
      exact (AddMonoidAlgebra.coeff F' m).2
    · intro h
      obtain ⟨F', hF'⟩ := (mem_range_map_iff_coeffs_subset (f := A.subtype)).2 (fun c hc => by
        obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.1 hc
        exact ⟨⟨_, h m⟩, rfl⟩)
      exact ⟨F', hF'⟩
  have hblock : ∀ M : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ a b, M τ a b ∈ A) → ∀ F ∈ R₀,
      Formalism.GradedWeylDivisibility.blockAct ℂ M F ∈ R₀ := by
    intro M hM F hF
    obtain ⟨F', rfl⟩ := hF
    induction F' using MvPolynomial.induction_on with
    | C a =>
      rw [map_C, Formalism.GradedWeylDivisibility.blockAct, aeval_C]
      exact ⟨C a, by rw [map_C]; rfl⟩
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem hp hq
    | mul_X p w hp =>
      rw [map_mul, map_mul, map_X]
      refine mul_mem hp ?_
      rw [Formalism.GradedWeylDivisibility.blockAct, aeval_X]
      exact sum_mem fun b _ => mul_mem ⟨C ⟨_, hM _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩
  have hent : ∀ τ a b, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b ∈ A := by
    intro τ a b
    show ((((Formalism.UG.bc (emb τ) γE)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) b a ∈ A
    rw [← map_inv]
    exact hA τ _
  have hdet : ∀ τ, ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ∈ A := by
    intro τ
    have e := RingHom.map_det A.subtype (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A))
    rw [show A.subtype.mapMatrix (Matrix.of fun a b => (⟨_, hent τ a b⟩ : A)) =
      ((invTrK (embGL emb γE) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) from Matrix.ext fun a b => rfl] at e
    rw [← e]
    exact SetLike.coe_mem _
  have hdt : detTwK lam (invTrK (embGL emb γE)) ∈ A := by
    unfold detTwK
    refine prod_mem fun τ _ => ?_
    unfold Formalism.BasicNotions.detPow
    rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact zpow_mem (hdet τ) _
  have htr : Formalism.L2.DIV.trAct (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n) ∈ R₀ :=
    hblock _ (fun τ a b => hent τ b a) _ ((memR _).2 hv)
  show AddMonoidAlgebra.coeff (Formalism.L2.DIV.actP lam (invTrK (embGL emb γE)) (v : Formalism.L2.DIV.Pol ℂ ι n)) m ∈ A
  rw [Formalism.L2.DIV.actP, LinearMap.smul_apply, coeff_smul, smul_eq_mul]
  exact mul_mem hdt ((memR _).1 htr m)

end GlobalTheory.RowRho
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffCoefficientSpaceActionMemRangeStatement
open Formalism.L2.DIV MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_coefficientSpaceAction_mem_range : ∀ {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E] (emb : ι → E →+* ℂ) {L : Type} [Field L] (κ : L →+* ℂ), (∀ (τ : ι) (x : E), emb τ x ∈ Set.range κ) → ∀ (lam : ι → Formalism.BasicNotions.DomWeight n) (g : GL (Fin n) E) (v : VV ℂ lam), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range κ) → ∀ m, AddMonoidAlgebra.coeff ((rhoVr emb lam g) v).1 m ∈ Set.range κ := by
  first | exact @GlobalTheory.RowRho.coeff_rhoVr_mem_range | exact GlobalTheory.RowRho.coeff_rhoVr_mem_range | (intros; apply GlobalTheory.RowRho.coeff_rhoVr_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.RowRat
open _root_.Formalism.L2.DIV MvPolynomial

theorem embLL_labLL {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem rowMap_coeff_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.rowMap d (ch.S.ptRow c) v).1 m ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ hF t Φ hSum β hβ τ hτ d hd c v hv
  have h0 := GlobalTheory.T.covariantVectorToFunctionForm_coeff_mem_range _ D.what₂.embLL hSum.read.1 v hv
  have h1 := GlobalTheory.T.coeff_coefficientSpaceAction_mem_range (tauE D) D.what₂.embLL (fun τ x => ⟨labLL D τ x, embLL_labLL τ x⟩) _
    (ch.S.N.fr (.grid 0 D.R.m))⁻¹ _ h0
  have gen : ∀ (k : ∀ i, VV ℂ (wt ch.G (.grid i D.R.m)) →ₗ[ℂ] VV ℂ (wt ch.G (.grid (i + 1) D.R.m))),
      (∀ i (w : VV ℂ (wt ch.G (.grid i D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (k i w).1 m ∈ Set.range D.what₂.embLL) →
      ∀ j (w : VV ℂ (wt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff w.1 m ∈ Set.range D.what₂.embLL) →
        ∀ m, AddMonoidAlgebra.coeff (chainTo (V := fun i => VV ℂ (wt ch.G (.grid i D.R.m))) k j w).1 m ∈ Set.range D.what₂.embLL := by
    intro k hk j
    induction j with
    | zero => intro w hw; exact hw
    | succ j ih => intro w hw; exact hk j _ (ih w hw)
  simp only [GlobalTheory.FunObj.GridChoice.rowMap, LinearMap.comp_apply]
  refine gen _ (fun i w hw m => ?_) D.R.m _ h1
  split_ifs with h
  · refine coeff_map_mem _ _ ?_ w hw m
    intro a b
    have := (hF.isRatAt hβ hτ hd c).2 ⟨i, h⟩ a b
    simpa [GlobalTheory.FunObj.Normal.IsRatAt, GlobalTheory.FunObj.Normal.IsRatIn, GlobalTheory.FunObj.Normal.kkIn, LinearMap.toMatrix_apply] using this
  · exact ⟨0, by simp⟩

end GlobalTheory.RowRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastColumnNormalizedKernelChainCoeffFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ → ∀ d ∈ τ.support, ∀ (c : ch.S.Classes t Φ β) (v : VV ℂ (listedWt ch.G (.grid 0 D.R.m))), (∀ m, AddMonoidAlgebra.coeff v.1 m ∈ Set.range D.what₂.embLL) → ∀ m, AddMonoidAlgebra.coeff (ch.S.rowMap d (ch.S.ptRow c) v).1 m ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.RowRat.rowMap_coeff_mem | exact GlobalTheory.RowRat.rowMap_coeff_mem | (intros; apply GlobalTheory.RowRat.rowMap_coeff_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningful
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowTest.SumRat

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem natCast_cpow_half (N : ℕ) (n : ℤ) : (N : ℂ) ^ ((n : ℂ) / 2) = ((Real.sqrt N : ℝ) : ℂ) ^ n := by
  have h1 : (N : ℂ) = ((N : ℝ) : ℂ) := by simp
  rw [h1, show ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

theorem sAA_mem (ch : Choice R) (h : ch.FieldOK) : ch.S.sAA ∈ D.what₂.embLL.fieldRange := by
  classical
  unfold GridChoice.sAA
  refine Subfield.prod_mem _ fun w hw => ?_
  obtain ⟨n, hn, -⟩ := aaScalar_eq_pow ch.W w (hasConductor_psiAt_AA ch.W w)
  have hq : GlobalTheory.SplitWeil.resCard (Kw w) = Ideal.absNorm w.asIdeal := GlobalTheory.LFun.SatBoundGL.resCard_completion w
  have hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ D.what₂.embLL.fieldRange := by
    obtain ⟨y, hy⟩ := h.sqrt w (Or.inl hw)
    exact ⟨y, hy⟩
  rw [hn, hq, natCast_cpow_half]
  exact zpow_mem hs n

theorem psiC_rat (ch : Choice R) (a : Fin ch.n) (g : FinPt ch.G (.top 0)) (m) :
    AddMonoidAlgebra.coeff (psiC (ch.Psi a) g).1 m ∈ Set.range D.what₂.embLL := by
  show AddMonoidAlgebra.coeff ((GlobalTheory.CoefModel.mapVV D.what₂.embLL (LaP ch.G) (ch.Psi a (finG (Xp ch.G) g))).1) m ∈ _
  simp [GlobalTheory.CoefModel.mapVV, MvPolynomial.coeff_map]

theorem vK_mem (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ) (hS : HidaSetting large₂ R F) (hi : ch.Is)
    (hsc : ch.AtScale CF b) (hK : ch.FieldOK) (hO : ∀ t a, ch.S.SumOK t (ch.Phi a)) (t : T) (x : A.fam.amb.FR t)
    (a : Fin ch.n) : vK ch t x a ∈ D.what₂.embLL.fieldRange := by
  classical
  have hR : ∀ z, z ∈ Set.range D.what₂.embLL → z ∈ D.what₂.embLL.fieldRange := fun z ⟨y, hy⟩ => ⟨y, hy⟩
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have h := hO t a
  have hex : ∀ β ∈ ch.S.supp t (ch.Phi a), ∃ τ, IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) τ :=
    fun β hβ => exists_cosetExpansion_expDepth hL ch.S.toGridChoice t (ch.Phi a) β (h.ex β hβ)
  let τf : CosFam ch.G t → PureDat ch.G t →₀ ℂ := fun β =>
    if hβ : β ∈ ch.S.supp t (ch.Phi a) then (hex β hβ).choose else 0
  have hτf : ∀ β (hβ : β ∈ ch.S.supp t (ch.Phi a)), IsCosetExpansion ch.S.toGridChoice t (ch.Phi a) β
      (expDepth ch.S.toGridChoice t (ch.Phi a) β) (τf β) := fun β hβ => by
    simp only [τf, dif_pos hβ]; exact (hex β hβ).choose_spec
  show ch.S.sAA * ch.S.vCore t (ch.Phi a) (psiC (ch.Psi a)) (ch.S.formC t (R.jX t x)) ∈ D.what₂.embLL.fieldRange
  refine mul_mem (sAA_mem ch hK) ?_
  rw [h.vCore_eq τf fun β hβ => (hτf β hβ).2.1]
  refine sum_mem fun β hβ' => ?_
  have hβ : β ∈ ch.S.supp t (ch.Phi a) := (Set.Finite.mem_toFinset _).1 hβ'
  refine mul_mem (prod_mem fun w _ => SubfieldClass.ratCast_mem _ _) ?_
  unfold GridChoice.classSum
  haveI := h.cls β
  haveI := Fintype.ofFinite (ch.S.Classes t (ch.Phi a) β)
  rw [finsum_eq_sum_of_fintype]
  refine sum_mem fun c _ => mul_mem ?_ ?_
  · unfold GridChoice.invGam
    exact mul_mem (prod_mem fun j _ => inv_mem (natCast_mem _ _)) (prod_mem fun i _ => inv_mem (natCast_mem _ _))
  · unfold GridChoice.pairAt
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply, smul_eq_mul]
    refine sum_mem fun d hd => mul_mem ?_ ?_
    · obtain ⟨X, Y, e⟩ := (hτf β hβ).coef_eq hd
      rw [e]
      exact prod_mem fun w _ => hR _ (GlobalTheory.T.unfoldedFlipTensor_values_mem_coeffField ch large₂ F CF b hS hi hsc hK t _ h β hβ w _ _)
    · have hU := GlobalTheory.T.topRow_normalisedKernelChain_preserves_coeffs ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _ (psiC_rat ch a (ch.S.ptTop c 0))
      have hV := GlobalTheory.T.lastColumn_normalizedKernelChain_coeffField ch large₂ F hS hi hK t _ h β hβ _ (hτf β hβ) d hd c _
        (GlobalTheory.T.rationalForm_coordinates_coeff_mem_coefficientField ch large₂ F hS hi hK t x (ch.S.ptRow c 0))
      exact hR _ (GlobalTheory.T.branchingPairing_mem_coefficientField ch large₂ F hS hi hK t _ h (ch.S.colMap d (ch.S.ptTop c) (psiC (ch.Psi a) (ch.S.ptTop c 0)))
        (ch.S.rowMap d (ch.S.ptRow c) (ch.S.formC t (R.jX t x) (ch.S.ptRow c 0))) hU hV)

end GlobalTheory.RowTest.SumRat

namespace GlobalTheory.RowTest

theorem sumRatK_of_sumOKK : SumOKK → SumRatK := by
  rintro ⟨CF0, h⟩
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hC
  refine ⟨x₀, fun D large₂ e hx' Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc hK t x a => ?_⟩
  obtain ⟨y, hy⟩ := SumRat.vK_mem ch large₂ F CF large₂.sc.b s hi hsc hK (hx D large₂ e hx' Γ Pl0 T A Ks R F s ch hi hsc) t x a
  exact ⟨y, hy⟩

end GlobalTheory.RowTest

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningfulStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful : GlobalTheory.RowClaim.SumOKK → GlobalTheory.RowClaim.SumRatK := by
  first | exact @GlobalTheory.RowTest.sumRatK_of_sumOKK | exact GlobalTheory.RowTest.sumRatK_of_sumOKK | (intros; apply GlobalTheory.RowTest.sumRatK_of_sumOKK <;> assumption)
end
