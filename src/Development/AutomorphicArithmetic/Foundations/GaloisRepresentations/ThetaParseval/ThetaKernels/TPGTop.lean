module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.MemClosureOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedWeilRepresentationConvergence
public import Development.WeilBound.ThetaLifts.LatticeBasics.HermCpt
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplit
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThConst
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
public import Development.WeilBound.ThetaLifts.LatticeBasics.OrthAn
public import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStd
public import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwo
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.WeilEx
public import Development.WeilBound.ThetaLifts.Reductions.LieScalar2
public import Development.WeilBound.ThetaLifts.Reductions.LocalLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGHgtFst
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRealPair
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGNonVan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsWeilLatticeDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGSchurStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGLiftAut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGReadLift
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGBumpAny
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsSeparatingOfNotMemLatticeCoset
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LatAtVSelfDualK
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PsiSympLatAtVK
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.LatVacArith
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F : Type} [Field F] [NumberField F]
section Gen
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
end Gen
section Main
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
end Main
end GlobalTheory.LatVacArith
namespace GlobalTheory.LatVacArith
section Final
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem psi_symp_latAtV_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (θ : 𝓞 E) (b : AF F),
    GlobalTheory.AdelicU.evFin F v b ∈ v.adicCompletionIntegers F →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') = 1 := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY v θ b hb γ hγ γ' hγ'
  have step : ∀ z' ∈ {z | ∃ a : AF F, At (GlobalTheory.AdelicU.evFin F v) a ∧ GlobalTheory.AdelicU.evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ x ∈ X.L, ∃ y ∈ Y.L, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (Matrix.vecMulVec x y)},
      ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, B.ψ (b * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ z') = 1 := by
    intro z' hz' γ hγ
    obtain ⟨a', -, ha', x', hx', y', hy', rfl⟩ := hz'
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, x, hx, y, hy, rfl⟩ := hz
      exact psi_gen σ B X Y hX hY hB.std v θ b hb ha hav ha' hx hx' hy hy'
    | zero => rw [symp_zero_left, mul_zero, AddChar.map_zero_eq_one]
    | add x y _ _ hx hy =>
      rw [symp_add_left, mul_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
    | neg x _ hx =>
      rw [symp_neg_left, mul_neg, AddChar.map_neg_eq_inv, hx, inv_one]
  induction hγ' using AddSubgroup.closure_induction with
  | mem z hz => exact step z hz γ hγ
  | zero => rw [symp_zero_right, mul_zero, AddChar.map_zero_eq_one]
  | add x y _ _ hx hy =>
    rw [symp_add_right, mul_add, AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx =>
    rw [symp_neg_right, mul_neg, AddChar.map_neg_eq_inv, hx, inv_one]
end Final
end GlobalTheory.LatVacArith
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Idele WithZero
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff)
noncomputable section
namespace GlobalTheory.LatSelfDualAll
section Scalar
variable {F : Type} [Field F] [NumberField F]
end Scalar
section Lat
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Lat
end GlobalTheory.LatSelfDualAll
namespace GlobalTheory.LatSelfDualAll
section Frame
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Frame
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Gen
end GlobalTheory.LatSelfDualAll
namespace GlobalTheory.LatSelfDualAll
open GlobalTheory.InertSelfDual (exists_traceFamily det_ne_zero_of_herm det_ne_zero_of_skew decomp hTens_frame trace_expand)
theorem latAtV_selfDual_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B →
    X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) z →
      (z ∈ latAtV X W v ↔ ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B n d X W r₁ s₁ r₂ s₂ hB hX hW v z hz
  constructor
  · intro hzm γ hγ
    have h := _root_.GlobalTheory.LatVacArith.psi_symp_latAtV_k σ B X W _ _ _ _ hB hX hW v (-1) 1
      (by rw [map_one]; exact one_mem _) z hzm γ hγ
    simpa using h
  · intro hψ
    haveI := hB.unram
    obtain ⟨m, s, c, hsc⟩ := exists_traceFamily (F := F) (E := E)
    obtain ⟨k, S, T, hS, hTm, -, hTS⟩ := exists_formFrame' σ X.J (det_ne_zero_of_herm σ B hX) X.L (by first | exact hX.lat | exact hX.lat.toIsLattice)
      (fun y hy => (hX.dual y).2 fun x hx => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]; exact RingOfIntegers.isIntegral_coe r)
    obtain ⟨k', S', T', hS', hTm', hTd', hTS'⟩ := exists_formFrame' σ W.J (det_ne_zero_of_skew σ B hW) W.L (by first | exact hW.lat | exact hW.lat.toIsLattice)
      (fun y hy => (hW.dual y).2 fun x hx o => by
        obtain ⟨r, hr⟩ := hy x hx
        rw [← hr]
        exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (RingOfIntegers.isIntegral_coe r)))
    set C := incM F (X.J * S.map σ)ᵀ * z * (incM F (W.J * S'.map σ)ᵀ)ᵀ with hC
    have hCat : ∀ j l, At (evFin F v) (C j l) := fun j l u hu => by
      have hz' : u • z = 0 := hz u hu
      have h1 : u • C = incM F (X.J * S.map σ)ᵀ * (u • z) * (incM F (W.J * S'.map σ)ᵀ)ᵀ := by
        rw [hC, Matrix.mul_smul, Matrix.smul_mul]
      rw [hz', Matrix.mul_zero, Matrix.zero_mul] at h1
      have := congrFun (congrFun h1 j) l
      simpa using this
    have hint : ∀ (e : E), IsIntegral ℤ e → ∀ j l, ∀ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l)) * y) = 1 := by
      intro e hei j l
      set M := incM F (Matrix.vecMulVec (fun i => e * S i j) (fun i => S' i l)) with hM
      set t := symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z M with ht
      have hx : (fun i => e * S i j) ∈ X.L := by
        have := X.L.smul_mem (⟨e, hei⟩ : 𝓞 E) (hS j)
        convert this using 1
        ext i; first | rfl | simp [Algebra.smul_def]
      have htat : At (evFin F v) t := fun u hu => by
        have := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) u 1 z M
        rw [hz u hu, one_smul, mul_one, GlobalTheory.LatVacArith.symp_zero_left] at this
        exact this.symm
      have htC : t = -Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (σ e) * C j l) := by
        rw [ht, symp, hM, hTens_frame, neg_one_mul, map_neg]
      have key : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v t * y) = 1 := by
        intro y hy
        have hmem : GlobalTheory.LatVac.liftV v y • M ∈ latAtV X W v :=
          AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v y, by rw [GlobalTheory.LatVac.evFin_liftV]; exact hy,
            _, hx, _, hS' l, rfl⟩
        have h1 := hψ _ hmem
        have h2 := GlobalTheory.LatVac.symp_smul_smul σ (incM F X.J) (incM F W.J) (-1) 1 (GlobalTheory.LatVac.liftV v y) z M
        rw [one_smul, one_mul] at h2
        rw [h2] at h1
        have hat2 : At (evFin F v) (GlobalTheory.LatVac.liftV v y * t) := fun u hu => by
          have := htat u hu
          rw [smul_eq_mul] at this ⊢
          rw [mul_left_comm, this, mul_zero]
        rw [GlobalTheory.VacIndic.psi_of_at _ hat2, map_mul, GlobalTheory.LatVac.evFin_liftV, mul_comm] at h1
        exact h1
      intro y hy
      have := key (-y) (neg_mem hy)
      rwa [htC, map_neg, neg_mul_neg] at this
    have hσ : Function.Bijective σ := AlgHom.bijective σ
    have hint' : ∀ i j l, ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v (evFin F v (Algebra.trace (AF F) (AE F E)
        (inclR (F := F) (AF F) (c i : E) * C j l)) * y) = 1 := by
      intro i j l
      obtain ⟨e, he⟩ := hσ.2 (c i : E)
      have hei : IsIntegral ℤ e := by
        rw [← isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) hσ.1]
        show IsIntegral ℤ (σ e)
        rw [he]; exact RingOfIntegers.isIntegral_coe _
      have := hint e hei j l
      rwa [he] at this
    rw [decomp T (X.J * S.map σ)ᵀ T' (W.J * S'.map σ)ᵀ hTS hTS' z, ← hC]
    refine AddSubgroup.sum_mem _ fun j _ => AddSubgroup.sum_mem _ fun l _ => ?_
    rw [trace_expand s c hsc (C j l), Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have hxi : (fun r => (s i : E) * T r j) ∈ X.L := by
      have := X.L.smul_mem (s i) (hTm j)
      convert this using 1
      ext r; simp [Algebra.smul_def]
    have hat : At (evFin F v) (Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (c i : E) * C j l)) := by
      intro u hu
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul, ← mul_smul_comm]
      have := hCat j l u hu
      rw [this, mul_zero, map_zero]
    have hmem := smul_mem_latAtV σ B hB.std hX hW v hat (hint' i j l) hxi (hTm' l) (hTd' l)
    convert hmem using 1
    rw [smul_assoc]
    congr 1
    ext p q
    simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, map_mul, smul_eq_mul]
    ring
end GlobalTheory.LatSelfDualAll
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels UpperTheory.TP.BA
namespace UpperTheory.SeparatedDualCondition
variable {F : Type} [Field F] [NumberField F]
private theorem exists_cond_pk (v : HeightOneSpectrum (𝓞 F)) (ψ₀ : AddChar (Fv F v) ℂ) (x₀ a : Fv F v) (hx₀ : ψ₀ x₀ ≠ 1)
    (ha0 : a ≠ 0) (ha : ∀ x ∈ v.adicCompletionIntegers F, ψ₀ (a * x) = 1) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ x, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) ↔
      c⁻¹ * x ∈ v.adicCompletionIntegers F := by
  classical
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ₀)
  let I : Ideal (v.adicCompletionIntegers F) :=
    { carrier := {o | ∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x₀ * o * y) = 1}
      add_mem' := by
        intro p q hp hq y hy
        have e : x₀ * ((p + q : v.adicCompletionIntegers F) : Fv F v) * y = x₀ * p * y + x₀ * q * y := by
          push_cast; ring
        rw [e, AddChar.map_add_eq_mul, hp y hy, hq y hy, one_mul]
      zero_mem' := by
        intro y _
        simp
      smul_mem' := by
        intro r p hp y hy
        have e : x₀ * ((r • p : v.adicCompletionIntegers F) : Fv F v) * y = x₀ * p * (r * y) := by
          simp only [smul_eq_mul]; push_cast; ring
        rw [e]
        exact hp _ (mul_mem r.2 hy) }
  have hI : ∀ o : v.adicCompletionIntegers F, o ∈ I ↔ ∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x₀ * o * y) = 1 :=
    fun _ => Iff.rfl
  have key : ∀ x, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x₀⁻¹ * x ∈ v.adicCompletionIntegers F := by
    intro x hx
    by_cases hx' : x = 0
    · subst hx'
      simp
    · refine ((v.adicCompletionIntegers F).mem_or_inv_mem (x₀⁻¹ * x)).resolve_right fun h => hx₀ ?_
      have := hx _ h
      have e : x * (x₀⁻¹ * x)⁻¹ = x₀ := by field_simp
      rwa [e] at this
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hbI : b ∈ I := by rw [hb]; exact Submodule.mem_span_singleton_self b
  have hmem : ∀ o, o ∈ I ↔ ∃ t : v.adicCompletionIntegers F, o = t * b := by
    intro o
    rw [hb, Submodule.mem_span_singleton]
    simp [eq_comm]
  have hb0 : (b : Fv F v) ≠ 0 := by
    intro h0
    have h0' : b = 0 := by exact_mod_cast h0
    have hk := key a ha
    have hin : (⟨_, hk⟩ : v.adicCompletionIntegers F) ∈ I := by
      rw [hI]
      intro y hy
      have := ha y hy
      simpa [hx0, mul_assoc, mul_inv_cancel_left₀] using this
    obtain ⟨t, ht⟩ := (hmem _).1 hin
    rw [h0', mul_zero] at ht
    have := congrArg Subtype.val ht
    simp [hx0, ha0] at this
  refine ⟨x₀ * b, mul_ne_zero hx0 hb0, fun x => ⟨fun hx => ?_, fun hx y hy => ?_⟩⟩
  · have hk := key x hx
    have hin : (⟨_, hk⟩ : v.adicCompletionIntegers F) ∈ I := by
      rw [hI]
      intro y hy
      have := hx y hy
      simpa [hx0, mul_assoc, mul_inv_cancel_left₀] using this
    obtain ⟨t, ht⟩ := (hmem _).1 hin
    have h2 : x₀⁻¹ * x = t * b := by simpa using congrArg Subtype.val ht
    have : (x₀ * b)⁻¹ * x = t := by
      rw [mul_inv, mul_comm x₀⁻¹, mul_assoc, h2]
      field_simp
    rw [this]
    exact t.2
  · have hh := (hI b).1 hbI (((x₀ * b)⁻¹ * x) * y) (mul_mem hx hy)
    have e : x₀ * b * ((x₀ * b)⁻¹ * x * y) = x * y := by
      field_simp
    rwa [e] at hh
private theorem sep_dual_pk (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ] (ψ₀ : AddChar (Fv F v) ℂ)
    (Λ L : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (hle : Λ ≤ L)
    (hdual : ∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1)
    (hst : ∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ L, a • l ∈ L)
    (c₀ : Fv F v) (hc₀ : c₀ ≠ 0)
    (hbd : ∀ l ∈ L, ∀ i, c₀ * l.1 i ∈ v.adicCompletionIntegers F ∧ c₀ * l.2 i ∈ v.adicCompletionIntegers F)
    (a : Fv F v) (ha0 : a ≠ 0) (ha : ∀ x ∈ v.adicCompletionIntegers F, ψ₀ (a * x) = 1)
    (y : (κ → Fv F v) × (κ → Fv F v)) (hy : y ∉ L) :
    ∃ u : (κ → Fv F v) × (κ → Fv F v), (∀ l ∈ L, ψ₀ (u.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ u.2) = 1) ∧
      ψ₀ (u.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ u.2) ≠ 1 := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ₀ x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hy (hle ((hdual y).2 fun l _ => h _))
  obtain ⟨c, hc0, hc⟩ := exists_cond_pk v ψ₀ x₀ a hx₀ ha0 ha
  let O := v.adicCompletionIntegers F
  let L' : Submodule O ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := L
      add_mem' := fun h h' => L.add_mem h h'
      zero_mem' := L.zero_mem
      smul_mem' := fun t l hl => hst (t : Fv F v) t.2 l hl }
  let φ : ((κ → O) × (κ → O)) →ₗ[O] ((κ → Fv F v) × (κ → Fv F v)) :=
    { toFun := fun x => (fun i => c₀⁻¹ * (x.1 i : Fv F v), fun i => c₀⁻¹ * (x.2 i : Fv F v))
      map_add' := by intro x y; ext i <;> simp [mul_add]
      map_smul' := by intro t x; ext i <;> simp [Algebra.smul_def] <;> ring }
  have hle' : L' ≤ LinearMap.range φ := by
    intro l hl
    refine ⟨(fun i => ⟨c₀ * l.1 i, (hbd l hl i).1⟩, fun i => ⟨c₀ * l.2 i, (hbd l hl i).2⟩), ?_⟩
    ext i <;> simp [φ, hc₀]
  haveI : IsNoetherian O (LinearMap.range φ) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian O L' := isNoetherian_of_le hle'
  have hfg : L'.FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span (Fv F v) (L' : Set ((κ → Fv F v) × (κ → Fv F v))) = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨t, ht0, ht⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v
      (fun s : κ ⊕ κ => Sum.elim (fun k => (c * c₀)⁻¹ * w.1 k) (fun k => (c * c₀)⁻¹ * w.2 k) s)
    have hw : t • w ∈ L := hle ((hdual _).2 fun l hl => by
      have hm : c⁻¹ * ((t • w).1 ⬝ᵥ l.2 - l.1 ⬝ᵥ (t • w).2) ∈ v.adicCompletionIntegers F := by
        rw [mul_sub]
        simp only [dotProduct, Finset.mul_sum]
        refine sub_mem (sum_mem fun k _ => ?_) (sum_mem fun k _ => ?_)
        · have := mul_mem (ht (Sum.inl k)) (hbd l (hle hl) k).2
          convert this using 1
          simp only [Sum.elim_inl, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          field_simp
        · have := mul_mem (ht (Sum.inr k)) (hbd l (hle hl) k).1
          convert this using 1
          simp only [Sum.elim_inr, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          field_simp
      have h1 := (hc _).2 hm 1 (one_mem _)
      rwa [mul_one] at h1)
    have e : w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hw)
  haveI : L'.IsLattice (Fv F v) := Submodule.IsLattice.of_fg (Fv F v) hfg
  haveI : L'.IsFullLattice (Fv F v) := ⟨hspan⟩
  let ψ' : AddChar (Fv F v) ℂ := ψ₀.compAddMonoidHom (AddMonoidHom.mulLeft c)
  have hψ' : ∀ x, ψ' x = ψ₀ (c * x) := fun _ => rfl
  have hsep : ∀ x, (∀ y : O, ψ' (x * algebraMap O (Fv F v) y) = 1) ↔ x ∈ (algebraMap O (Fv F v)).range := by
    intro x
    have e : c⁻¹ * (c * x) = x := by field_simp
    have h := hc (c * x)
    rw [e] at h
    constructor
    · intro hx
      have hm := h.1 fun y hy => by
        have := hx ⟨y, hy⟩
        rw [hψ', ← mul_assoc] at this
        exact this
      exact ⟨⟨x, hm⟩, rfl⟩
    · rintro ⟨o, rfl⟩ y
      have := h.2 o.2 y y.2
      rw [hψ', ← mul_assoc]
      exact this
  obtain ⟨l, h1, h2⟩ := GlobalTheory.ThK.Dbl.Bmp.sep ψ' hsep L' hy
  let e : κ → κ → Fv F v := fun k j => if k = j then 1 else 0
  let A : (κ → Fv F v) →ₗ[Fv F v] Fv F v := l ∘ₗ LinearMap.inl _ _ _
  let Bm : (κ → Fv F v) →ₗ[Fv F v] Fv F v := l ∘ₗ LinearMap.inr _ _ _
  have hl : ∀ z, l z = ∑ k, z.1 k * A (e k) + ∑ k, z.2 k * Bm (e k) := by
    intro z
    have hz : z = (z.1, 0) + (0, z.2) := by simp
    have h1 := LinearMap.pi_apply_eq_sum_univ A z.1
    have h2 := LinearMap.pi_apply_eq_sum_univ Bm z.2
    simp only [smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
    conv_lhs => rw [hz, map_add (f := _)]
    rfl
  have hu : ∀ z, ψ₀ ((fun k => c * Bm (e k)) ⬝ᵥ z.2 - z.1 ⬝ᵥ (fun k => -(c * A (e k)))) = ψ' (l z) := by
    intro z
    rw [hψ', hl, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    simp only [dotProduct]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib, add_comm]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  exact ⟨(fun k => c * Bm (e k), fun k => -(c * A (e k))), fun z hz => (hu z).trans (h1 z hz), fun h => h2 ((hu y).symm.trans h)⟩
open GlobalTheory.Idele in
open GlobalTheory.StdDual (codiff codiff_ne_zero one_le_codiff) in
private theorem psi_triv_pk {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (v : Pl F) (x : Fv F v)
    (hx : x ∈ v.adicCompletionIntegers F) : GlobalTheory.LatVac.psiAt ψ v (1 * x) = 1 := by
  have h1 : (1 : Af F) ∈ adelicIdeal (codiff F) := by
    have h := (algebraMap_mem_adelicIdeal codiff_ne_zero (1 : F)).2
      ((one_le_codiff (F := F)) (FractionalIdeal.one_mem_one _))
    simpa using h
  have h2 := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) 1).1 h1 (singleFin v x) (by
    intro w
    by_cases h : w = v
    · subst h
      have e : (singleFin w x) w = x := evalV_singleFin_self w x
      rw [e]
      exact hx
    · have e : (singleFin v x) w = 0 := evalV_singleFin_ne h x
      rw [e]
      exact zero_mem _)
  rw [mul_one] at h2
  rw [one_mul]
  exact h2
private theorem locCo_smul'_pk {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) (a : AF F) (w : W) :
    GlobalTheory.LatVac.locCo co v (a • w) = evFin F v a • GlobalTheory.LatVac.locCo co v w := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
  ext k <;> simp [smul_eq_mul, map_mul]
private theorem exists_at_pk {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) (w : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ z : W, At (evFin F v) z ∧ GlobalTheory.LatVac.locCo co v z = w := by
  obtain ⟨p, hp⟩ : ∃ p : (κ → AF F) × (κ → AF F),
      p = (fun k => GlobalTheory.LatVac.liftV v (w.1 k), fun k => GlobalTheory.LatVac.liftV v (w.2 k)) := ⟨_, rfl⟩
  refine ⟨co.e.symm p, fun u hu => ?_, ?_⟩
  · have hp0 : u • p = 0 := by
      subst hp
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (w.1 k) u hu
      · exact GlobalTheory.LatVac.at_liftV v (w.2 k) u hu
    rw [← map_smul, hp0, map_zero]
  · subst hp
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((co.e (co.e.symm _)).1 k) = w.1 k
      rw [LinearEquiv.apply_symm_apply]
      exact GlobalTheory.LatVac.evFin_liftV v (w.1 k)
    · show evFin F v ((co.e (co.e.symm _)).2 k) = w.2 k
      rw [LinearEquiv.apply_symm_apply]
      exact GlobalTheory.LatVac.evFin_liftV v (w.2 k)
private theorem at_inj_pk {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) {z : W} (hz : At (evFin F v) z)
    (h0 : GlobalTheory.LatVac.locCo co v z = 0) : z = 0 := by
  have hz1 : GlobalTheory.LatVac.liftV v 1 • z = z := by
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have he : co.e z = 0 := by
    rw [← hz1, map_smul]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · have h : evFin F v ((co.e z).1 k) = 0 := congrFun (congrArg Prod.fst h0) k
      have := GlobalTheory.LatVac.at_liftV v 1 _ h
      simpa [smul_eq_mul, mul_comm] using this
    · have h : evFin F v ((co.e z).2 k) = 0 := congrFun (congrArg Prod.snd h0) k
      have := GlobalTheory.LatVac.at_liftV v 1 _ h
      simpa [smul_eq_mul, mul_comm] using this
  exact (map_eq_zero_iff co.e co.e.injective).1 he
private theorem common_bound_pk (v : Pl F) {c₁ c₂ : Fv F v} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    ∃ c : Fv F v, c ≠ 0 ∧ (∀ x, c₁ * x ∈ v.adicCompletionIntegers F → c * x ∈ v.adicCompletionIntegers F) ∧
      ∀ x, c₂ * x ∈ v.adicCompletionIntegers F → c * x ∈ v.adicCompletionIntegers F := by
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (c₁⁻¹ * c₂) with h | h
  · refine ⟨c₂, h₂, fun x hx => ?_, fun x hx => hx⟩
    have := mul_mem h hx
    rwa [show c₁⁻¹ * c₂ * (c₁ * x) = c₂ * x by field_simp] at this
  · refine ⟨c₁, h₁, fun x hx => hx, fun x hx => ?_⟩
    have := mul_mem h hx
    rwa [show (c₁⁻¹ * c₂)⁻¹ * (c₂ * x) = c₁ * x by field_simp] at this
end UpperTheory.SeparatedDualCondition
open UpperTheory.SeparatedDualCondition in
theorem UpperTheory.exists_separating_of_not_mem_lattice_coset :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ y : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) y → (∀ a ∈ latAtV X W v, ∀ b ∈ latAtV X W v, y ≠ a + mat g⁻¹ * b) → ∃ u ∈ latAtV X W v, mat g * u ∈ latAtV X W v ∧ B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y) ≠ 1 := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB hX hW v g _ y hy hne
  classical
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hO := (GlobalTheory.LatVac.latAtV_at_stable X W v).2
  have hself := _root_.GlobalTheory.LatSelfDualAll.latAtV_selfDual_k F E σ B n d X W r s r' s' hB hX hW v
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ (latAtV X W v) hat hself
  let S : AddSubgroup (Matrix (Fin n) (Fin d) (AE F E)) :=
    { carrier := {z | ∃ a ∈ latAtV X W v, ∃ b ∈ latAtV X W v, z = a + mat g⁻¹ * b}
      add_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by rw [Matrix.mul_add]; abel⟩
      zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
      neg_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨-a, neg_mem ha, -b, neg_mem hb, by rw [Matrix.mul_neg]; abel⟩ }
  have hmulat : ∀ (A : Matrix (Fin n) (Fin n) (AE F E)) (z : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) z →
      At (evFin F v) (A * z) := fun A z hz u hu => by
    rw [← Matrix.mul_smul, hz u hu, Matrix.mul_zero]
  have hSat : ∀ z ∈ S, At (evFin F v) z := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ u hu
    rw [smul_add, hat a ha u hu, hmulat _ b (hat b hb) u hu, add_zero]
  obtain ⟨c₁, hc₁0, hc₁⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat.toIsLattice hW.lat.toIsLattice
  obtain ⟨Mt, _, gm, hgm⟩ := GlobalTheory.LatParam.latAtV_param X W hX.lat.toIsLattice hW.lat.toIsLattice v
  obtain ⟨c₂, hc₂0, hc₂⟩ := GlobalTheory.LatBound.exists_mul_mem_integers v
    (fun t : Bool × Mt × (Fin n × Fin d) =>
      if t.1 then (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * incM F (gm t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * incM F (gm t.2.1))).2 t.2.2)
  have hb2 : ∀ b ∈ latAtV X W v, ∀ i, c₂ * (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * b)).1 i ∈ v.adicCompletionIntegers F ∧
      c₂ * (GlobalTheory.LatVac.locCo M.co v (mat g⁻¹ * b)).2 i ∈ v.adicCompletionIntegers F := by
    intro b hb i
    obtain ⟨a, rfl⟩ := (hgm b).1 hb
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_sum, Matrix.mul_smul, map_sum, locCo_smul'_pk, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Prod.snd_sum,
      Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    constructor
    · refine sum_mem fun m _ => ?_
      rw [mul_left_comm]
      exact mul_mem (a m).2 (by simpa using hc₂ (true, m, i))
    · refine sum_mem fun m _ => ?_
      rw [mul_left_comm]
      exact mul_mem (a m).2 (by simpa using hc₂ (false, m, i))
  obtain ⟨c₀, hc₀, hb₁, hb₂⟩ := common_bound_pk v hc₁0 hc₂0
  have hbd : ∀ l ∈ S.map (GlobalTheory.LatVac.locCo M.co v), ∀ i, c₀ * l.1 i ∈ v.adicCompletionIntegers F ∧
      c₀ * l.2 i ∈ v.adicCompletionIntegers F := by
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩ i
    rw [map_add (f := _)]
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add]
    exact ⟨add_mem (hb₁ _ (hc₁ a ha i).1) (hb₂ _ (hb2 b hb i).1), add_mem (hb₁ _ (hc₁ a ha i).2) (hb₂ _ (hb2 b hb i).2)⟩
  have hst : ∀ t ∈ v.adicCompletionIntegers F, ∀ l ∈ S.map (GlobalTheory.LatVac.locCo M.co v),
      t • l ∈ S.map (GlobalTheory.LatVac.locCo M.co v) := by
    rintro t ht _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨GlobalTheory.LatVac.liftV v t • (a + mat g⁻¹ * b), ⟨GlobalTheory.LatVac.liftV v t • a, hO t ht a ha,
      GlobalTheory.LatVac.liftV v t • b, hO t ht b hb, by rw [smul_add, Matrix.mul_smul]⟩, ?_⟩
    rw [locCo_smul'_pk, GlobalTheory.LatVac.evFin_liftV]
  have hle : (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v) ≤ S.map (GlobalTheory.LatVac.locCo M.co v) := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨γ, ⟨γ, hγ, 0, zero_mem _, by simp⟩, rfl⟩
  have hyL : GlobalTheory.LatVac.locCo M.co v y ∉ S.map (GlobalTheory.LatVac.locCo M.co v) := by
    rintro ⟨z, hzS, hz⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := id hzS
    refine hne a ha b hb (sub_eq_zero.1 (at_inj_pk M.co v (fun u hu => ?_) ?_)).symm
    · rw [smul_sub, hy u hu, hSat _ hzS u hu, sub_zero]
    · rw [map_sub, hz, sub_self]
  obtain ⟨w, hw1, hw2⟩ := sep_dual_pk v (GlobalTheory.LatVac.psiAt B.ψ v) _ _ hle hsd hst c₀ hc₀ hbd 1 one_ne_zero
    (psi_triv_pk hB.std v) _ hyL
  obtain ⟨z, hzat, rfl⟩ := exists_at_pk M.co v w
  have hform := fun γ => GlobalTheory.LatVac.DualLoc.psi_form M.co v B.ψ hzat γ
  have hgg : mat g * mat g⁻¹ = 1 := by
    show mat (g * g⁻¹) = 1
    rw [mul_inv_cancel]
    rfl
  refine ⟨z, (hself z hzat).2 fun γ hγ => ?_, (hself _ (hmulat _ z hzat)).2 fun γ hγ => ?_, ?_⟩
  · rw [hform]
    exact hw1 _ (hle ⟨γ, hγ, rfl⟩)
  · have e := GlobalTheory.SympInv.symp_act F E σ n d X W g 1 z (mat g⁻¹ * γ)
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_one, ← Matrix.mul_assoc, hgg, Matrix.one_mul] at e
    rw [e, hform]
    exact hw1 _ ⟨mat g⁻¹ * γ, ⟨0, zero_mem _, γ, hγ, by simp⟩, rfl⟩
  · rw [hform]
    exact hw2
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace UpperTheory.TP.BA
section Schr
variable {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ]
private theorem schr_comp_pk (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' f) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') f := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h
private theorem schr_comm_pk (ψ : AddChar R ℂ) (w w' : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' f) = ψ (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) • schr ψ w' (schr ψ w f) := by
  rw [schr_comp_pk, schr_comp_pk, add_comm w' w, smul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) * h
private theorem schr_add_of_pk (ψ : AddChar R ℂ) {w w' : (κ → R) × (κ → R)} (h : w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0)
    (f : (κ → R) → ℂ) : schr ψ (w + w') f = schr ψ w (schr ψ w' f) := by
  rw [schr_comp_pk, h, mul_zero, AddChar.map_zero_eq_one, one_smul]
private theorem schr_zero_pk (ψ : AddChar R ℂ) (f : (κ → R) → ℂ) : schr ψ 0 f = f := by
  funext x
  simp [schr]
private theorem schr_neg_pk (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) (f : (κ → R) → ℂ) :
    schr ψ (-w) (schr ψ w f) = f := by
  rw [← schr_add_of_pk ψ (by simp [dotProduct_comm]), neg_add_cancel, schr_zero_pk]
end Schr
section Alg
private theorem cong_key_pk {A : Type} [Ring A] {e s m m' α β q q' : A} (hs : ∀ a : A, s * a = a * s)
    (h : m * (e - s * β) = e + s * α) (hmm : m' * m = 1) (hq : (e - s * β) * q = e) (hq' : (e + s * α) * q' = e)
    (eq : e * q = q) (eq' : e * q' = q') (eα : α * e = α) (eβ : β * e = β) (e1 : e * α = α) (e2 : e * β = β)
    (e3 : e * e = e) (hm : (m - 1) * e = m - 1) (hm' : (m' - 1) * e = m' - 1) :
    m - 1 = s * (α + β * q + s * (α * (β * q))) ∧ m' - 1 = s * (-β - α * q' + s * (β * (α * q'))) := by
  have a1 : q = e + s * (β * q) := by
    have : e * q - s * β * q = e := by rw [← sub_mul]; exact hq
    rw [eq] at this
    rw [← this, mul_assoc]
    abel
  have a2 : q' = e - s * (α * q') := by
    have : e * q' + s * α * q' = e := by rw [← add_mul]; exact hq'
    rw [eq'] at this
    rw [← this, mul_assoc]
    abel
  have b1 : m * e = (e + s * α) * q := by rw [← h, mul_assoc, hq]
  have b2 : m' * e = (e - s * β) * q' := by
    calc m' * e = m' * ((e + s * α) * q') := by rw [hq']
      _ = m' * (m * (e - s * β) * q') := by rw [h]
      _ = (m' * m) * (e - s * β) * q' := by simp only [mul_assoc]
      _ = _ := by rw [hmm, one_mul]
  have c : ∀ a b : A, a * (s * b) = s * (a * b) := fun a b => by rw [← mul_assoc, ← hs a, mul_assoc]
  have a3 : α * q = α + s * (α * (β * q)) := by
    conv_lhs => rw [a1]
    rw [mul_add, eα, c]
  have a4 : β * q' = β - s * (β * (α * q')) := by
    conv_lhs => rw [a2]
    rw [mul_sub, eβ, c]
  constructor
  · rw [← hm, sub_mul, one_mul, b1]
    calc (e + s * α) * q - e = q + s * (α * q) - e := by rw [add_mul, eq, mul_assoc]
      _ = (e + s * (β * q)) + s * (α + s * (α * (β * q))) - e := by rw [a3, ← a1]
      _ = _ := by rw [mul_add, mul_add, mul_add]; abel
  · rw [← hm', sub_mul, one_mul, b2]
    calc (e - s * β) * q' - e = q' - s * (β * q') - e := by rw [sub_mul, eq', mul_assoc]
      _ = (e - s * (α * q')) - s * (β - s * (β * (α * q'))) - e := by rw [a4, ← a2]
      _ = _ := by simp only [mul_add, mul_sub, mul_neg]; abel
end Alg
section Geo
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
private theorem sg_mul_pk (v : Pl F) (a b : Fv F v) : sg v a * sg v b = sg v (a * b) := by
  rw [PositivityTheory.ThKH.Iwas.mul_sg, PositivityTheory.ThKH.Iwas.ev_sg]
private theorem sg_one_smul_pk {v : Pl F} {A : Type} [AddCommGroup A] [Module (AF F) A] {z : A} (h : At (evFin F v) z) :
    sg v 1 • z = z := PositivityTheory.KCo.at_iff.1 h
private theorem at_sg_smul_pk {v : Pl F} {A : Type} [AddCommGroup A] [Module (AF F) A] (t : Fv F v) (z : A) :
    At (evFin F v) (sg v t • z) := fun u hu => by
  rw [smul_smul, PositivityTheory.ThKH.Iwas.mul_sg, hu, zero_mul, map_zero, zero_smul]
private theorem hTens_zero'_pk {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (c : K →ₐ[R] K) (JA : Matrix (Fin n) (Fin n) K)
    (JB : Matrix (Fin d) (Fin d) K) (p q : Matrix (Fin n) (Fin n) K) (x : Matrix (Fin n) (Fin d) K)
    (h : x * JB * (x.map c)ᵀ = 0) : hTens c JA JB (p * x) (q * x) = 0 := by
  have m : ∀ {a b e : ℕ} (A : Matrix (Fin a) (Fin b) K) (B : Matrix (Fin b) (Fin e) K), (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := c.toRingHom)
  have h' : x.map c * JBᵀ * xᵀ = 0 := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  rw [PositivityTheory.KCo.hTens_eq, m, Matrix.transpose_mul]
  calc (xᵀ * pᵀ * JA * (q.map c * x.map c) * JBᵀ).trace = (xᵀ * (pᵀ * JA * q.map c * (x.map c * JBᵀ))).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((pᵀ * JA * q.map c * (x.map c * JBᵀ)) * xᵀ).trace := Matrix.trace_mul_comm _ _
    _ = 0 := by rw [Matrix.mul_assoc, h', Matrix.mul_zero, Matrix.trace_zero]
private theorem symp_zero'_pk {R K : Type} [CommRing R] [CommRing K] [Algebra R K] (c : K →ₐ[R] K) (ξ : K) (JA : Matrix (Fin n) (Fin n) K)
    (JB : Matrix (Fin d) (Fin d) K) (p q : Matrix (Fin n) (Fin n) K) (x : Matrix (Fin n) (Fin d) K)
    (h : x * JB * (x.map c)ᵀ = 0) : symp (R := R) c ξ JA JB (p * x) (q * x) = 0 := by
  rw [symp, hTens_zero'_pk c JA JB p q x h, mul_zero, map_zero]
variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d}
private theorem at_mat_inv_pk {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) : g⁻¹ ∈ UAt σ X (evFin F v) := by
  have e : mat g⁻¹ - 1 = -mat g⁻¹ * (mat g - 1) := by
    rw [mul_sub, neg_mul, show mat g⁻¹ * mat g = 1 from g.1.inv_mul]
    simp [neg_add_eq_sub]
  show At (evFin F v) (mat g⁻¹ - 1)
  rw [e]
  exact PositivityTheory.ThKH.Iwas.at_mul_right _ hg
private theorem mem_UAt_of_locGrp_pk {v : Pl F} {g : UA σ X.J} (hg : g ∈ GlobalTheory.ThK.Dbl.locGrp σ X v) : g ∈ UAt σ X (evFin F v) := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact PositivityTheory.ThKH.Locrep.one_mem_UAt X v
  | mul x y _ _ hx hy => exact PositivityTheory.ThKH.Locrep.mul_mem_UAt hx hy
  | inv x _ hx => exact at_mat_inv_pk hx
private def cong_pk (v : Pl F) (Λ : AddSubgroup (Matrix (Fin n) (Fin n) (AE F E))) (s : AF F)
    (h1 : ∀ a ∈ Λ, ∀ b ∈ Λ, a * b ∈ Λ) (h2 : ∀ a ∈ Λ, s • a ∈ Λ) : Subgroup (UA σ X.J) where
  carrier := {g | g ∈ UAt σ X (evFin F v) ∧ (∃ a ∈ Λ, mat g - 1 = s • a) ∧ ∃ a ∈ Λ, mat g⁻¹ - 1 = s • a}
  one_mem' := ⟨PositivityTheory.ThKH.Locrep.one_mem_UAt X v, ⟨0, zero_mem _, by simp [mat]⟩, ⟨0, zero_mem _, by simp [mat]⟩⟩
  mul_mem' := fun {g h} ⟨a1, ⟨a, ha, ea⟩, ⟨a', ha', ea'⟩⟩ ⟨b1, ⟨b, hb, eb⟩, ⟨b', hb', eb'⟩⟩ => by
    have key : ∀ (p q a b : Matrix (Fin n) (Fin n) (AE F E)), p - 1 = s • a → q - 1 = s • b →
        p * q - 1 = s • (a + b + s • (a * b)) := fun p q a b e1 e2 => by
      have p1 : p = 1 + s • a := by rw [← e1]; abel
      have q1 : q = 1 + s • b := by rw [← e2]; abel
      rw [p1, q1]
      simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_add]
      abel
    refine ⟨PositivityTheory.ThKH.Locrep.mul_mem_UAt a1 b1, ⟨_, add_mem (add_mem ha hb) (h2 _ (h1 _ ha _ hb)), key _ _ _ _ ea eb⟩,
      ⟨_, add_mem (add_mem hb' ha') (h2 _ (h1 _ hb' _ ha')), ?_⟩⟩
    rw [mul_inv_rev]
    exact key _ _ _ _ eb' ea'
  inv_mem' := fun {g} ⟨a1, p, q⟩ => ⟨at_mat_inv_pk a1, q, by rw [inv_inv]; exact p⟩
end Geo
section Main
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
  {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d}
private abbrev Sc_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : (Fin n × Fin d → Fv F v) → ℂ) : (Fin n × Fin d → Fv F v) → ℂ :=
  schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v u) f
private abbrev Bf_pk (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (u y : Matrix (Fin n) (Fin d) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y
private theorem sc_comm_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) {u : Matrix (Fin n) (Fin d) (AE F E)}
    (hu : At (evFin F v) u) (y) (f) : Sc_pk M ψ v u (Sc_pk M ψ v y f) = ψ (Bf_pk σ X W u y) • Sc_pk M ψ v y (Sc_pk M ψ v u f) := by
  rw [Sc_pk, Sc_pk, schr_comm_pk]
  congr 1
  exact (GlobalTheory.LatVac.DualLoc.psi_form M.co v ψ hu y).symm
private theorem sc_add_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) {u y : Matrix (Fin n) (Fin d) (AE F E)}
    (h : Bf_pk σ X W u y = 0) (f) : Sc_pk M ψ v (u + y) f = Sc_pk M ψ v u (Sc_pk M ψ v y f) := by
  have := GlobalTheory.LatVac.DualLoc.evFin_form M.co v u y
  rw [show symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u y = 0 from h, map_zero] at this
  rw [Sc_pk, map_add (f := _)]
  exact schr_add_of_pk _ this.symm f
private theorem sc_neg_pk (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) (u) (f) : Sc_pk M ψ v (-u) (Sc_pk M ψ v u f) = f := by
  rw [Sc_pk, Sc_pk, map_neg]
  exact schr_neg_pk _ _ f
private theorem schr_smul_pk {R : Type} [CommRing R] [Invertible (2 : R)] {κ : Type} [Fintype κ] (ψ : AddChar R ℂ)
    (w : (κ → R) × (κ → R)) (c : ℂ) (f : (κ → R) → ℂ) : schr ψ w (c • f) = c • schr ψ w f := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  ring
private theorem bf_sub_pk (M : Model σ X W) (u y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    Bf_pk σ X W u (y - y') = Bf_pk σ X W u y - Bf_pk σ X W u y' := by
  simp only [Bf_pk, M.co.form, map_sub, Prod.fst_sub, Prod.snd_sub, dotProduct_sub, sub_dotProduct]
  ring
private theorem symp_g_pk (ξ : AE F E) (g : UA σ X.J) (u y : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (mat g * u) (mat g * y) =
      symp (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) u y := by
  have := PositivityTheory.KCo.symp_act (R := AF F) (cA σ) ξ (incM F X.J) (incM F W.J) (g, (1 : UA σ W.J)) u y
  simpa [actAB, mat] using this
end Main
section Thm
open UpperTheory.TP
theorem _root_.UpperTheory.TP.bumpAny_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.BumpAny_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd v N hN
  classical
  obtain ⟨ω, ρ, L⟩ := _root_.PositivityTheory.ThKH.Locrep.locRepEx_k F E σ n d B X W M om
    ⟨hP.base, ⟨n, 0, hP.herm⟩, ⟨d, 0, hP.skew⟩, hP.good, χX, χW, hP.weil⟩ v
  obtain ⟨Λ, x₁, r, ϖ, D⟩ := _root_.UpperTheory.exists_weilLatticeDatum F E σ B n d X W n 0 d 0 hP.base hP.herm hP.skew hd v
  obtain ⟨hvS, hv0, θ, hθ, hvac⟩ := hP.good.vac v
  have hat : ∀ γ ∈ latAtV X W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have hone : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := PositivityTheory.ThKH.Locrep.one_mem_UAt W v
  obtain ⟨U, hU, hUf⟩ := (T.acts F E σ B n d X W M χX χW om n 0 d 0 hP v).2.2 (M.vac v) hvS
  have hU1 : {g : UA σ X.J | (g, (1 : UA σ W.J)) ∈ U} ∈ 𝓝 (1 : UA σ X.J) := by
    have c : Continuous fun g : UA σ X.J => (g, (1 : UA σ W.J)) := continuous_id.prodMk continuous_const
    exact c.continuousAt.preimage_mem_nhds (show U ∈ 𝓝 ((1 : UA σ X.J), (1 : UA σ W.J)) from hU)
  have hI : {g : UA σ X.J | GlobalTheory.ThK.Dbl.IntAt v g} ∈ 𝓝 (1 : UA σ X.J) :=
    (GlobalTheory.ThK.Dbl.Euler.isOpen_int (σ := σ) hP.herm.lat v).mem_nhds (one_mem _)
  obtain ⟨k₀, hk₀⟩ := D.small _ (Filter.inter_mem hN (Filter.inter_mem hU1 hI))
  obtain ⟨k, hk⟩ : ∃ k, k = k₀ + 1 := ⟨_, rfl⟩
  have hϖO : ∀ m : ℕ, ϖ ^ m ∈ v.adicCompletionIntegers F := fun m => pow_mem D.ϖ_mem m
  obtain ⟨s, hs⟩ : ∃ s, s = sg v (ϖ ^ k) := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s', s' = sg v (ϖ ^ k)⁻¹ := ⟨_, rfl⟩
  have ss : s * s' = sg v 1 := by rw [hs, hs', sg_mul_pk, mul_inv_cancel₀ (pow_ne_zero _ D.ϖ_ne)]
  have hsΛ : ∀ a ∈ Λ, s • a ∈ Λ := fun a ha => hs ▸ D.smul_mem _ (hϖO k) a ha
  let H : Subgroup (UA σ X.J) := cong_pk v Λ s D.mul_mem hsΛ
  have memH : ∀ g, g ∈ H ↔ g ∈ UAt σ X (evFin F v) ∧ (∃ a ∈ Λ, mat g - 1 = s • a) ∧ ∃ a ∈ Λ, mat g⁻¹ - 1 = s • a :=
    fun g => Iff.rfl
  have hsm : ∀ g ∈ H, g ∈ N ∩ ({g : UA σ X.J | (g, (1 : UA σ W.J)) ∈ U} ∩ {g : UA σ X.J | GlobalTheory.ThK.Dbl.IntAt v g}) := fun g hg => by
    obtain ⟨h1, h2, h3⟩ := (memH g).1 hg
    exact hk₀ k (by omega) g h1 (hs ▸ h2) (hs ▸ h3)
  have hx₁ := hat _ D.x_mem
  obtain ⟨x0, hx0d⟩ : ∃ x0, x0 = s' • x₁ := ⟨_, rfl⟩
  have hx0 : At (evFin F v) x0 := hx0d ▸ hs' ▸ at_sg_smul_pk _ _
  have hsx0 : s • x0 = x₁ := by rw [hx0d, smul_smul, ss, sg_one_smul_pk hx₁]
  obtain ⟨φ, hφd⟩ : ∃ φ, φ = Sc_pk M B.ψ v x0 (M.vac v) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin d) (AE F E) → ℂ, Q = fun γ =>
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) := ⟨_, rfl⟩
  have hSρ : ∀ u, At (evFin F v) u → ∀ f ∈ SB (Fin n × Fin d → Fv F v), Sc_pk M B.ψ v u f = ρ u f := fun u hu f hf =>
    (L.actsH u hu f hf _).1 (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu f)
  have hφS : φ ∈ SB (Fin n × Fin d → Fv F v) := by
    rw [hφd, hSρ _ hx0 _ hvS]
    exact L.presH _ hx0 _ hvS
  have hφ0 : φ ≠ 0 := fun h0 => hv0 (by
    have := sc_neg_pk M B.ψ v x0 (M.vac v)
    rw [← hφd, h0] at this
    rw [← this]
    funext x
    simp [schr])
  have hSv : ∀ γ ∈ latAtV X W v, Sc_pk M B.ψ v γ (M.vac v) = Q γ • M.vac v := fun γ hγ =>
    GlobalTheory.TensUniq.eq_of_tens_eq v (M.vac v) _ _ hvS fun r' hr =>
      (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hat γ hγ) (M.vac v) r' hr).symm.trans (by rw [hQ]; exact hvac γ hγ r' hr)
  have E1 : ∀ γ ∈ latAtV X W v, Sc_pk M B.ψ v γ φ = (B.ψ (Bf_pk σ X W γ x0) * Q γ) • φ := fun γ hγ => by
    rw [hφd, sc_comm_pk M B.ψ v (hat γ hγ), hSv γ hγ, Sc_pk, schr_smul_pk, smul_smul]
  have hA : ∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) φ ((B.ψ (Bf_pk σ X W γ x0) * Q γ) • φ) := fun γ hγ => by
    rw [← E1 γ hγ]
    exact GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ (hat γ hγ) φ
  have hfix : ∀ g ∈ H, Acts (evFin F v) (om (g, 1)) φ φ := fun g hg => by
    obtain ⟨h1, ⟨a, ha, ea⟩, -⟩ := (memH g).1 hg
    have vf : Acts (evFin F v) (om (g, 1)) (M.vac v) (M.vac v) := hUf (g, 1) (hsm g hg).2.1 h1 hone
    have w1 : M.vac v = ω (g, 1) (M.vac v) := (L.acts g h1 1 hone _ hvS _).1 vf
    refine (L.acts g h1 1 hone φ hφS φ).2 ?_
    have hγ := D.act a ha x₁ D.x_mem
    have e1 : mat g * x0 * (mat (1 : UA σ W.J))ᵀ = x0 + a * x₁ := by
      rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.transpose_one, Matrix.mul_one,
        show mat g = 1 + (mat g - 1) by abel, Matrix.add_mul, Matrix.one_mul, ea]
      congr 1
      rw [hx0d, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ss, sg_one_smul_pk (hat _ hγ)]
    have hb0 : Bf_pk σ X W x0 (a * x₁) = 0 := by
      have := symp_zero'_pk (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (s' • 1) a x₁ D.gram
      rwa [Matrix.smul_mul, Matrix.one_mul, ← hx0d] at this
    have hq1 : Q (a * x₁) = 1 := by
      rw [hQ]
      show B.ψ _ = 1
      rw [symp_zero'_pk (R := AF F) (cA σ) _ (incM F X.J) (incM F W.J) a a x₁ D.gram, mul_zero, AddChar.map_zero_eq_one]
    have e2 := L.impl g h1 1 hone x0 hx0 (M.vac v) hvS
    rw [e1, ← w1, ← hSρ _ hx0 _ hvS, ← hφd, ← hSρ _ (PositivityTheory.ThKH.Iwas.at_add hx0 (hat _ hγ)) _ hvS, sc_add_pk M B.ψ v hb0,
      hSv _ hγ, hq1, one_smul, ← hφd] at e2
    exact e2.symm
  have hsep : ∀ g ∈ GlobalTheory.ThK.Dbl.locGrp σ X v, g ∉ H → ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
      Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ) := fun g hgl hgH => by
    have hg := mem_UAt_of_locGrp_pk hgl
    have hg' := at_mat_inv_pk hg
    have hgm : mat g * mat g⁻¹ = 1 := g.1.mul_inv
    obtain ⟨y, hyd⟩ : ∃ y, y = mat g⁻¹ * x0 - x0 := ⟨_, rfl⟩
    have hy : At (evFin F v) y := hyd ▸ PositivityTheory.ThKH.Iwas.at_sub (PositivityTheory.ThKH.Iwas.at_mul_right _ hx0) hx0
    by_cases hc : ∀ a ∈ latAtV X W v, ∀ b ∈ latAtV X W v, y ≠ a + mat g⁻¹ * b
    · obtain ⟨u, hu, hgu, hne⟩ := _root_.UpperTheory.exists_separating_of_not_mem_lattice_coset F E σ B n d X W M n 0 d 0 hP.base hP.herm hP.skew v g hg y hy hc
      have hq : Q (mat g * u) = Q u := by
        rw [hQ]
        show B.ψ _ = B.ψ _
        rw [symp_g_pk]
      have hb : Bf_pk σ X W (mat g * u) x0 = Bf_pk σ X W u (mat g⁻¹ * x0) := by
        have := symp_g_pk (W := W) (-1) g u (mat g⁻¹ * x0)
        rwa [← Matrix.mul_assoc, hgm, Matrix.one_mul] at this
      have hQ0 : Q u ≠ 0 := by
        rw [hQ]
        exact (B.ψ.val_isUnit _).ne_zero
      refine ⟨u, _, _, hat u hu, ?_, hA u hu, hA _ hgu⟩
      intro h
      apply hne
      have h3 : B.ψ (Bf_pk σ X W u x0) = B.ψ (Bf_pk σ X W (mat g * u) x0) := mul_right_cancel₀ hQ0 (by rw [h, hq])
      rw [hyd]
      show B.ψ (Bf_pk σ X W u _) = 1
      rw [bf_sub_pk M, AddChar.map_sub_eq_div, ← hb, ← h3, div_self (B.ψ.val_isUnit _).ne_zero]
    · exfalso
      apply hgH
      push Not at hc
      obtain ⟨a, ha, b, hb, e⟩ := hc
      have hα := D.r_mem a ha
      have hβ := D.r_mem b hb
      obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (Fin n) (AE F E), S = s • 1 := ⟨_, rfl⟩
      have hSx : ∀ {l : ℕ} (x : Matrix (Fin n) (Fin l) (AE F E)), S * x = s • x := fun x => by
        rw [hS, Matrix.smul_mul, Matrix.one_mul]
      have hcomm : ∀ x : Matrix (Fin n) (Fin n) (AE F E), S * x = x * S := fun x => by
        rw [hSx, hS, Matrix.mul_smul, Matrix.mul_one]
      have e0 : mat g⁻¹ * (x₁ - s • b) = x₁ + s • a := by
        have e' : mat g⁻¹ * x0 = x0 + a + mat g⁻¹ * b := by
          rw [add_assoc, ← e, hyd]
          abel
        calc mat g⁻¹ * (x₁ - s • b) = s • (mat g⁻¹ * x0 - mat g⁻¹ * b) := by
              rw [← hsx0, ← smul_sub, Matrix.mul_smul, Matrix.mul_sub]
          _ = s • (x0 + a) := by
              rw [e']
              congr 1
              abel
          _ = x₁ + s • a := by rw [smul_add, hsx0]
      have hkey : mat g⁻¹ * (eM v n - S * (b * r)) = eM v n + S * (a * r) := by
        rw [← D.right, hSx, hSx, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.sub_mul, ← Matrix.add_mul, ← Matrix.mul_assoc, e0]
      have hsk : ∀ p : Matrix (Fin n) (Fin n) (AE F E), sg v ϖ • (sg v (ϖ ^ k₀) • p) = s • p := fun p => by
        rw [smul_smul, sg_mul_pk, hs, hk, pow_succ']
      obtain ⟨q, hq, hq1⟩ := D.unit (sg v (ϖ ^ k₀) • (-(b * r))) (D.smul_mem _ (hϖO _) _ (neg_mem hβ))
      obtain ⟨q', hq', hq1'⟩ := D.unit (sg v (ϖ ^ k₀) • (a * r)) (D.smul_mem _ (hϖO _) _ hα)
      rw [hsk, smul_neg, ← sub_eq_add_neg, ← hSx] at hq1
      rw [hsk, ← hSx] at hq1'
      have eL : ∀ x ∈ Λ, eM v n * x = x := fun x hx => by
        rw [Matrix.smul_mul, Matrix.one_mul, sg_one_smul_pk (D.at_mem x hx)]
      have eR : ∀ x : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) x → x * eM v n = x := fun x hx => by
        rw [Matrix.mul_smul, Matrix.mul_one, sg_one_smul_pk hx]
      obtain ⟨c1, c2⟩ := cong_key_pk (s := S) (m := mat g⁻¹) (m' := mat g) hcomm hkey hgm hq1 hq1' (eL q hq) (eL q' hq')
        (eR _ (D.at_mem _ hα)) (eR _ (D.at_mem _ hβ)) (eL _ hα) (eL _ hβ) (eL _ D.one_mem) (eR _ hg') (eR _ hg)
      simp only [hSx] at c1 c2
      exact (memH g).2 ⟨hg, ⟨_, add_mem (sub_mem (neg_mem hβ) (D.mul_mem _ hα _ hq')) (hsΛ _ (D.mul_mem _ hβ _ (D.mul_mem _ hα _ hq'))), c2⟩,
        ⟨_, add_mem (add_mem hα (D.mul_mem _ hβ _ hq)) (hsΛ _ (D.mul_mem _ hα _ (D.mul_mem _ hβ _ hq))), c1⟩⟩
  refine ⟨H, φ, ⟨hφS, hφ0, fun g hg => Subgroup.subset_closure ((memH g).1 hg).1, fun g hg => (hsm g hg).2.2, ?_, hfix, hsep⟩,
    fun g hg => (hsm g hg).1⟩
  obtain ⟨O, hO, h1, hOg⟩ := D.nbhd k
  refine ⟨O, hO, h1, fun g hg hgO => ?_⟩
  have hu := mem_UAt_of_locGrp_pk hg
  have := hOg g hu hgO
  exact (memH g).2 ⟨hu, hs ▸ this.1, hs ▸ this.2⟩
end Thm
end UpperTheory.TP.BA
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TP
theorem tLift_of_tools_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.UpperTheory.TP.TLift_k :=
  _root_.UpperTheory.TP.tLift_of_k T hH brEx (_root_.UpperTheory.TP.hgtFst_k T) (_root_.UpperTheory.TP.realPair_k T)
    (_root_.UpperTheory.TP.nonVan_k T (_root_.UpperTheory.TP.rallis_k T) (_root_.UpperTheory.TP.decomp_k T) (_root_.UpperTheory.TP.bumpAny_k T) (_root_.UpperTheory.TP.datum_k T) (_root_.UpperTheory.TP.tail_k T) absNe (_root_.UpperTheory.TP.schurStep_k T)) (_root_.UpperTheory.TP.liftAut_k T) projEx
    (_root_.UpperTheory.TP.readLift_k T (_root_.UpperTheory.TP.liftAut_k T) absIso)
end UpperTheory.TP
end
