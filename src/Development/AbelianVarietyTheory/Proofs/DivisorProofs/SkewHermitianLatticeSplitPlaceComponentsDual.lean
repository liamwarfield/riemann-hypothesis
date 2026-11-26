module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeInertPlaceSelfDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentCoprimeAtGoodPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalLatticeIdealMapSmulIffGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalLatticeIdealMapSmulIffGenerator
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LatLocIdealSmul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem smul_tmul_fun {v : HeightOneSpectrum (𝓞 F)} (z b : Fv F v) (x : Fin n → E) :
    (z • fun i => b ⊗ₜ[F] x i) = fun i => (z * b) ⊗ₜ[F] x i := by
  funext i
  simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]

omit [NumberField E] in
theorem tmul_algebraMap_mul {v : HeightOneSpectrum (𝓞 F)} (a : Fv F v) (c : F) (e : E) :
    a ⊗ₜ[F] (algebraMap F E c * e) = (algebraMap F (Fv F v) c * a) ⊗ₜ[F] e := by
  rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def]

noncomputable def smulSet (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v) :
    AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  (GlobalTheory.AdelicU.latLoc F L v).toAddSubgroup.map (DistribSMul.toAddMonoidHom _ z)

omit [NumberField E] in
theorem mem_smulSet {L : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)} {z : Fv F v}
    {y : Fin n → Fv F v ⊗[F] E} : y ∈ smulSet L v z ↔ ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  simp only [smulSet, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, DistribSMul.toAddMonoidHom_apply]
  exact ⟨fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩, fun ⟨x, hx, e⟩ => ⟨x, hx, e.symm⟩⟩

theorem mem_latLoc_idealMap_smul_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (hle : ∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z)
    (hex : ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z) :
    ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E,
      y ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v ↔
        ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  intro y
  rw [← mem_smulSet]
  constructor
  · intro hy

    have key : ∀ a ∈ v.adicCompletionIntegers F, ∀ d ∈ I, ∀ x₀ ∈ L,
        (fun i => a ⊗ₜ[F] (algebraMap F E (d : F) * x₀ i)) ∈ smulSet L v z := by
      intro a ha d hd x₀ hx₀
      simp_rw [tmul_algebraMap_mul]
      by_cases hz : z = 0
      · have h0 : algebraMap F (Fv F v) (d : F) = 0 := by
          have := hle d hd
          rw [hz, map_zero] at this
          exact (Valuation.zero_iff _).1 (le_antisymm this zero_le')
        rw [h0, zero_mul]
        simp only [TensorProduct.zero_tmul]
        exact zero_mem _
      · refine mem_smulSet.2 ⟨fun i => (algebraMap F (Fv F v) (d : F) * a / z) ⊗ₜ[F] x₀ i,
          GlobalTheory.AdelicU.tmul_mem_latLoc ?_ hx₀, ?_⟩
        · rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
          have hzv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
          rw [map_div₀, map_mul, div_le_one₀ (zero_lt_iff.2 hzv)]
          calc Valued.v (algebraMap F (Fv F v) (d : F)) * Valued.v a
              ≤ Valued.v z * 1 := mul_le_mul' (hle d hd) ha
            _ = Valued.v z := mul_one _
        · rw [smul_tmul_fun, mul_div_cancel₀ _ hz]
    refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => y ∈ smulSet L v z) ?_ (zero_mem _)
      (fun _ _ h h' => add_mem h h') (fun _ h => neg_mem h) hy
    intro a ha x' hx'
    refine Submodule.smul_induction_on hx' ?_ ?_
    · intro r hr x₀ hx₀
      induction hr using Submodule.span_induction generalizing x₀ with
      | mem r hr =>
        obtain ⟨d, hd, rfl⟩ := hr
        exact key a ha d hd x₀ hx₀
      | zero =>
        simp only [zero_smul, Pi.zero_apply, TensorProduct.tmul_zero]
        exact zero_mem _
      | add r s _ _ hr hs =>
        have e : (fun i => a ⊗ₜ[F] ((r + s) • x₀) i) =
            (fun i => a ⊗ₜ[F] (r • x₀) i) + fun i => a ⊗ₜ[F] (s • x₀) i := by
          funext i; simp [add_smul, TensorProduct.tmul_add]
        rw [e]; exact add_mem (hr x₀ hx₀) (hs x₀ hx₀)
      | smul o r _ hr =>
        have e : (o • r) • x₀ = r • (o • x₀) := by rw [smul_eq_mul, mul_smul, smul_comm]
        rw [e]; exact hr _ (L.smul_mem o hx₀)
    · intro x y hx hy
      have e : (fun i => a ⊗ₜ[F] (x + y) i) = (fun i => a ⊗ₜ[F] x i) + fun i => a ⊗ₜ[F] y i := by
        funext i; simp [TensorProduct.tmul_add]
      rw [e]; exact add_mem hx hy
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_smulSet.1 hy
    obtain ⟨d₀, hd₀, hv⟩ := hex
    refine GlobalTheory.AdelicU.latLoc_induction
      (p := fun x => z • x ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v) ?_
      (by rw [smul_zero]; exact zero_mem _) (fun _ _ h h' => by rw [smul_add]; exact add_mem h h')
      (fun _ h => by rw [smul_neg]; exact neg_mem h) hx
    intro a ha x₀ hx₀
    by_cases hz : z = 0
    · rw [hz, zero_smul]; exact zero_mem _
    have hzv : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
    have hd0 : algebraMap F (Fv F v) (d₀ : F) ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact hzv hv.symm
    have hmem : (algebraMap (𝓞 F) (𝓞 E) d₀ • x₀) ∈ I.map (algebraMap (𝓞 F) (𝓞 E)) • L :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hd₀) hx₀
    have hc : z * a / algebraMap F (Fv F v) (d₀ : F) ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
      rw [map_div₀, map_mul, hv, mul_div_cancel_left₀ _ hzv]
      exact ha
    have := GlobalTheory.AdelicU.tmul_mem_latLoc (L := I.map (algebraMap (𝓞 F) (𝓞 E)) • L) hc hmem
    convert this using 1
    rw [smul_tmul_fun]
    funext i
    change _ = (z * a / algebraMap F (Fv F v) (d₀ : F)) ⊗ₜ[F] (algebraMap F E (d₀ : F) * x₀ i)
    rw [tmul_algebraMap_mul, mul_div_cancel₀ _ hd0]

end GlobalTheory.LatLocIdealSmul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalLatticeIdealMapSmulIffGeneratorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localLattice_idealMap_smul_iff_generator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v), (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) → (∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z) → ∀ y : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E, y ∈ GlobalTheory.AdelicU.latLoc F (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) v ↔ ∃ x ∈ GlobalTheory.AdelicU.latLoc F L v, y = z • x := by
  first | exact @GlobalTheory.LatLocIdealSmul.mem_latLoc_idealMap_smul_iff | exact GlobalTheory.LatLocIdealSmul.mem_latLoc_idealMap_smul_iff | (intros; apply GlobalTheory.LatLocIdealSmul.mem_latLoc_idealMap_smul_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdeal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open IsDedekindDomain HeightOneSpectrum WithZero

theorem locGen_val_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (d : 𝓞 F) :
    Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = v.intValuation d := by
  have h := valuedAdicCompletion_eq_valuation' (K := F) v (d : F)
  rw [← valuation_of_algebraMap (K := F) v d]
  exact h

theorem ideal_localGenerator : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  intro F _ _ I v hI
  by_cases hv : I ≤ v.asIdeal
  · classical
    have hex : ∃ n : ℕ, ∃ d ∈ I, v.intValuation d = exp (-(n : ℤ)) := by
      obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
      exact ⟨_, d, hdI, v.intValuation_if_neg hd0⟩
    obtain ⟨d0, hd0I, hd0v⟩ := Nat.find_spec hex
    refine ⟨algebraMap F _ (d0 : F), ?_, fun h => absurd hv h, ?_, d0, hd0I, rfl⟩
    · intro h
      have h2 := locGen_val_eq F v d0
      rw [h, map_zero, hd0v] at h2
      exact exp_ne_zero h2.symm
    · intro d hd
      rw [locGen_val_eq, locGen_val_eq, hd0v]
      by_cases hd0 : d = 0
      · simp [hd0]
      · have hk := v.intValuation_if_neg hd0
        rw [hk, exp_le_exp, neg_le_neg_iff, Int.ofNat_le]
        exact Nat.find_min' hex ⟨d, hd, hk⟩
  · obtain ⟨d, hdI, hdv⟩ := Set.not_subset.mp hv
    refine ⟨1, one_ne_zero, fun _ => rfl, ?_, d, hdI, ?_⟩
    · intro e _
      rw [locGen_val_eq, map_one]
      exact v.intValuation_le_one e
    · rw [locGen_val_eq, map_one]
      exact intValuation_eq_one_iff.mpr hdv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdealStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_of_nonzero_ideal : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  first | exact @GlobalTheory.ideal_localGenerator | exact GlobalTheory.ideal_localGenerator | (intros; apply GlobalTheory.ideal_localGenerator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualRingOfIntegersIffOfUnramifiedExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualRingOfIntegersIffOfUnramifiedExtension
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped nonZeroDivisors

namespace GlobalTheory.UnrTraceDual

theorem traceDual_ringOfIntegers_iff_of_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  intro F E _ _ _ _ _ hU e
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := inferInstance
  have hEq : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu, Ideal.top_mul]
  have hint : ∀ x : E, IsIntegral ℤ x ↔ x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro x
    rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]
  have h1 : (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔
      e ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))]
    constructor
    · intro h a ha
      obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).1 ha
      rw [Algebra.traceForm_apply, mul_comm]
      exact RingHom.mem_range.2 (IsIntegrallyClosed.isIntegral_iff.1 (h o))
    · intro h o
      have := h (algebraMap (𝓞 E) E o) ((FractionalIdeal.mem_one_iff (𝓞 E)⁰).2 ⟨o, rfl⟩)
      rw [Algebra.traceForm_apply, mul_comm] at this
      exact IsIntegrallyClosed.isIntegral_iff.2 (RingHom.mem_range.1 this)
  have h2 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) =
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E), inv_inv]
  have hne : ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact differentIdeal_ne_bot
  rw [h1, h2, FractionalIdeal.mem_inv_iff hne, hEq]
  let J : Ideal (𝓞 E) :=
    { carrier := {x | IsIntegral ℤ (algebraMap (𝓞 E) E x * e)}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at *
        exact ha.add hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, zero_mul]
        exact isIntegral_zero
      smul_mem' := by
        intro c x hx
        have hx' : IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := hx
        have hc : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
        show IsIntegral ℤ (algebraMap (𝓞 E) E (c * x) * e)
        rw [map_mul, mul_assoc]
        exact IsIntegral.mul hc hx' }
  have hJ : ∀ x : 𝓞 E, x ∈ J ↔ IsIntegral ℤ (algebraMap (𝓞 E) E x * e) := fun _ => Iff.rfl
  have hL : (∀ y ∈ (((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (𝓞 E)⁰ E), e * y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔
      (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) ≤ J := by
    constructor
    · intro h x hx
      rw [hJ, hint, mul_comm]
      exact h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hx)
    · intro h y hy
      obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
      rw [mul_comm, ← hint]
      exact (hJ x).1 (h hx)
  rw [hL, Ideal.map_le_iff_le_comap]
  constructor
  · intro h d hd
    have := (hJ _).1 (h hd)
    rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E] at this
  · intro h d hd
    show algebraMap (𝓞 F) (𝓞 E) d ∈ J
    rw [hJ, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F E]
    exact h d hd

end GlobalTheory.UnrTraceDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualRingOfIntegersIffOfUnramifiedExtensionStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceDual_ringOfIntegers_iff_of_unramified_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * e))) ↔ ∀ d ∈ differentIdeal ℤ (𝓞 F), IsIntegral ℤ (algebraMap F E (d : F) * e) := by
  first | exact @GlobalTheory.UnrTraceDual.traceDual_ringOfIntegers_iff_of_unramified | exact GlobalTheory.UnrTraceDual.traceDual_ringOfIntegers_iff_of_unramified | (intros; apply GlobalTheory.UnrTraceDual.traceDual_ringOfIntegers_iff_of_unramified <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapSmulIsLatticeOfNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapSmulIsLatticeOfNeBot
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise

namespace GlobalTheory

theorem ideal_map_smul_isLattice (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)) :
    I ≠ ⊥ → Submodule.IsLattice E L →
      Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  intro hI hL
  have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) • L ≤ L := Submodule.smul_le_right
  obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hdE : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hd0
    have h1 : algebraMap (𝓞 F) (𝓞 E) d = 0 := by exact_mod_cast h
    exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h1)
  set u : Eˣ := Units.mk0 _ hdE
  have hsub : (u • L : Submodule (𝓞 E) (Fin n → E)) ≤ I.map (algebraMap (𝓞 F) (𝓞 E)) • L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have : (u • y : Fin n → E) = (algebraMap (𝓞 F) (𝓞 E) d) • y := by
      rw [Units.smul_def, Units.val_mk0, ← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) d) y]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hdI) hy
  exact Submodule.IsLattice.of_fg E (Submodule.FG.of_le hL.fg hle)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapSmulIsLatticeOfNeBotStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_map_smul_isLattice_of_ne_bot : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)), I ≠ ⊥ → Submodule.IsLattice E L → Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  first | exact @GlobalTheory.ideal_map_smul_isLattice | exact GlobalTheory.ideal_map_smul_isLattice | (intros; apply GlobalTheory.ideal_map_smul_isLattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSplitPlaceComponentsDual
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SkewSplitDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x x' : Fin n → E) :
    form σ J y (x + x') = form σ J y x + form σ J y x' := by
  have : (fun i => σ ((x + x') i)) = (fun i => σ (x i)) + fun i => σ (x' i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (y x : Fin n → E) :
    form σ J y (c • x) = σ c * form σ J y x := by
  have : (fun i => σ ((c • x) i)) = σ c • fun i => σ (x i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem isIntegral_iff_mem_range (e : E) : IsIntegral ℤ e ↔ e ∈ (algebraMap (𝓞 E) E).range :=
  ⟨fun h => ⟨⟨e, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.isIntegral_coe⟩

theorem coe_algebraMap_int (d : 𝓞 F) : ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) = algebraMap F E (d : F) := rfl

theorem eq_dualGlob {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    (hu : Algebra.Unramified (𝓞 F) (𝓞 E))
    (hdual : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ J y x))) :
    L = SelfDual.dualGlob σ Jᵀ ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  ext y
  rw [SelfDual.mem_dualGlob]
  simp only [hE_transpose]
  constructor
  · intro hy x hx
    refine Submodule.smul_induction_on hx (fun i hi x hx => ?_) (fun a b ha hb => ?_)
    · have key := (GlobalTheory.T.traceDual_ringOfIntegers_iff_of_unramified_extension F E hu (form σ J y x)).1 ((hdual y).1 hy x hx)
      have e1 : i • x = (i : E) • x := by ext j; rfl
      rw [e1, form_smul_right]
      have hi' : i ∈ Ideal.span (algebraMap (𝓞 F) (𝓞 E) '' (differentIdeal ℤ (𝓞 F) : Set (𝓞 F))) := hi
      refine Submodule.span_induction
        (p := fun (i : 𝓞 E) _ => σ (i : E) * form σ J y x ∈ (algebraMap (𝓞 E) E).range) ?_ ?_ ?_ ?_ hi'
      · rintro _ ⟨d, hd, rfl⟩
        rw [coe_algebraMap_int, AlgHom.commutes, ← isIntegral_iff_mem_range]
        exact key d hd
      · simp
      · intro a b _ _ ha hb
        simp only [Subalgebra.coe_add, map_add (f := _), add_mul]
        exact add_mem ha hb
      · intro c a _ ha
        have e2 : σ ((c • a : 𝓞 E) : E) * form σ J y x = σ (c : E) * (σ (a : E) * form σ J y x) := by
          rw [← mul_assoc, ← map_mul]; rfl
        rw [e2]
        exact mul_mem ((isIntegral_iff_mem_range _).1
          ((isIntegral_algHom_iff ((σ : E →+* E).toIntAlgHom) σ.injective).2 c.isIntegral_coe)) ha
    · rw [form_add_right]; exact add_mem ha hb
  · intro hy
    rw [hdual y]
    intro x hx o
    refine (GlobalTheory.T.traceDual_ringOfIntegers_iff_of_unramified_extension F E hu (form σ J y x)).2 (fun d hd => ?_) o
    have hmem : (algebraMap (𝓞 F) (𝓞 E) d) • x ∈ (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • L :=
      Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hd) hx
    have h2 := hy _ hmem
    have e1 : (algebraMap (𝓞 F) (𝓞 E) d) • x = ((algebraMap (𝓞 F) (𝓞 E) d : 𝓞 E) : E) • x := by ext j; rfl
    rw [e1, form_smul_right, coe_algebraMap_int, AlgHom.commutes] at h2
    exact (isIntegral_iff_mem_range _).2 h2

theorem mem_splitLat_comp_iff_skew {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hskew : ∀ i j, σ (J j i) = -J i j) {L L₁ : Submodule (𝓞 E) (Fin n → E)} {v : HeightOneSpectrum (𝓞 F)}
    (t : E →ₐ[F] Fv F v) (z : Fv F v)
    (hloc : latLoc F L v = dualLoc σ Jᵀ L₁ v)
    (h1 : ∀ y, y ∈ latLoc F L₁ v ↔ ∃ x ∈ latLoc F L v, y = z • x) (u' : Fin n → Fv F v) :
    u' ∈ splitLat (t.comp σ) L ↔ ∀ u ∈ splitLat t L, z * (u ⬝ᵥ J.map t *ᵥ u') ∈ v.adicCompletionIntegers F := by
  have hJ : Jᵀ.map (t.comp σ) = -J.map t := by
    ext i j; simp [Matrix.transpose_apply, hskew]
  rw [← splitIncl_mem_latLoc_iff hcm, hloc]
  change (∀ x ∈ latLoc F L₁ v, hLin σ Jᵀ (Fv F v) (splitIncl hcm (t.comp σ) u') x ∈ intLoc F E v) ↔ _
  have hc : ∀ x, hLin σ Jᵀ (Fv F v) (splitIncl hcm (t.comp σ) u') x ∈ intLoc F E v ↔
      splitVec t x ⬝ᵥ J.map t *ᵥ u' ∈ v.adicCompletionIntegers F := by
    intro x
    rw [mem_intLoc_iff_split hcm t, splitProj_hLin, splitProj_hLin, comp_conj_conj hcm, splitVec_splitIncl_comp,
      splitVec_splitIncl, hJ, Matrix.mulVec_zero, dotProduct_zero, Matrix.neg_mulVec, dotProduct_neg, neg_mem_iff]
    exact and_iff_right (zero_mem _)
  simp only [hc]
  have hsv : ∀ x : Fin n → Fv F v ⊗[F] E, splitVec t (z • x) = z • splitVec t x := fun x =>
    funext fun i => map_smul (splitProj t) z (x i)
  constructor
  · rintro H _ ⟨x, hx, rfl⟩
    have := H (z • x) ((h1 _).2 ⟨x, hx, rfl⟩)
    rwa [hsv, smul_dotProduct, smul_eq_mul] at this
  · intro H y hy
    obtain ⟨x, hx, rfl⟩ := (h1 y).1 hy
    rw [hsv, smul_dotProduct, smul_eq_mul]
    exact H _ ⟨x, hx, rfl⟩

theorem skewSplitDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)), IsSplitBasis t W.L c →
    ∃ (z : (Fv F v)ˣ) (c₂ : GL (Fin d) (Fv F v)), (PsiUnr B.ψ v → z = 1) ∧
      (c₂⁻¹).1 = (z : Fv F v) • (c.1ᵀ * W.J.map t) ∧ IsSplitBasis (t.comp σ) W.L c₂ := by
  intro F E _ _ _ _ _ σ B d W r s hB hW v t c hc
  haveI := hB.unram
  have hcm : IsCMExt F E σ := hB.cm
  have h𝔡0 : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  have hdet : W.J.det ≠ 0 := GlobalTheory.InertSelfDual.det_ne_zero_of_skew σ B hW
  have hdetT : W.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hdet
  have hfull : Submodule.IsFullLattice E
      ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • W.L) := by
    haveI := hW.lat
    haveI := GlobalTheory.T.ideal_map_smul_isLattice_of_ne_bot F E d W.L _ h𝔡0 hW.lat.toIsLattice
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔡0
    have haE : ((algebraMap (𝓞 F) (𝓞 E) a : 𝓞 E) : E) ≠ 0 := by
      intro h
      apply ha0
      have h1 : algebraMap (𝓞 F) (𝓞 E) a = 0 := by exact_mod_cast h
      exact (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)) (by simpa using h1)
    let u : Eˣ := Units.mk0 _ haE
    apply Submodule.IsFullLattice.of_le E (M := u • W.L)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    have heq : (u • y : Fin d → E) = (algebraMap (𝓞 F) (𝓞 E) a) • y := by
      rw [Units.smul_def, Units.val_mk0, ← algebraMap_smul E (algebraMap (𝓞 F) (𝓞 E) a) y]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) hy
  have hglob := eq_dualGlob (σ := σ) (J := W.J) (L := W.L) hB.unram hW.dual
  have hloc : latLoc F W.L v =
      dualLoc σ W.Jᵀ ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) • W.L) v :=
    (congrArg (fun L => latLoc F L v) hglob).trans
      (SelfDual.latLoc_dualGlob hdetT hfull v)
  obtain ⟨z, hz0, hz1, hzle, hzeq⟩ := GlobalTheory.T.exists_local_generator_of_nonzero_ideal F (differentIdeal ℤ (𝓞 F)) v h𝔡0
  have key := mem_splitLat_comp_iff_skew hcm hW.skew t z hloc (GlobalTheory.T.mem_localLattice_idealMap_smul_iff_generator F E d W.L _ v z hzle hzeq)
  set M : Matrix (Fin d) (Fin d) (Fv F v) := z • (c.1ᵀ * W.J.map t) with hM
  have hMdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ hz0) (mul_ne_zero (c.isUnit.map Matrix.detMonoidHom).ne_zero ?_)
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero t).2 hdet
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin d) (Fv F v), g.1 = M :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet, rfl⟩
  refine ⟨Units.mk0 z hz0, g⁻¹, fun hp => Units.ext ?_, ?_, ?_⟩
  · simpa using hz1 (GlobalTheory.DiffCoprimeP.not_le_differentIdeal_of_psiUnr hB.std v hp)
  · rw [inv_inv, hg]; rfl
  · have hMc : M * (g⁻¹).1 = 1 := by rw [← hg]; exact g.mul_inv
    have hid : ∀ (w a : Fin d → Fv F v), z * ((c.1 *ᵥ a) ⬝ᵥ W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w)) = a ⬝ᵥ w := by
      intro w a
      have e1 : z * ((c.1 *ᵥ a) ⬝ᵥ W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w)) = a ⬝ᵥ ((M * (g⁻¹).1) *ᵥ w) := by
        rw [hM, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, dotProduct_smul,
          smul_eq_mul]
        congr 1
        generalize W.J.map t *ᵥ ((g⁻¹).1 *ᵥ w) = X
        simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, hMc, Matrix.one_mulVec]
    intro w
    rw [key]
    constructor
    · intro hw u hu
      have hu' := hc.mem_iff.1 hu
      have e : u = c.1 *ᵥ ((c⁻¹).1 *ᵥ u) := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      rw [e, hid]
      simp only [dotProduct]
      exact sum_mem fun i _ => mul_mem (hu' i) (hw i)
    · intro H i
      have hs : ∀ j, (Pi.single i (1 : Fv F v) : Fin d → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
        by_cases e : j = i
        · subst e; simp
        · simp [e]
      have := H _ ((hc _).1 hs)
      rwa [hid, single_dotProduct, one_mul] at this

end GlobalTheory.SkewSplitDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSplitPlaceComponentsDualStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitianLattice_splitPlace_components_dual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (c : GL (Fin d) (Fv F v)), IsSplitBasis t W.L c →
    ∃ (z : (Fv F v)ˣ) (c₂ : GL (Fin d) (Fv F v)), (PsiUnr B.ψ v → z = 1) ∧
      (c₂⁻¹).1 = (z : Fv F v) • (c.1ᵀ * W.J.map t) ∧ IsSplitBasis (t.comp σ) W.L c₂ := by
  first | exact @GlobalTheory.SkewSplitDual.skewSplitDual | exact GlobalTheory.SkewSplitDual.skewSplitDual | (intros; apply GlobalTheory.SkewSplitDual.skewSplitDual <;> assumption)
end
