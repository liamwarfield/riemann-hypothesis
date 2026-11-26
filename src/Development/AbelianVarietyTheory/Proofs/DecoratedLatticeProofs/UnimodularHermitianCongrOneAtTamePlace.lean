module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SigV
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.FinPl
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

def intV (D : D7) (v : Pl D) : AddSubgroup (Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers D.host.F, ∃ x : 𝓞 D.host.E, y = a ⊗ₜ[D.host.F] (x : D.host.E)}

def sigV (D : D7) (v : Pl D) : Fv D.host.F v ⊗[D.host.F] D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E :=
  Algebra.TensorProduct.map (AlgHom.id D.host.F (Fv D.host.F v)) D.sp.cm.sig

end GlobalTheory.FixedUnitNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section
open IsDedekindDomain NumberField
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.IwaFixed

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y h

def intIn (D : D7) (v : Pl D) : v.adicCompletionIntegers D.host.F →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)).comp (algebraMap _ (Fv D.host.F v))

theorem integral_compFin (v : Pl D) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (intIn D v).IsIntegralElem (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    have e : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        intIn D v ⟨evalV D.host.F v a, ha v⟩ *
          (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E) (o : D.host.E) := by
      show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _) (a ⊗ₜ[D.host.F] (o : D.host.E)) =
        (evalV D.host.F v a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (o : D.host.E))
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    rw [e]
    refine RingHom.IsIntegralElem.mul _ (RingHom.isIntegralElem_map _) ?_
    obtain ⟨p, hp, hpo⟩ : IsIntegral ℤ (o : D.host.E) := o.2
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h := congrArg (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom hpo
    rw [Polynomial.hom_eval₂, map_zero] at h
    rw [RingHom.ext_int ((intIn D v).comp (Int.castRingHom _)) ((Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Fv D.host.F v ⊗[D.host.F] D.host.E).toRingHom.comp (algebraMap ℤ D.host.E))]
    exact h
  | zero => rw [map_zero]; exact RingHom.isIntegralElem_zero _
  | add z z' _ _ h h' => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ h h'
  | neg z _ h => rw [map_neg]; exact RingHom.IsIntegralElem.neg _ h

theorem mem_int_of_integral (v : Pl D) (a : Fv D.host.F v)
    (h : (intIn D v).IsIntegralElem (a ⊗ₜ[D.host.F] (1 : D.host.E))) : a ∈ v.adicCompletionIntegers D.host.F := by
  obtain ⟨p, hp, hpa⟩ := h
  have hinj : Function.Injective (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :=
    RingHom.injective _
  have hi : IsIntegral (v.adicCompletionIntegers D.host.F) a := by
    refine ⟨p, hp, hinj ?_⟩
    rw [Polynomial.hom_eval₂, map_zero]
    exact hpa
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact y.2

theorem exists_inv (v : Pl D) {x : AE D} (hx : x ∈ idAt D (· = v)) (u : (v.adicCompletionIntegers D.host.F)ˣ)
    (hu : compAt D v x = ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E)) :
    ∃ y ∈ intAt D (· = v), x * y = idem D (· = v) := by
  classical
  obtain ⟨c, hci, hc⟩ : ∃ c : Fv D.host.F v, c ∈ v.adicCompletionIntegers D.host.F ∧ (u.val.1 : Fv D.host.F v) * c = 1 :=
    ⟨u.inv.1, u.inv.2, congrArg Subtype.val u.val_inv⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · exact pair_mem_idAt _ _ (fun w hw => evalV_single_ne _ v c hw) _
  · rw [finPart_pair]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v c, fun w => ?_, 1, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same]; exact hci
    · rw [evalV_single_ne _ v c hw]; exact zero_mem _
  · rw [← sub_eq_zero]
    apply eq_zero_of_comp
    · rw [map_sub, map_mul, infPart_of_idAt hx, infPart_of_idAt (idem_mem_idAt _), zero_mul, sub_zero]
    · intro w
      rw [map_sub, map_mul, compAt_idem]
      by_cases hw : w = v
      · subst hw
        rw [hu, compAt_pair, evalV_single_same, if_pos rfl, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hc,
          ← Algebra.TensorProduct.one_def, sub_self]
      · rw [compAt_of_idAt hx hw, if_neg hw, zero_mul, sub_zero]

theorem fixed_unit_or : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x →
    (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  intro D v ε _ _ _ hε hid x hx hfix
  classical
  have hεe : ε = idem D (· = v) := by
    have h1 := (hid _).1 (idem_mem_idAt (· = v))
    have h2 := (mem_idAt_iff (· = v) ε).1 hε.1
    rw [← h2, mul_comm, h1]
  subst hεe
  obtain ⟨b, hb⟩ := GlobalTheory.CharConjFixed.fixed_mem D x hfix
  have hcomp : compAt D v x = evalV D.host.F v (sndA D.host.F b) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [← hb]
    show Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id _ _)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (b ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  have hint : evalV D.host.F v (sndA D.host.F b) ∈ v.adicCompletionIntegers D.host.F := by
    apply mem_int_of_integral
    rw [← hcomp]
    exact integral_compFin v hx.2
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨_, hint⟩ : v.adicCompletionIntegers D.host.F) with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    refine exists_inv v hx.1 u ?_
    rw [hu, hcomp]
  · right
    refine exists_inv v (sub_mem (idem_mem_idAt _) hx.1) u ?_
    rw [hu, map_sub, compAt_idem, if_pos rfl, hcomp, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    rfl

end GlobalTheory.IwaFixed

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjFixedIntegralIsUnitOrIdemSubUnitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ x ∈ intAt D (· = v), cA D x = x → (∃ y ∈ intAt D (· = v), x * y = ε) ∨ (∃ y ∈ intAt D (· = v), (ε - x) * y = ε) := by
  first | exact @GlobalTheory.IwaFixed.fixed_unit_or | exact GlobalTheory.IwaFixed.fixed_unit_or | (intros; apply GlobalTheory.IwaFixed.fixed_unit_or <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm

theorem evalAtPlace_singleAtPlace_self (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    evalV F v (singleV F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y

theorem evalAtPlace_singleAtPlace_of_ne (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) : evalV F w (singleV F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) y hw

theorem exists_integralAdele_atPlace_component_tmul (D : D7) (v : Pl D) (a : Fv D.host.F v) (ha : a ∈ v.adicCompletionIntegers D.host.F)
    (x : 𝓞 D.host.E) : ∃ y ∈ intAt D (· = v), compAt D v y = a ⊗ₜ[D.host.F] (x : D.host.E) := by
  have hc : ∀ w : Pl D, compAt D w (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) =
      evalV D.host.F w (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E) := by
    intro w
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    rfl
  refine ⟨pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw => ?_⟩
    · change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
        (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) = 0
      rw [Algebra.TensorProduct.map_tmul]
      exact TensorProduct.zero_tmul _ _
    · rw [hc, evalAtPlace_singleAtPlace_of_ne _ v a hw, TensorProduct.zero_tmul]
  · change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      (pairA D.host.F 0 (singleV D.host.F v a) ⊗ₜ[D.host.F] (x : D.host.E)) ∈ intAE D
    rw [Algebra.TensorProduct.map_tmul]
    refine AddSubgroup.subset_closure ⟨singleV D.host.F v a, fun w => ?_, x, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [evalAtPlace_singleAtPlace_self]; exact ha
    · rw [evalAtPlace_singleAtPlace_of_ne _ v a hw]; exact zero_mem _
  · rw [hc, evalAtPlace_singleAtPlace_self]

theorem exists_intAt_compAt_eq : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v →
    ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  intro D v z hz
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact exists_integralAdele_atPlace_component_tmul D v a ha x
  | zero =>
    exact ⟨0, ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩, map_zero _⟩
  | add y z _ _ h1 h2 =>
    obtain ⟨a, ha, hya⟩ := h1
    obtain ⟨b, hb, hzb⟩ := h2
    exact ⟨a + b, GlobalTheory.IwaPlace.SdComap.intAt_add ha hb, by rw [RingHom.map_add (f := _), hya, hzb]⟩
  | neg y _ h =>
    obtain ⟨a, ha, hya⟩ := h
    exact ⟨-a, ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩, by rw [RingHom.map_neg, hya]⟩

end GlobalTheory.FixedUnitNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdeleAtPlaceWithComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdele_atPlace_with_component : ∀ (D : D7) (v : Pl D) (z : Fv D.host.F v ⊗[D.host.F] D.host.E), z ∈ intV D v → ∃ x ∈ intAt D (· = v), compAt D v x = z := by
  first | exact @GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | exact GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq | (intros; apply GlobalTheory.FixedUnitNorm.exists_intAt_compAt_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem integral_of_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t →
    w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  intro D w t n ht hn
  have hint : ∀ s : 𝓞 D.host.F, IsIntegral ℤ (algebraMap D.host.F D.host.E s) := fun s =>
    (NumberField.RingOfIntegers.isIntegral_coe s).map (IsScalarTower.toAlgHom ℤ D.host.F D.host.E)
  let t' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E t, hint t⟩
  let n' : 𝓞 D.host.E := ⟨algebraMap D.host.F D.host.E n, hint n⟩
  have hw : IsIntegral (𝓞 D.host.E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C n', ?_, ?_⟩
    · monicity!
    · have h1 : algebraMap (𝓞 D.host.E) D.host.E t' = w + D.sp.cm.sig w := ht.symm
      have h2 : algebraMap (𝓞 D.host.E) D.host.E n' = w * D.sp.cm.sig w := hn.symm
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2]
      ring
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := 𝓞 D.host.E) (K := D.host.E)).mp hw
  exact ⟨y, hy⟩

end GlobalTheory.FixedUnitNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerOfRelativeTraceNormIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_of_relative_trace_norm_integral : ∀ (D : D7) (w : D.host.E) (t n : 𝓞 D.host.F), w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → ∃ x : 𝓞 D.host.E, (x : D.host.E) = w := by
  first | exact @GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | exact GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral | (intros; apply GlobalTheory.FixedUnitNorm.integral_of_trace_norm_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionTensorRelativeBasisCoordsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionTensorRelativeBasisCoordsUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.CoordUnique

theorem coords_unique_of_field {K E A : Type*} [Field K] [Ring E] [Nontrivial E] [Algebra K E] [AddCommGroup A]
    [Module K A] (w : E) (hw : ∀ f : K, algebraMap K E f ≠ w) (a b : A)
    (h : a ⊗ₜ[K] (1 : E) + b ⊗ₜ[K] w = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : (K × K) →ₗ[K] E, ∀ p, φ p = p.1 • (1 : E) + p.2 • w :=
    ⟨{ toFun := fun p => p.1 • (1 : E) + p.2 • w,
       map_add' := fun p q => by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel,
       map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, smul_add, RingHom.id_apply] },
      fun p => rfl⟩
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, t⟩ hst
    rw [hφ] at hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      simp [hst]
    · exfalso
      apply hw (-s / t)
      have h1 : t • w = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : w = t⁻¹ • (-(s • (1 : E))) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, div_eq_mul_inv, neg_mul, neg_smul, mul_comm]
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := A) φ hinj
  have hx : φ.lTensor A (a ⊗ₜ[K] ((1 : K), (0 : K)) +
      b ⊗ₜ[K] ((0 : K), (1 : K))) = 0 := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, hφ, hφ]
    simpa using h
  rw [← map_zero (φ.lTensor A)] at hx
  have hx0 := hinj' hx
  have ha : TensorProduct.rid K A
      ((LinearMap.fst K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = a := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.fst_apply, LinearMap.fst_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, add_zero]
  have hb : TensorProduct.rid K A
      ((LinearMap.snd K K K).lTensor A
        (a ⊗ₜ[K] ((1 : K), (0 : K)) + b ⊗ₜ[K] ((0 : K), (1 : K)))) = b := by
    rw [map_add (f := _), LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.snd_apply, LinearMap.snd_apply,
      map_add, TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, zero_smul, zero_add]
  rw [hx0, map_zero, map_zero] at ha hb
  exact ⟨ha.symm, hb.symm⟩

theorem coords_unique : ∀ (D : D7) (v : Pl D) (w : D.host.E), (∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w) →
    ∀ a b : Fv D.host.F v, a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w = 0 → a = 0 ∧ b = 0 :=
  fun _ _ w hw a b h => coords_unique_of_field w hw a b h

end GlobalTheory.CoordUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionTensorRelativeBasisCoordsUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_tensor_relativeBasis_coords_unique : ∀ (D : D7) (v : Pl D) (w : D.host.E), (∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w) → ∀ a b : Fv D.host.F v, a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w = 0 → a = 0 ∧ b = 0 := by
  first | exact @GlobalTheory.CoordUnique.coords_unique | exact GlobalTheory.CoordUnique.coords_unique | (intros; apply GlobalTheory.CoordUnique.coords_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTenso
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTenso
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

theorem compAt_mem_intV_of_intAt : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  intro D v a ha
  have h : finPart D a ∈ intAE D := ha.2
  show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v (finPart D a) ∈ intV D v
  generalize finPart D a = b at h ⊢
  induction h using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    exact ⟨_, hα v, x, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [RingHom.map_add (f := _)]; exact add_mem hy hz
  | neg y _ hy => rw [RingHom.map_neg]; exact neg_mem hy

end GlobalTheory.FixedUnitNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdeleComponentAtFinitePlaceIntegralMemLocalTensoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ intAt D (· = v) → compAt D v a ∈ intV D v := by
  first | exact @GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | exact GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt | (intros; apply GlobalTheory.FixedUnitNorm.compAt_mem_intV_of_intAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalIntegersTensorCoordsPrimeToDiscriminant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalIntegersTensorCoordsPrimeToDiscriminant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FixedUnitNorm.Coords

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem isIntegral_of_trace_norm (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) : IsIntegral ℤ w := by
  have hE : IsIntegral (𝓞 E) w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap (𝓞 F) (𝓞 E) t) * Polynomial.X +
      Polynomial.C (algebraMap (𝓞 F) (𝓞 E) n), by monicity!, ?_⟩
    have h1 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) t) = algebraMap F E t := rfl
    have h2 : algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) n) = algebraMap F E n := rfl
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, h1, h2, ← ht, ← hn]
    ring
  exact isIntegral_trans (R := ℤ) w hE

theorem exists_coords (h : IsCMExt F E σ) (w : E) (t n : 𝓞 F) (ht : w + σ w = algebraMap F E t)
    (hn : w * σ w = algebraMap F E n) (x : 𝓞 E) :
    ∃ a b : 𝓞 F, (x : E) * algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) =
      algebraMap F E a + algebraMap F E b * w := by
  have hσ := GlobalTheory.SelfDualLatticeCompare.conj_conj h
  let W : 𝓞 E := ⟨w, isIntegral_of_trace_norm w t n ht hn⟩
  let s : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)
  have hs : ∀ y : 𝓞 E, ((s y : 𝓞 E) : E) = σ y := fun _ => rfl
  have hW : ((W : 𝓞 E) : E) = w := rfl
  obtain ⟨a, ha⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((s x * W - x * s W) * (W - s W)) (by
      change σ ((σ (x : E) * w - (x : E) * σ w) * (w - σ w)) = (σ (x : E) * w - (x : E) * σ w) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h
    ((x - s x) * (W - s W)) (by
      change σ (((x : E) - σ x) * (w - σ w)) = ((x : E) - σ x) * (w - σ w)
      simp only [map_mul, map_sub, hσ]
      ring)
  have ha' : algebraMap F E a = (σ x * w - x * σ w) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) ha
  have hb' : algebraMap F E b = (x - σ x) * (w - σ w) := by
    exact congrArg (algebraMap (𝓞 E) E) hb
  refine ⟨a, b, ?_⟩
  have hd : algebraMap F E ((t ^ 2 - 4 * n : 𝓞 F) : F) = (algebraMap F E t) ^ 2 - 4 * algebraMap F E n := by
    push_cast
    simp [map_sub, map_pow, map_mul, map_ofNat]
  rw [hd, ha', hb', ← ht, ← hn]
  ring

theorem tmul_move {K : Type} [Field K] [Algebra F K] (m : K) (r : F) (e : E) :
    (algebraMap F K r * m) ⊗ₜ[F] e = m ⊗ₜ[F] (algebraMap F E r * e) := by
  rw [← Algebra.smul_def, ← Algebra.smul_def, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]

theorem coords_add {K : Type} [Field K] [Algebra F K] (a b a' b' : K) (w : E) :
    (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) + (a' ⊗ₜ[F] (1 : E) + b' ⊗ₜ[F] w) = (a + a') ⊗ₜ[F] (1 : E) + (b + b') ⊗ₜ[F] w := by
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]

theorem coords_neg {K : Type} [Field K] [Algebra F K] (a b : K) (w : E) :
    -(a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] w) = (-a) ⊗ₜ[F] (1 : E) + (-b) ⊗ₜ[F] w := by
  rw [TensorProduct.neg_tmul, TensorProduct.neg_tmul, neg_add]

end Field

end GlobalTheory.FixedUnitNorm.Coords

namespace GlobalTheory.FixedUnitNorm.Coords


set_option maxHeartbeats 1000000 in
theorem mem_intV_coords : ∀ (D : D7) (v : Pl D) (w : D.host.E) (t n : 𝓞 D.host.F),
    w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n →
    t ^ 2 - 4 * n ∉ v.asIdeal → ∀ z ∈ intV D v, ∃ a ∈ v.adicCompletionIntegers D.host.F,
      ∃ b ∈ v.adicCompletionIntegers D.host.F, z = a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w := by
  intro D v w t n ht hn hv z hz
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hcoe : ∀ r : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r :
      v.adicCompletionIntegers D.host.F) : Fv D.host.F v) = algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) :=
    fun r => rfl
  have hmem : ∀ r : 𝓞 D.host.F, algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈
      v.adicCompletionIntegers D.host.F := fun r => hcoe r ▸ (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) r).2
  obtain ⟨u, hu⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (t ^ 2 - 4 * n)).2 hv).exists_left_inv
  set U : Fv D.host.F v := ((u : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) with hU
  have hu' : U * algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 1 := by
    have := congrArg (fun y : v.adicCompletionIntegers D.host.F => (y : Fv D.host.F v)) hu
    rw [MulMemClass.coe_mul, hcoe, OneMemClass.coe_one] at this
    exact this
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, rfl⟩ := hy
    obtain ⟨a, b, hab⟩ := exists_coords hcm w t n ht hn x
    refine ⟨c * U * algebraMap D.host.F (Fv D.host.F v) (a : D.host.F), mul_mem (mul_mem hc u.2) (hmem a),
      c * U * algebraMap D.host.F (Fv D.host.F v) (b : D.host.F), mul_mem (mul_mem hc u.2) (hmem b), ?_⟩
    have hc' : c = algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U) := by
      rw [mul_comm, mul_assoc, hu', mul_one]
    calc c ⊗ₜ[D.host.F] (x : D.host.E)
        = (algebraMap D.host.F (Fv D.host.F v) ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * (c * U)) ⊗ₜ[D.host.F]
            (x : D.host.E) := by rw [← hc']
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) * x) :=
          tmul_move _ _ _
      _ = (c * U) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (a : D.host.F) * 1 +
            algebraMap D.host.F D.host.E (b : D.host.F) * w) := by rw [mul_comm (algebraMap D.host.F D.host.E _) (x : D.host.E), hab, mul_one]
      _ = (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F) * (c * U)) ⊗ₜ[D.host.F] (1 : D.host.E) +
            (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F) * (c * U)) ⊗ₜ[D.host.F] w := by
          rw [TensorProduct.tmul_add, tmul_move, tmul_move]
      _ = _ := by rw [mul_comm (algebraMap D.host.F (Fv D.host.F v) (a : D.host.F)),
            mul_comm (algebraMap D.host.F (Fv D.host.F v) (b : D.host.F))]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ h h' =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨a', ha', b', hb', rfl⟩ := h'
    refine ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', ?_⟩
    exact coords_add a b a' b' w
  | neg y _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine ⟨-a, neg_mem ha, -b, neg_mem hb, ?_⟩
    exact coords_neg a b w

end GlobalTheory.FixedUnitNorm.Coords
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalIntegersTensorCoordsPrimeToDiscriminantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant : ∀ (D : D7) (v : Pl D) (w : D.host.E) (t n : 𝓞 D.host.F), w + D.sp.cm.sig w = algebraMap D.host.F D.host.E t → w * D.sp.cm.sig w = algebraMap D.host.F D.host.E n → t ^ 2 - 4 * n ∉ v.asIdeal → ∀ z ∈ intV D v, ∃ a ∈ v.adicCompletionIntegers D.host.F, ∃ b ∈ v.adicCompletionIntegers D.host.F, z = a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w := by
  first | exact @GlobalTheory.FixedUnitNorm.Coords.mem_intV_coords | exact GlobalTheory.FixedUnitNorm.Coords.mem_intV_coords | (intros; apply GlobalTheory.FixedUnitNorm.Coords.mem_intV_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace
open IsDedekindDomain NumberField GlobalTheory.FixedUnitNorm
open scoped TensorProduct

namespace GlobalTheory.FixedUnitNorm

set_option synthInstance.maxHeartbeats 200000 in
theorem compAt_cA (D : D7) (v : Pl D) (a : AE D) : compAt D v (cA D a) = sigV D v (compAt D v a) := by
  induction a using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), map_add (f := _), hx, hy]
  | tmul a m => rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem tmul_algebraMap (D : D7) (v : Pl D) (c : Fv D.host.F v) (f : D.host.F) :
    c ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E f) = (algebraMap D.host.F (Fv D.host.F v) f * c) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem fixed_unit_norm : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) →
    (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u →
    (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  intro D v ε hT _ _ _ hid u hu hcu ⟨y, hy, huy⟩
  obtain ⟨w, t, n, h1, h2, h3⟩ := GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem D.host.F D.host.E D.sp.cm.sig
    (GlobalTheory.AdelicU.isCMExt_host D) v (fun P hP => @hT.1 P.asIdeal P.isPrime hP)
  have hw : ∀ f : D.host.F, algebraMap D.host.F D.host.E f ≠ w := by
    intro f hf
    apply h3
    have hs : D.sp.cm.sig w = w := by rw [← hf, AlgHom.commutes]
    have e : algebraMap D.host.F D.host.E ((t : D.host.F) ^ 2 - 4 * n) = 0 := by
      rw [map_sub, map_pow, map_mul, ← h1, ← h2, hs, map_ofNat]; ring
    have e2 : ((t ^ 2 - 4 * n : 𝓞 D.host.F) : D.host.F) = 0 := by
      have := (FaithfulSMul.algebraMap_injective D.host.F D.host.E) (e.trans (map_zero _).symm)
      push_cast; exact this
    have e3 : t ^ 2 - 4 * n = 0 := RingOfIntegers.coe_eq_zero_iff.1 e2
    rw [e3]; exact v.asIdeal.zero_mem
  obtain ⟨W, hW⟩ := GlobalTheory.T.exists_integer_of_relative_trace_norm_integral D w t n h1 h2

  have hone : (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intV D v :=
    AddSubgroup.subset_closure ⟨1, (v.adicCompletionIntegers D.host.F).one_mem, 1, by simp [Algebra.TensorProduct.one_def]⟩
  have hε1 : compAt D v ε = 1 := by
    obtain ⟨z, hz, hz1⟩ := GlobalTheory.T.exists_integralAdele_atPlace_with_component D v 1 hone
    have h := congrArg (compAt D v) ((hid z).1 hz.1)
    rwa [RingHom.map_mul, hz1, mul_one] at h

  obtain ⟨a, ha, b, hb, hU⟩ := GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant D v w t n h1 h2 h3 _ (GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor D v u hu)
  have hsig : sigV D v (compAt D v u) = compAt D v u := by rw [← compAt_cA, hcu]
  have hsw : D.sp.cm.sig w = algebraMap D.host.F D.host.E t - w := by rw [← h1]; ring
  have hb0 : b = 0 := by
    have e : sigV D v (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) -
        (a ⊗ₜ[D.host.F] (1 : D.host.E) + b ⊗ₜ[D.host.F] w) = 0 := by rw [← hU, hsig, sub_self]
    have e' : (algebraMap D.host.F (Fv D.host.F v) t * b) ⊗ₜ[D.host.F] (1 : D.host.E) + (-(2 * b)) ⊗ₜ[D.host.F] w = 0 := by
      rw [← e, sigV, map_add (f := _), Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply,
        map_one, hsw, TensorProduct.tmul_sub, tmul_algebraMap, TensorProduct.neg_tmul]
      rw [show (2 : Fv D.host.F v) * b = b + b by ring, TensorProduct.add_tmul]
      abel
    have := (GlobalTheory.T.completion_tensor_relativeBasis_coords_unique D v w hw _ _ e').2
    have h2b : (2 : Fv D.host.F v) * b = 0 := neg_eq_zero.1 this
    have h2ne : (2 : Fv D.host.F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := D.host.F)
      apply (algebraMap D.host.F (Fv D.host.F v)).injective
      rw [map_ofNat, map_zero]; exact h
    exact (mul_eq_zero.1 h2b).resolve_left h2ne
  rw [hb0, TensorProduct.zero_tmul, add_zero] at hU
  obtain ⟨a', ha', b', hb', hY⟩ := GlobalTheory.T.localIntegers_tensor_coords_prime_to_discriminant D v w t n h1 h2 h3 _ (GlobalTheory.T.adeleComponentAtFinitePlace_integral_mem_localTensor D v y hy)
  have haa : a * a' = 1 := by
    have e : compAt D v u * compAt D v y = 1 := by rw [← RingHom.map_mul, huy, hε1]
    rw [hU, hY, mul_add, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul] at e
    have e' : (a * a' - 1) ⊗ₜ[D.host.F] (1 : D.host.E) + (a * b') ⊗ₜ[D.host.F] w = 0 := by
      rw [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def, ← e]; abel
    exact sub_eq_zero.1 (GlobalTheory.T.completion_tensor_relativeBasis_coords_unique D v w hw _ _ e').1
  let A : v.adicCompletionIntegers D.host.F := ⟨a, ha⟩
  have hAu : IsUnit A := ⟨⟨A, ⟨a', ha'⟩, Subtype.ext haa, Subtype.ext (by rw [mul_comm]; exact haa)⟩, rfl⟩
  have hD : IsUnit (algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) t ^ 2 -
      4 * algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) n) := by
    have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 h3
    rwa [map_sub, map_pow, map_mul, map_ofNat] at this
  obtain ⟨r, s, hrs⟩ := GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit D.host.F v _ _ A hD hAu

  set x' : Fv D.host.F v ⊗[D.host.F] D.host.E := (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] w
  have hx'i : x' ∈ intV D v := by
    refine AddSubgroup.add_mem _ (AddSubgroup.subset_closure ⟨r, r.2, 1, by simp⟩)
      (AddSubgroup.subset_closure ⟨s, s.2, W, by rw [hW]⟩)
  have hcoe : ∀ c : 𝓞 D.host.F, ((algebraMap (𝓞 D.host.F) (v.adicCompletionIntegers D.host.F) c : v.adicCompletionIntegers D.host.F) : Fv D.host.F v) =
      algebraMap D.host.F (Fv D.host.F v) c := fun c => rfl
  have hnorm : x' * sigV D v x' = compAt D v u := by
    have hrs' : (r : Fv D.host.F v) ^ 2 + algebraMap D.host.F (Fv D.host.F v) t * r * s +
        algebraMap D.host.F (Fv D.host.F v) n * (s : Fv D.host.F v) ^ 2 = a := by
      have := congrArg (fun q : v.adicCompletionIntegers D.host.F => (q : Fv D.host.F v)) hrs
      exact this
    have e1 : sigV D v x' = (r : Fv D.host.F v) ⊗ₜ[D.host.F] (1 : D.host.E) + (s : Fv D.host.F v) ⊗ₜ[D.host.F] D.sp.cm.sig w := by
      simp only [x', sigV, map_add (f := _), Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rw [e1, hU]
    simp only [x', add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have e2 : ((s : Fv D.host.F v) * r) ⊗ₜ[D.host.F] w = ((r : Fv D.host.F v) * s) ⊗ₜ[D.host.F] w := by rw [mul_comm]
    rw [e2, h2, tmul_algebraMap, hsw, TensorProduct.tmul_sub, tmul_algebraMap]
    have key : ∀ P Q R S : Fv D.host.F v ⊗[D.host.F] D.host.E, P + S + (Q - S + R) = P + Q + R := fun P Q R S => by abel
    rw [key, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    rw [← hrs']; ring
  obtain ⟨x, hxi, hxc⟩ := GlobalTheory.T.exists_integralAdele_atPlace_with_component D v x' hx'i
  refine ⟨x, hxi, ?_⟩
  have hx0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ x).1 hxi.1
  have hu0 := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ u).1 hu.1
  rw [← sub_eq_zero]
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_sub, RingHom.map_mul, hx0.1, zero_mul, hu0.1, sub_zero]
  · intro w'
    by_cases hw' : w' = v
    · subst hw'; rw [RingHom.map_sub, RingHom.map_mul, compAt_cA, hxc, hnorm, sub_self]
    · rw [RingHom.map_sub, RingHom.map_mul, hx0.2 w' hw', zero_mul, hu0.2 w' hw', sub_zero]

end GlobalTheory.FixedUnitNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOfConjFixedUnitTamePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → ∀ u ∈ intAt D (· = v), cA D u = u → (∃ y ∈ intAt D (· = v), u * y = ε) → ∃ x ∈ intAt D (· = v), x * cA D x = u := by
  first | exact @GlobalTheory.FixedUnitNorm.fixed_unit_norm | exact GlobalTheory.FixedUnitNorm.fixed_unit_norm | (intros; apply GlobalTheory.FixedUnitNorm.fixed_unit_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.UnimodNF

section Abstract

variable {A : Type*} [CommRing A] {ε : A} (hid : IsIdempotentElem ε) (O : Set A)
  (h0 : (0 : A) ∈ O) (hadd : ∀ a ∈ O, ∀ b ∈ O, a + b ∈ O) (hneg : ∀ a ∈ O, -a ∈ O)
  (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hεO : ε ∈ O)

def sub : Subring hid.Corner where
  carrier := {x | x.1 ∈ O}
  zero_mem' := h0
  add_mem' {x y} hx hy := hadd _ hx _ hy
  neg_mem' {x} hx := hneg _ hx
  mul_mem' {x y} hx hy := hmul _ hx _ hy
  one_mem' := hεO


include hid h0 hadd hneg hmul hεO in
theorem exists_congr_one (c : A →+* A) (hc : ∀ x, c (c x) = x) (hcO : ∀ a ∈ O, c a ∈ O) (hcε : c ε = ε)
    (hεa : ∀ a ∈ O, ε * a = a)
    (hloc : ∀ x ∈ O, c x = x → (∃ y ∈ O, x * y = ε) ∨ (∃ y ∈ O, (ε - x) * y = ε))
    (hw : ∃ w ∈ O, w + c w = ε)
    (hnorm : ∀ u ∈ O, c u = u → (∃ y ∈ O, u * y = ε) → ∃ x ∈ O, x * c x = u)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) A) (hH : ∀ i j, H i j ∈ O) (hherm : ∀ i j, c (H i j) = H j i)
    (hinv : ∃ H' : Matrix (Fin n) (Fin n) A, (∀ i j, H' i j ∈ O) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) A)) :
    ∃ P P' : Matrix (Fin n) (Fin n) A, (∀ i j, P i j ∈ O) ∧ (∀ i j, P' i j ∈ O) ∧
      P * P' = ε • (1 : Matrix (Fin n) (Fin n) A) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) A) ∧
      (P.map c)ᵀ * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) A) := by
  classical
  let R := sub hid O h0 hadd hneg hmul hεO
  have corner_mem : ∀ a ∈ O, a ∈ Subsemigroup.corner ε := fun a ha =>
    (Subsemigroup.mem_corner_iff hid).2 ⟨hεa a ha, by rw [mul_comm]; exact hεa a ha⟩
  let mk : ∀ a, a ∈ O → R := fun a ha => ⟨⟨a, corner_mem a ha⟩, ha⟩
  let val : R →+ A := { toFun := fun x => x.1.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have val_mem : ∀ x : R, val x ∈ O := fun x => x.2
  have val_inj : ∀ x y : R, val x = val y → x = y := fun x y h => Subtype.ext (Subtype.ext h)
  let c' : R →+* R :=
    { toFun := fun x => mk (c (val x)) (hcO _ (val_mem x))
      map_one' := val_inj _ _ (show c ε = ε from hcε)
      map_mul' := fun x y => val_inj _ _ (show c (val x * val y) = c (val x) * c (val y) from map_mul c _ _)
      map_zero' := val_inj _ _ (show c 0 = 0 from map_zero c)
      map_add' := fun x y => val_inj _ _ (show c (val x + val y) = c (val x) + c (val y) from map_add c _ _) }
  have hc' : ∀ x, c' (c' x) = x := fun x => val_inj _ _ (show c (c (val x)) = val x from hc _)
  have map_mul_val : ∀ X Y : Matrix (Fin n) (Fin n) R, (X * Y).map val = X.map val * Y.map val := by
    intro X Y
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, map_sum]
    rfl
  have map_one_val : (1 : Matrix (Fin n) (Fin n) R).map val = ε • (1 : Matrix (Fin n) (Fin n) A) := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · simp only [smul_eq_mul, mul_one]; rfl
    · simp only [smul_eq_mul, mul_zero, map_zero]
  have map_inj : ∀ X Y : Matrix (Fin n) (Fin n) R, X.map val = Y.map val → X = Y := fun X Y h =>
    Matrix.ext fun i j => val_inj _ _ (congrFun (congrFun h i) j)
  let G : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H i j) (hH i j)
  have hGH : G.map val = H := by ext i j; rfl
  obtain ⟨H', hH'O, hHH'⟩ := hinv
  let G' : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => mk (H' i j) (hH'O i j)
  have hG'H : G'.map val = H' := by ext i j; rfl
  have hGG' : G * G' = 1 := map_inj _ _ (by rw [map_mul_val, map_one_val, hGH, hG'H]; exact hHH')
  have hdet : IsUnit G.det := Matrix.isUnit_det_of_right_inverse hGG'
  have hG : ∀ a b, c' (G a b) = G b a := fun a b => val_inj _ _ (hherm a b)
  have hlocR : ∀ x : R, c' x = x → IsUnit x ∨ IsUnit (1 - x) := by
    intro x hx
    have hx' : c (val x) = val x := congrArg val hx
    rcases hloc (val x) (val_mem x) hx' with ⟨y, hy, hxy⟩ | ⟨y, hy, hxy⟩
    · exact Or.inl (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
    · exact Or.inr (isUnit_iff_exists_inv.2 ⟨mk y hy, val_inj _ _ hxy⟩)
  have hwR : ∃ w : R, w + c' w = 1 := by
    obtain ⟨w, hw, hw'⟩ := hw
    exact ⟨mk w hw, val_inj _ _ hw'⟩
  have hnormR : ∀ u : R, c' u = u → IsUnit u → ∃ x, x * c' x = u := by
    intro u hu hu'
    obtain ⟨y, hy⟩ := hu'.exists_right_inv
    obtain ⟨x, hx, hx'⟩ := hnorm (val u) (val_mem u) (congrArg val hu) ⟨val y, val_mem y, congrArg val hy⟩
    exact ⟨mk x hx, val_inj _ _ hx'⟩
  obtain ⟨Q, hQ, hGQ⟩ :=
    GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map_of_isUnit_or c' hc' hlocR hwR hnormR hG hdet
  have hmap1 : (1 : Matrix (Fin n) (Fin n) R).map c' = 1 := Matrix.map_one _ (map_zero c') (map_one c')
  refine ⟨((Q⁻¹).map c').map val, (Q.map c').map val, fun i j => val_mem _, fun i j => val_mem _, ?_, ?_, ?_⟩
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.nonsing_inv_mul Q hQ, hmap1, map_one_val]
  · rw [← map_mul_val, ← Matrix.map_mul, Matrix.mul_nonsing_inv Q hQ, hmap1, map_one_val]
  · have e1 : (((Q⁻¹).map c').map val).map c = (Q⁻¹).map val := by
      ext i j
      exact congrArg val (hc' (Q⁻¹ i j))
    rw [e1, ← Matrix.transpose_map, ← hGH, ← map_mul_val, ← map_mul_val, ← map_one_val]
    congr 1
    have h1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
    rw [hGQ]
    calc (Q⁻¹)ᵀ * (Qᵀ * Q.map c' * (Q⁻¹).map c') = (Q * Q⁻¹)ᵀ * (Q * Q⁻¹).map c' := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.transpose_one, hmap1, Matrix.one_mul]

end Abstract

set_option synthInstance.maxHeartbeats 400000

variable {D : D7}

theorem intAt_zero' (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P := ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_neg' {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem cA_mem_intAt' {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) :=
  ⟨GlobalTheory.FinPl.RootKeep.conj_mem_idAt ha.1, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩

theorem unimodular_congr_one : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  intro D v ε n H htame hεε hεc hεI hε hHI hherm hinv
  exact exists_congr_one (hid := hεε) (O := intAt D (· = v)) (intAt_zero' _)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_add ha hb) (fun a ha => intAt_neg' ha)
    (fun a ha b hb => GlobalTheory.IwaPlace.SdComap.intAt_mul ha hb) hεI (cA D) (fun z => Formalism.L2.Theta.cA_cA z)
    (fun a ha => cA_mem_intAt' ha) hεc (fun a ha => (hε a).1 ha.1)
    (GlobalTheory.T.conjFixed_integral_isUnit_or_idem_sub_unit D v ε htame hεε hεc hεI hε)
    (GlobalTheory.IwaPlace.exists_trace_one_at_tame D v ε hεε hεc hεI hε htame)
    (GlobalTheory.T.exists_norm_of_conjFixed_unit_tamePlace D v ε htame hεε hεc hεI hε) H hHI hherm hinv

end GlobalTheory.IwaPlace.UnimodNF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnimodularHermitianCongrOneAtTamePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_hermitian_congr_one_at_tamePlace : ∀ (D : D7) (v : Pl D) (ε : AE D) (n : ℕ) (H : Matrix (Fin n) (Fin n) (AE D)), Tame D v → ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → (∀ i j, H i j ∈ intAt D (· = v)) → (∀ i j, cA D (H i j) = H j i) → (∃ H' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ H * H' = ε • (1 : Matrix (Fin n) (Fin n) (AE D))) → ∃ P P' : Matrix (Fin n) (Fin n) (AE D), (∀ i j, P i j ∈ intAt D (· = v)) ∧ (∀ i j, P' i j ∈ intAt D (· = v)) ∧ P * P' = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ P' * P = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) ∧ adj P * (H * P) = ε • (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | exact GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one | (intros; apply GlobalTheory.IwaPlace.UnimodNF.unimodular_congr_one <;> assumption)
end
