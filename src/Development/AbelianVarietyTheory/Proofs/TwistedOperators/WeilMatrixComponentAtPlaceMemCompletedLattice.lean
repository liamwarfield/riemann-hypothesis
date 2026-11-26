module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatticeLocal

section
variable (F : Type) [Field F] [NumberField F]

theorem ev_self (v : HeightOneSpectrum (𝓞 F)) : evalV F v (singleV F v 1) = 1 := by
  classical
  show (singleV F v 1 : Af F) v = 1
  unfold singleV
  exact RestrictedProduct.single_eq_same _ v 1

theorem ev_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : evalV F w (singleV F v 1) = 0 := by
  classical
  show (singleV F v 1 : Af F) w = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ 1 h

theorem af_ext {α β : Af F} (h : ∀ w, evalV F w α = evalV F w β) : α = β := by
  apply RestrictedProduct.ext
  intro w
  exact h w

end

variable {D : D7}

theorem idem_inl_mul (v : FinPl D) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inl v) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] m := by
  have key : pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 α =
      pairA D.host.F 0 (singleV D.host.F v 1 * α) := Prod.ext (mul_zero _) rfl
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, key]

theorem idem_inr_mul (τ : D.what₂.Tau) (α : Af D.host.F) (m : D.host.E) :
    idem D (.inr τ) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] m) = 0 := by
  have key : pairA D.host.F (GlobalTheory.AutFunCompare.sgW (plTau D τ) 1) 0 * pairA D.host.F 0 α = 0 :=
    Prod.ext (mul_zero _) (zero_mul _)
  simp only [idem, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, key, TensorProduct.zero_tmul]

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  ext i j
  simp [wAt, mul_add]

theorem wAt_neg {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (-x) = -wAt p x := by
  ext i j
  simp [wAt]

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  ext i j
  simp [wAt]

theorem wAt_mem_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  intro D S T ΛS ΛT P u hu p
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hv, a, ha, s, hs, t, ht, hw⟩ := hw

    obtain ⟨X, hX⟩ : ∃ X : Fin T.rank → Fin S.rank → D.host.E,
        X = fun i j => a * t i * ∑ k, star (s k) * S.gram k j := ⟨_, rfl⟩

    have gen : ∀ (Q : FinPl D → Prop) (β : Af D.host.F), β ∈ intAf D.host.F →
        (∀ v, ¬ Q v → evalV D.host.F v β = 0) →
        (Matrix.of fun i j => pairA D.host.F 0 β ⊗ₜ[D.host.F] X i j) ∈ latO S T ΛS ΛT Q := by
      intro Q β hβ hQ
      unfold latO
      refine AddSubgroup.subset_closure ?_
      simp only [Set.mem_setOf_eq]
      exact ⟨β, hβ, hQ, a, ha, s, hs, t, ht, by subst hX; rfl⟩
    have hw' : w = Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j := by
      subst hX
      exact hw
    subst hw'
    rcases p with v | τ
    ·
      have hs1 : ∀ v', evalV D.host.F v' (singleV D.host.F v 1) ∈ v'.adicCompletionIntegers D.host.F := by
        intro v'
        by_cases h : v' = v
        · rw [h, ev_self]
          exact one_mem _
        · rw [ev_ne _ h]
          exact zero_mem _
      have e1 : wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        ext i j
        simp only [wAt, Matrix.of_apply, idem_inl_mul]
      have e2 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) -
            wAt (.inl v) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) =
          Matrix.of fun i j => pairA D.host.F 0 (α - singleV D.host.F v 1 * α) ⊗ₜ[D.host.F] X i j := by
        rw [e1]
        ext i j
        simp only [Matrix.sub_apply, Matrix.of_apply, ← TensorProduct.sub_tmul]
        congr 1
        exact Prod.ext (sub_self _) rfl
      refine ⟨?_, ?_, fun hp => ?_⟩
      · rw [e1]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_mul]
          exact mul_mem (hs1 v') (hα v')
        · by_cases h : v' = v
          · rw [h] at hv' ⊢
            have hPv : ¬ P v := fun hP => hv' ⟨hP, rfl⟩
            rw [map_mul, hv v hPv, mul_zero]
          · rw [map_mul, ev_ne _ h, zero_mul]
      · rw [e2]
        refine gen _ _ (fun v' => ?_) (fun v' hv' => ?_)
        · rw [map_sub, map_mul]
          exact sub_mem (hα v') (mul_mem (hs1 v') (hα v'))
        · by_cases h : v' = v
          · rw [h, map_sub, map_mul, ev_self, one_mul, sub_self]
          · have hPv : ¬ P v' := fun hP => hv' ⟨hP, fun e => h (Sum.inl_injective e)⟩
            rw [map_sub, map_mul, hv v' hPv, mul_zero, sub_zero]
      · have hPv : ¬ P v := fun hP => hp v hP rfl
        have h0 : singleV D.host.F v 1 * α = 0 := by
          apply af_ext
          intro v'
          by_cases h : v' = v
          · rw [h, map_mul, hv v hPv, mul_zero, map_zero]
          · rw [map_mul, ev_ne _ h, zero_mul, map_zero]
        rw [e1, h0]
        ext i j
        simp only [Matrix.of_apply, Matrix.zero_apply]
        rw [show pairA D.host.F 0 0 = 0 from Prod.ext rfl rfl, TensorProduct.zero_tmul]
    ·
      have e0 : wAt (.inr τ) (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] X i j) = 0 := by
        ext i j
        simp only [wAt, Matrix.of_apply, Matrix.zero_apply, idem_inr_mul]
      refine ⟨?_, ?_, fun _ => e0⟩
      · rw [e0]
        exact zero_mem _
      · rw [e0, sub_zero]
        exact gen _ _ hα (fun v' hv' => hv v' (fun hP => hv' ⟨hP, Sum.inl_ne_inr⟩))
  | zero =>
    rw [wAt_zero, sub_zero]
    exact ⟨zero_mem _, zero_mem _, fun _ => rfl⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨hx1, hx2, hx3⟩ := ihx
    obtain ⟨hy1, hy2, hy3⟩ := ihy
    rw [wAt_add]
    refine ⟨add_mem hx1 hy1, ?_, fun hp => by rw [hx3 hp, hy3 hp, add_zero]⟩
    rw [add_sub_add_comm]
    exact add_mem hx2 hy2
  | neg x _ ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [wAt_neg]
    refine ⟨neg_mem h1, ?_, fun hp => by rw [h3 hp, neg_zero]⟩
    rw [neg_sub_neg, ← neg_sub]
    exact neg_mem h2

end GlobalTheory.LatticeLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixComponentAtPlaceMemCompletedLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : FinPl D → Prop) (u : WO S T), u ∈ latO S T ΛS ΛT P → ∀ p : Place D, wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v = p) ∧ u - wAt p u ∈ (latO S T ΛS ΛT fun v => P v ∧ Sum.inl v ≠ p) ∧ ((∀ v, P v → Sum.inl v ≠ p) → wAt p u = 0) := by
  first | exact @GlobalTheory.LatticeLocal.wAt_mem_latO | exact GlobalTheory.LatticeLocal.wAt_mem_latO | (intros; apply GlobalTheory.LatticeLocal.wAt_mem_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuArtin

theorem addEquivAddHaarChar_mulVecCE (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] :
    IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)]
      [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det),
      addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  intro hA hR κ _ _ inst hB M hM
  have heq : inst = MeasurableSpace.pi := by
    exact hB.measurable_eq.trans (@BorelSpace.measurable_eq (κ → B) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst heq
  set ν : Measure B := Measure.addHaar
  set μ : Measure (κ → B) := Measure.pi fun _ : κ => ν
  have h1 := addEquivAddHaarChar_smul_map μ (mulVecCE M hM)
  have h2 : (modu B M.det : ℝ≥0∞) • Measure.map M.mulVec μ = μ :=
    GlobalTheory.GaugeEx.ModDet.smul_map_mulVec_pi ν M hM
  have hfun : ⇑(mulVecCE M hM) = M.mulVec := funext fun x => mulVecCE_apply M hM x
  rw [hfun] at h1
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (κ → B)))
  have hpos : μ K ≠ 0 := ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
    (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  set m := (Measure.map M.mulVec μ) (K : Set (κ → B))
  have e1 : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h1]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have e2 : (modu B M.det : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h2]
    rw [Measure.smul_apply, smul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hpos e1.symm
  have hmt : m ≠ ⊤ := by
    intro h
    rw [h] at e1
    have hc : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (addEquivAddHaarChar_pos (mulVecCE M hM)).ne'
    rw [ENNReal.mul_top hc] at e1
    exact hfin e1.symm
  have := (ENNReal.mul_left_inj hm0 hmt).1 (e1.trans e2.symm)
  exact_mod_cast this

end GlobalTheory.ModuArtin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReducedStatement
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_mulVec_artinian_reduced : ∀ (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B], IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)] [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det), addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  first | exact @GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | exact GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE | (intros; apply GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct Pointwise

namespace GlobalTheory.ModuPiLocal

theorem distribHaarChar_pi {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, T2Space (A i)] [∀ i, SecondCountableTopology (A i)] (u : (∀ i, A i)ˣ) :
    distribHaarChar (∀ i, A i) u = ∏ i, distribHaarChar (A i) (Units.map (Pi.evalRingHom A i).toMonoidHom u) := by
  classical
  letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)
  haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩
  let μ : ∀ i, Measure (A i) := fun i => Measure.addHaar
  let S : ∀ i, TopologicalSpace.PositiveCompacts (A i) := fun i => Classical.choice inferInstance
  have h0 : ∀ i, μ i (S i : Set (A i)) ≠ 0 := fun i =>
    (Measure.measure_pos_of_nonempty_interior (μ i) (S i).interior_nonempty).ne'
  have h1 : ∀ i, μ i (S i : Set (A i)) ≠ ⊤ := fun i => (S i).isCompact.measure_lt_top.ne
  have hp : ∀ T : ∀ i, Set (A i), (Measure.pi μ) (Set.univ.pi T) = ∏ i, μ i (T i) := fun T =>
    Measure.pi_pi _ _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := Set.univ.pi fun i => (S i : Set (A i)))
    (by rw [hp]; exact Finset.prod_ne_zero_iff.2 fun i _ => h0 i)
    (by rw [hp]; exact ENNReal.prod_ne_top fun i _ => h1 i) ?_
  have e : u • (Set.univ.pi fun i => (S i : Set (A i))) =
      Set.univ.pi fun i => Units.map (Pi.evalRingHom A i).toMonoidHom u • (S i : Set (A i)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [← map_inv]
    rfl
  rw [e, hp, hp]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [distribHaarChar_mul]

end GlobalTheory.ModuPiLocal

namespace GlobalTheory.ModuPiLocal

theorem modu_sPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  intro F _ _ S x hx
  rw [modu, dite_eq_left hx, distribHaarChar_pi (fun v : S => Fv F v.1), NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : IsUnit (x v) := (Pi.isUnit_iff.1 hx) v
  have h := GlobalTheory.GaugeProdFormula.modu_finite F v.1 (x v) hv.ne_zero
  rw [modu, dite_eq_left hv] at h
  rw [← h]
  congr 2
  ext
  rfl

end GlobalTheory.ModuPiLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNormStatement
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarModulusOfUnit_completionsAtPlaces_eq_prod_norm : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  first | exact @GlobalTheory.ModuPiLocal.modu_sPart | exact GlobalTheory.ModuPiLocal.modu_sPart | (intros; apply GlobalTheory.ModuPiLocal.modu_sPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitPrimeAvoiding
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardEqNcardPrimesOver
section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers

section Unip

variable {A : Type} [CommRing A] {n : ℕ}

def stabAdd (M : AddSubgroup (Fin n → A)) : Subgroup (GL (Fin n) A) where
  carrier := {g | ∀ v, v ∈ M ↔ (g : Matrix (Fin n) (Fin n) A) *ᵥ v ∈ M}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb x).trans (ha _)
  inv_mem' := by
    intro g hg x
    have := hg (((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm

def unip (M M' : AddSubgroup (Fin n → A)) : Subgroup (GL (Fin n) A) where
  carrier := {g | g ∈ stabAdd M ∧ g ∈ stabAdd M' ∧
    ∀ v ∈ M, (g : Matrix (Fin n) (Fin n) A) *ᵥ v - v ∈ M'}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨Subgroup.mul_mem _ ha1 hb1, Subgroup.mul_mem _ ha2 hb2, fun v hv => ?_⟩
    have h := M'.add_mem (ha3 _ ((hb1 v).1 hv)) (hb3 v hv)
    simpa only [Units.val_mul, ← Matrix.mulVec_mulVec, sub_add_sub_cancel] using h
  inv_mem' := by
    rintro g ⟨h1, h2, h3⟩
    refine ⟨Subgroup.inv_mem _ h1, Subgroup.inv_mem _ h2, fun v hv => ?_⟩
    have h := M'.neg_mem (h3 _ ((Subgroup.inv_mem _ h1 v).1 hv))
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub] at h
    exact h

end Unip

section Groups

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {n r : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

end Groups

section Lattices

variable {E : Type} [Field E] [NumberField E] {n r : ℕ}

def SplitsCompletely (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  Nat.card {w : HeightOneSpectrum (𝓞 E) // (p : 𝓞 E) ∈ w.asIdeal} = Module.finrank ℚ E

def gammaOne (SG : Finset (HeightOneSpectrum (𝓞 E))) (k : ℕ) : ℝ≥0∞ :=
  ∏ w ∈ SG, (Nat.card (GL (Fin k) (𝓞 E ⧸ w.asIdeal)) : ℝ≥0∞) /
    (Nat.card (Formalism.L2.Col.HU (𝓞 E ⧸ w.asIdeal) k) : ℝ≥0∞)

end Lattices

section Levels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (σ : E →ₐ[F] E) {n r k : ℕ} (J : Matrix (Fin n) (Fin n) E)


variable (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
  (L : Submodule (𝓞 E) (Fin n → E)) (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (ε : HeightOneSpectrum (𝓞 E) → Fin k → Fin n → E)

end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.SplitResidue

theorem card_eq_ncard_primesOver (E : Type) [Field E] [NumberField E] {g : ℕ} (hg : g.Prime) :
    Nat.card {w : HeightOneSpectrum (𝓞 E) // (g : 𝓞 E) ∈ w.asIdeal} =
      (Ideal.primesOver (Ideal.span {(g : ℤ)}) (𝓞 E)).ncard := by
  have hp : Prime (g : ℤ) := Nat.prime_iff_prime_int.mp hg
  haveI : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hne : (Ideal.span {(g : ℤ)}) ≠ ⊥ := by simpa using hg.ne_zero
  haveI hmax : (Ideal.span {(g : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨w.1.asIdeal, w.1.isPrime, ?_⟩) ⟨?_, ?_⟩)
  · haveI := w.1.isPrime
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using w.2
  · intro a b h
    exact Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro ⟨P, hP, hPl⟩
    refine ⟨⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_⟩, rfl⟩
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(g : ℤ)}) (g : ℤ)).1
      (Ideal.mem_span_singleton_self _)

theorem residue_and_unramified : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely E g →
    ∀ w : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ w.asIdeal →
      Nonempty ((𝓞 E ⧸ w.asIdeal) ≃+* ZMod g) ∧ (g : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro E _ _ g hg h w hw
  haveI := w.isPrime
  haveI := Fact.mk hg
  have h' := (card_eq_ncard_primesOver E hg).symm.trans h
  obtain ⟨h1, h2⟩ := GlobalTheory.LocSplit.split_prime hg h' w.asIdeal hw
  refine ⟨?_, h1⟩
  haveI : Nontrivial (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
  haveI : CharP (𝓞 E ⧸ w.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hg, ← map_natCast (Ideal.Quotient.mk w.asIdeal),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  refine ⟨(RingEquiv.ofBijective (ZMod.castHom (dvd_refl g) (𝓞 E ⧸ w.asIdeal))
    ⟨ZMod.castHom_injective _, fun y => ?_⟩).symm⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨m, hm⟩ := h2 x
  refine ⟨(m : ZMod g), ?_⟩
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq]
  exact hm

end GlobalTheory.SplitResidue
end

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitChoice

theorem exists_place_over (K : Type) [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  have hm : ((p : ℕ) : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun h0 => ?_⟩, hm⟩
  rw [h0, Ideal.mem_bot] at hm
  exact hp.ne_zero (by exact_mod_cast hm)

theorem natCast_notMem_of_absNorm_lt {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p : ℕ}
    (hp : p.Prime) (h : Ideal.absNorm v.asIdeal < p) : (p : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have hcop : Nat.Coprime p (Ideal.absNorm v.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd) (by omega)
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at hab
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _))))

theorem splitsCompletely_of_modEq_one (D : D7) {p : ℕ} (hp : p.Prime)
    (hc : p ≡ 1 [MOD D.host.QS * D.host.q * D.host.d]) : SplitsCompletely D p := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have hs : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely D.host.E p := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentStabilizers.SplitsCompletely
    rw [GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp, ← GlobalTheory.HostSplit.ncard_placesOver D.host.E hp, h1]
  refine ⟨hp, fun w hw => ⟨h3 w hw, ?_⟩⟩
  haveI := w.isPrime
  have hs' := (GlobalTheory.SplitResidue.card_eq_ncard_primesOver D.host.E hp).symm.trans hs
  exact (GlobalTheory.LocSplit.split_prime hp hs' w.asIdeal hw).1

theorem exists_split_prime : ∀ (D : D7) (S : Set (HeightOneSpectrum (𝓞 D.host.F))) (N : ℕ), S.Finite → N ≠ 0 →
    ∃ p : ℕ, SplitsCompletely D p ∧ p.Coprime N ∧ (∀ v ∈ S, (p : 𝓞 D.host.F) ∉ v.asIdeal) ∧
      ∃ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  intro D S N hS hN
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one
    (N + ∑ v ∈ hS.toFinset, Ideal.absNorm v.asIdeal) hm
  refine ⟨p, splitsCompletely_of_modEq_one D hp hc, ?_, fun v hv => ?_, exists_place_over _ hp⟩
  · refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdv => ?_
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdv
    omega
  · refine natCast_notMem_of_absNorm_lt v hp ?_
    have := Finset.single_le_sum (f := fun v : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm v.asIdeal)
      (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.2 hv)
    omega

end GlobalTheory.SplitChoice
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterEquivalenceLocalData
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.ChrTie

theorem unrAt_iff_and_val_eq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (UnrAt c w ↔ χ.UnrAt w) ∧ val c w = χ.val w :=
  fun _ _ _ h w => ⟨GlobalTheory.LFun.unrAt_iff_of_chrEq h w, GlobalTheory.LFun.val_eq_of_chrEq h w⟩

end GlobalTheory.ChrTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


open Classical in
def gLoc {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (PP : Formalism.L2.DIV.Pl D.host.E)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero a y ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ H then
    ((c ⟨Formalism.L2.DIV.upperLeftBlock L.hr h.2.choose, h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ i ∈ Finset.range L.s,
        ((L.cg (i + 1) PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) h.2.choose) : ℂˣ) : ℂ)) *
      (((χ (Matrix.GeneralLinearGroup.det h.2.choose)) : ℂˣ) : ℂ)⁻¹
  else 0


open Classical in
def qLoc {a b : ℕ} (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero r y ∧ IsUnit (topL r y).det then ((ξ h.2.unit : ℂˣ) : ℂ) else 0

def IsRedMap {v : FinPl D} (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP) : Prop :=
  Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧
    (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧
    ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩


open Classical in
def viaRed {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ} (r : v.adicCompletionIntegers D.host.F →+* k)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) (Y : Matrix (Fin b) (Fin a) (Fv D.host.F v)) : ℂ :=
  if h : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F then ω (Matrix.of fun i j => r ⟨Y i j, h i j⟩) else 0


open Classical in
def locFn (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (PP : Formalism.L2.DIV.Pl D.host.E) (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) : WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then ω (redM PP (frMapO S T βS βT x)) else 0

end GlobalTheory.StepVec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrict
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory.HaarOpenEmb

theorem nnreal_smul_cancel {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [LocallyCompactSpace Y]
    (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ] [ρ.IsOpenPosMeasure] [Nonempty Y] {a b : ℝ≥0}
    (h : a • ρ = b • ρ) : a = b := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds y
  have h0 : ρ K ≠ 0 := (Measure.measure_pos_of_mem_nhds ρ hKn).ne'
  have hT : ρ K ≠ ∞ := hK.measure_lt_top.ne
  have e := congrArg (fun μ : Measure Y => μ K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
  exact_mod_cast (ENNReal.mul_left_inj h0 hT).1 e

theorem addEquivAddHaarChar_eq_of_isOpenEmbedding :
    ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  intro G G' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj e e' hcomm
  by_cases hne : Nonempty G'
  swap
  · have : IsEmpty G' := not_nonempty_iff.1 hne
    exact absurd ⟨0⟩ hne
  let μ : Measure G := Measure.addHaar
  let ν : Measure G' := μ.comap j
  haveI : ν.IsAddHaarMeasure := Measure.IsAddHaarMeasure.comap (mH := inferInstance) μ hj
  haveI : ν.Regular := inferInstance
  have hjm : ∀ s, MeasurableSet s → MeasurableSet ((j : G' → G) '' s) :=
    fun s hs => hj.measurableEmbedding.measurableSet_image' hs
  have hem : ∀ s, MeasurableSet s → MeasurableSet ((e : G → G) '' s) :=
    fun s hs => e.toHomeomorph.measurableEmbedding.measurableSet_image' hs
  have he'm : ∀ s, MeasurableSet s → MeasurableSet ((e' : G' → G') '' s) :=
    fun s hs => e'.toHomeomorph.measurableEmbedding.measurableSet_image' hs
  have h1 := addEquivAddHaarChar_smul_eq_comap μ e
  have h2 := addEquivAddHaarChar_smul_eq_comap ν e'
  have hfun : (e : G → G) ∘ (j : G' → G) = (j : G' → G) ∘ (e' : G' → G') := funext hcomm
  have key : addEquivAddHaarChar e • ν = addEquivAddHaarChar e' • ν := by
    rw [h2]
    change addEquivAddHaarChar e • μ.comap j = (μ.comap j).comap e'
    rw [Measure.comap_comap he'm hj.injective hjm, ← hfun,
      ← Measure.comap_comap hjm e.injective hem, ← h1]
    have hs : ∀ (c : ℝ≥0) (m : Measure G), c • m = (c : ℝ≥0∞) • m := fun c m => by
      ext s hs; rw [Measure.smul_apply, Measure.smul_apply]; rfl
    have hs' : ∀ (c : ℝ≥0) (m : Measure G'), c • m = (c : ℝ≥0∞) • m := fun c m => by
      ext s hs; rw [Measure.smul_apply, Measure.smul_apply]; rfl
    rw [hs, hs', Measure.comap_smul]
  exact nnreal_smul_cancel ν key

end GlobalTheory.HaarOpenEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharEqOfIsOpenEmbeddingRestrictStatement
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict : ∀ (G G' : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [T2Space G'] [SecondCountableTopology G'] [MeasurableSpace G'] [BorelSpace G'] (j : G' →+ G), IsOpenEmbedding j → ∀ (e : G ≃ₜ+ G) (e' : G' ≃ₜ+ G'), (∀ x, e (j x) = j (e' x)) → addEquivAddHaarChar e = addEquivAddHaarChar e' := by
  first | exact @GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | exact GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding | (intros; apply GlobalTheory.HaarOpenEmb.addEquivAddHaarChar_eq_of_isOpenEmbedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
open Classical MeasureTheory

noncomputable section

open MvPolynomial Matrix

namespace GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι]

def colMat {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) : Matrix (Var ι d a) (Var ι d a) ℂ :=
  fun w v => if w.1 = v.1 ∧ w.2.1 = v.2.1 then g v.1 w.2.2 v.2.2 else 0

theorem colSub_eq_lsub {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub g : Pol ι d a →ₐ[ℂ] Pol ι d a) = GlobalTheory.JointHarm.FMul.lsub (colMat g) := by
  refine algHom_ext fun v => ?_
  rw [GlobalTheory.JointHarm.FMul.lsub_X, colSub, aeval_X]
  obtain ⟨τ, r, c⟩ := v
  simp only [colMat, Fintype.sum_prod_type, ite_and, apply_ite C, map_zero, ite_mul, zero_mul]
  simp

theorem colMat_conjTranspose {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colMat (d := d) g)ᴴ = colMat fun τ => (g τ)ᴴ := by
  ext w v
  simp only [colMat, conjTranspose_apply]
  by_cases h : v.1 = w.1 ∧ v.2.1 = w.2.1
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩, h.1]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1.symm, h'.2.symm⟩, star_zero]

theorem colSub_comp {d a : ℕ} (h g : ι → Matrix (Fin a) (Fin a) ℂ) :
    (colSub h : Pol ι d a →ₐ[ℂ] Pol ι d a).comp (colSub g) = colSub fun τ => h τ * g τ := by
  refine algHom_ext fun v => ?_
  rw [AlgHom.comp_apply]
  unfold colSub
  set_option synthInstance.maxHeartbeats 100000 in
    rw [aeval_X, aeval_X, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem colSub_one {d a : ℕ} : (colSub (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) : Pol ι d a →ₐ[ℂ] Pol ι d a) =
    AlgHom.id ℂ _ := by
  refine algHom_ext fun v => ?_
  rw [colSub, aeval_X, Finset.sum_eq_single v.2.2]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne hb]
    simp
  · simp

theorem fockS_colSub_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ)
    (P Q : GlobalTheory.MinorFrame.Pol ι d a),
    Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
      (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  intro ι _ a d u P Q
  rw [← Formalism.L2.DIV.fockL_apply, ← Formalism.L2.DIV.fockL_apply, colSub_eq_lsub, GlobalTheory.JointHarm.FMul.fockL_lsub_adj,
    ← colSub_eq_lsub, colMat_conjTranspose, ← colSub_eq_lsub, ← AlgHom.comp_apply, colSub_comp]
  have hu : (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)ᴴ * (u τ : Matrix (Fin a) (Fin a) ℂ)) = fun _ => 1 := by
    funext τ
    exact Matrix.mem_unitaryGroup_iff'.1 (u τ).2
  rw [hu, colSub_one, AlgHom.id_apply]

end GlobalTheory.MinorFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitaryStatement
open Classical MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockS_fockColumnSubstitution_unitary : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (u : ι → Matrix.unitaryGroup (Fin a) ℂ) (P Q : GlobalTheory.MinorFrame.Pol ι d a),
  Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) P)
    (GlobalTheory.MinorFrame.colSub (fun τ => (u τ : Matrix (Fin a) (Fin a) ℂ)) Q) = Formalism.L2.DIV.fockS P Q := by
  first | exact @GlobalTheory.MinorFrame.fockS_colSub_unitary | exact GlobalTheory.MinorFrame.fockS_colSub_unitary | (intros; apply GlobalTheory.MinorFrame.fockS_colSub_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNorm
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

namespace GlobalTheory

theorem absE_eq_prod_norm_fstA_sndA (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ) :
    (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) *
      ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  have hf := GlobalTheory.Doubling.finite_mulSupport_absEv (F := F) (E := E) y
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  simp only [GlobalTheory.Doubling.absEw_unitInf] at *
  simp only [GlobalTheory.Doubling.absEv_unitFin] at hf ⊢
  rw [show ((∏ᶠ v, ‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) =
      ∏ᶠ v, ((‖GlobalTheory.AdelicU.evFin F v (Algebra.norm (AF F) y.1)‖₊ : ℝ≥0) : ℝ) from
    NNReal.toRealHom.toMonoidHom.map_finprod hf]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, coe_nnnorm]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorIdeleNormalizedAbsEqAdelicAbsNormStatement
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ), (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) * ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  first | exact @GlobalTheory.absE_eq_prod_norm_fstA_sndA | exact GlobalTheory.absE_eq_prod_norm_fstA_sndA | (intros; apply GlobalTheory.absE_eq_prod_norm_fstA_sndA <;> assumption)
end
end
