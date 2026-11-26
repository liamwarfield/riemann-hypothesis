module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsKActOfStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarOfComm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdeleTensorCoordsMulDenominatorBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdeleTensorCoordsMulDenominatorBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoordDenom

theorem finCoord_mul_denom : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  intro D
  set B := Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E) with hB
  obtain ⟨c, hc, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (GlobalTheory.HolDict.ShortVec.intRing D.host.F)
    (fun p : Fin (Module.finrank D.host.F D.host.E) × Fin (Module.finrank D.host.F D.host.E) ×
      Fin (Module.finrank D.host.F D.host.E) => B.repr (B p.1 * B p.2.1) p.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  refine ⟨c, hc, fun e₁ e₂ a b ha hb k => ?_⟩
  have ha' : ∀ i, (e₁ : Af D.host.F) * B.repr a i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := ha
  have hb' : ∀ i, (e₂ : Af D.host.F) * B.repr b i ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := hb
  change ((c * e₁ * e₂ : ℕ) : Af D.host.F) * B.repr (a * b) k ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr a, ← B.sum_repr b, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e : ((c * e₁ * e₂ : ℕ) : Af D.host.F) * (B.repr a i * B.repr b j * B.repr (B i * B j) k) =
      ((e₁ : Af D.host.F) * B.repr a i) * ((e₂ : Af D.host.F) * B.repr b j) * ((c : Af D.host.F) * B.repr (B i * B j) k) := by
    push_cast; ring
  rw [e]
  exact Subring.mul_mem _ (Subring.mul_mem _ (ha' i) (hb' j)) (h (i, j, k))

end GlobalTheory.CoordDenom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdeleTensorCoordsMulDenominatorBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdeleTensorCoords_mul_denominator_bound : ∀ (D : D7), ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E), (∀ k, (e₁ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D a k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → (∀ k, (e₂ : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D b k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F) → ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D (a * b) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  first | exact @GlobalTheory.CoordDenom.finCoord_mul_denom | exact GlobalTheory.CoordDenom.finCoord_mul_denom | (intros; apply GlobalTheory.CoordDenom.finCoord_mul_denom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DenInt

open IsDedekindDomain

theorem intRing_of_isIntegral {F : Type} [Field F] [NumberField F] {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Af F) c ∈ GlobalTheory.HolDict.ShortVec.intRing F := by
  refine GlobalTheory.HolDict.ShortVec.mem_intRing.2 fun v => ?_
  rw [AlgHom.commutes]
  refine Valued.toNormedField.norm_le_one_iff.2 ?_
  have := HeightOneSpectrum.valuation_le_one (K := F) v (⟨c, hc⟩ : 𝓞 F)
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v c).trans_le this

theorem exists_den (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  set b := Module.finBasis D.host.F D.host.E
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ D.host.F D.host.E
  obtain ⟨b', hb⟩ : ∃ b' : Fin (Module.finrank D.host.F D.host.E) → D.host.E,
      ∀ x k, Algebra.trace D.host.F D.host.E (b' k * x) = b.repr x k :=
    ⟨fun k => ((Algebra.traceForm D.host.F D.host.E).toDual (traceForm_nondegenerate D.host.F D.host.E)).symm (b.coord k),
      fun x k => LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_nondegenerate D.host.F D.host.E) (b.coord k) x⟩
  obtain ⟨d, hd, h⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (integralClosure ℤ D.host.E).toSubring b' fun k => by
    obtain ⟨k, hk, r, hr⟩ := GlobalTheory.SmoothForms.denom_exists_int (b' k)
    exact ⟨k, hk, hr ▸ r.2⟩
  refine ⟨d, hd, fun x hx k => ?_⟩
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k = algebraMap D.host.F (Af D.host.F) (b.repr x k) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.algebraMap_eq_smul_one]
  have e2 : (d : D.host.F) * b.repr x k = Algebra.trace D.host.F D.host.E (((d : D.host.E) * b' k) * x) := by
    rw [← hb, mul_assoc, ← nsmul_eq_mul d (b' k * x), map_nsmul, nsmul_eq_mul]
  have hi : IsIntegral ℤ ((d : D.host.F) * b.repr x k) := by
    rw [e2]
    exact Algebra.isIntegral_trace ((h k).mul hx)
  rw [e1, ← map_natCast (algebraMap D.host.F (Af D.host.F)) d, ← map_mul]
  exact intRing_of_isIntegral hi

end GlobalTheory.DenInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedDenominatorFiniteCoordsIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral : ∀ (D : D7), ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x → ∀ k, (d : Af D.host.F) * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ GlobalTheory.HolDict.ShortVec.intRing D.host.F := by
  first | exact @GlobalTheory.DenInt.exists_den | exact GlobalTheory.DenInt.exists_den | (intros; apply GlobalTheory.DenInt.exists_den <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBound
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelHeight
open GlobalTheory.HolDict.ShortVec (intRing finPr)
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (finCoord)

theorem openSub (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ a : Fin W.rank → Fin V.rank → Fin (Module.finrank D.host.F D.host.E) → Af D.host.F,
      (∀ i j k, a i j k ∈ intRing D.host.F) →
      (Matrix.of fun i j => ∑ k, pairA D.host.F 0 ((M₀ : Af D.host.F) * a i j k) ⊗ₜ[D.host.F]
        Module.finBasis D.host.F D.host.E k : WO V W) ∈ U :=
  GlobalTheory.T.exists_natMul_integralMatrices_subset_openAddSubgroup D V W U hU

theorem eq_sum_of_infPart (D : D7) (z : AE D) (hz : infPart D z = 0) :
    z = ∑ k, pairA D.host.F 0 (finCoord D (finPr D z) k) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E k :=
  GlobalTheory.T.eq_sum_finiteCoords_of_infinitePart_zero D z hz

theorem exists_denom_mul (D : D7) : ∃ c : ℕ, 0 < c ∧ ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
    (∀ k, (e₁ : Af D.host.F) * finCoord D a k ∈ intRing D.host.F) →
    (∀ k, (e₂ : Af D.host.F) * finCoord D b k ∈ intRing D.host.F) →
    ∀ k, ((c * e₁ * e₂ : ℕ) : Af D.host.F) * finCoord D (a * b) k ∈ intRing D.host.F :=
  GlobalTheory.T.finiteAdeleTensorCoords_mul_denominator_bound D

theorem exists_denom_integral (D : D7) : ∃ d : ℕ, 0 < d ∧ ∀ x : D.host.E, IsIntegral ℤ x →
    ∀ k, (d : Af D.host.F) * finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) k ∈ intRing D.host.F :=
  GlobalTheory.T.exists_fixed_denominator_finiteCoords_integral D

theorem infPart_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) : (finLift z).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i j) = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] z i j := rfl
  simp only [finLift, Matrix.map_apply, Matrix.zero_apply]
  rw [h1, TensorProduct.zero_tmul]

theorem finPr_finLift {D : D7} {m n : ℕ} (z : Matrix (Fin m) (Fin n) D.host.E) :
    (finLift z).map (finPr D) = z.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  ext i j
  rfl

theorem tmul_natCast_mul {D : D7} (N : ℕ) (e : D.host.E) :
    (1 : Af D.host.F) ⊗ₜ[D.host.F] ((N : D.host.E) * e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  rw [Algebra.TensorProduct.natCast_def', Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem finPr_Y {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (N : ℕ)
    (x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    (HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) : WO V W).map (finPr D) =
      ((N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e)) *
        P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
  have e1 : ((N : D.host.E) • x).map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) =
      (N : Af D.host.F ⊗[D.host.F] D.host.E) • x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j
    exact tmul_natCast_mul N (x i j)
  have e2 : (P.map (incA D)).map (finPr D) = P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) := by
    ext i j; rfl
  rw [Matrix.map_mul, finPr_finLift, e1, e2]

theorem finPr_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W).map (finPr D) =
      Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * Y.map (finPr D) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := by
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

theorem infPart_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (z : Matrix (Fin W.rank) (Fin r) D.host.E)
    (g : GA D V) (h : GA D W) :
    (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) (HMul.hMul (finLift z) (P.map (incA D)) : WO V W))
      (Formalism.L2.Theta.mt V g) : WO V W).map (infPart D) = 0 := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, infPart_finLift]
  simp

theorem actO_u {D : D7} {V W : HSp D} (g : GA D V) (h : GA D W) (Y : WO V W) :
    actO V W g h (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) : WO V W) = Y := by
  have e1 : Formalism.L2.Theta.mt W h * Formalism.L2.Theta.mt W h⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have e2 : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  simp only [actO, ← Matrix.mul_assoc]
  rw [e1, Matrix.one_mul, Matrix.mul_assoc, e2, Matrix.mul_one]

theorem entry_of_map_eq {m n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (u : Matrix (Fin m) (Fin n) R)
    (c : S) (w : Matrix (Fin m) (Fin n) S) (h : u.map f = c • w) (i : Fin m) (j : Fin n) : f (u i j) = c * w i j := by
  have := congrFun (congrFun h i) j
  simpa using this

theorem openSubY (D : D7) (V W : HSp D) (U : AddSubgroup (WO V W)) (hU : IsOpen (U : Set (WO V W))) :
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U := by
  obtain ⟨M₀, hM₀, hsub⟩ := openSub D V W U hU
  refine ⟨M₀, hM₀, fun y hy hc => ?_⟩
  choose b hb hbe using hc
  convert hsub b hb using 1
  ext i j
  rw [Matrix.of_apply, eq_sum_of_infPart D (y i j) (by simpa using congrFun (congrFun hy i) j)]
  exact Finset.sum_congr rfl fun k _ => by rw [hbe]

def Den (D : D7) (e : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) : Prop :=
  ∀ k, (e : Af D.host.F) * finCoord D z k ∈ intRing D.host.F

theorem den_sum {D : D7} {e : ℕ} {ι : Type} (s : Finset ι) (f : ι → Af D.host.F ⊗[D.host.F] D.host.E)
    (h : ∀ i ∈ s, Den D e (f i)) : Den D e (∑ i ∈ s, f i) := fun k => by
  unfold finCoord
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  exact (intRing D.host.F).sum_mem fun i hi => h i hi k

theorem den_matMul {D : D7} {c : ℕ} (hc : ∀ (e₁ e₂ : ℕ) (a b : Af D.host.F ⊗[D.host.F] D.host.E),
      Den D e₁ a → Den D e₂ b → Den D (c * e₁ * e₂) (a * b)) {m n p : ℕ} {e₁ e₂ : ℕ}
    (A : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (B : Matrix (Fin n) (Fin p) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hA : ∀ i j, Den D e₁ (A i j)) (hB : ∀ i j, Den D e₂ (B i j)) : ∀ i j, Den D (c * e₁ * e₂) ((A * B) i j) :=
  fun i j => by
    rw [Matrix.mul_apply]
    exact den_sum _ _ fun l _ => hc e₁ e₂ _ _ (hA i l) (hB l j)

theorem finCoord_natCast_mul (D : D7) (N : ℕ) (z : Af D.host.F ⊗[D.host.F] D.host.E) (k) :
    finCoord D ((N : Af D.host.F ⊗[D.host.F] D.host.E) * z) k = (N : Af D.host.F) * finCoord D z k := by
  unfold finCoord
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

theorem exists_u {D : D7} {V W : HSp D} {r : ℕ} (P : Matrix (Fin r) (Fin V.rank) D.host.E) (U : AddSubgroup (WO V W))
    {M₀ : ℕ} (hsub : ∀ y : WO V W, y.map (infPart D) = 0 →
      (∀ i j k, ∃ b ∈ intRing D.host.F, finCoord D (finPr D (y i j)) k = (M₀ : Af D.host.F) * b) → y ∈ U)
    (D' : ℕ) (g : GA D V) (h : GA D W) (x : Matrix (Fin W.rank) (Fin r) D.host.E)
    (hden : ∀ i j, Den D D' ((Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g) i j)) :
    ∃ u ∈ U, u.map (infPart D) = 0 ∧
      actO V W g h u = HMul.hMul (finLift (((M₀ * D' : ℕ) : D.host.E) • x)) (P.map (incA D)) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = M₀ * D' := ⟨_, rfl⟩
  rw [← hN]
  obtain ⟨wf, hwf⟩ : ∃ wf : Matrix (Fin W.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E),
    wf = Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig W.gram h⁻¹ * x.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) *
      P.map (fun e => (1 : Af D.host.F) ⊗ₜ[D.host.F] e) * Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram g := ⟨_, rfl⟩
  rw [← hwf] at hden
  obtain ⟨Y, hY⟩ : ∃ Y : WO V W, Y = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : WO V W, u = HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h⁻¹) Y) (Formalism.L2.Theta.mt V g) := ⟨_, rfl⟩
  have hinf : u.map (infPart D) = 0 := by
    rw [hu, hY]; exact infPart_u P _ g h
  have hfin : u.map (finPr D) = (N : Af D.host.F ⊗[D.host.F] D.host.E) • wf := by
    rw [hu, finPr_u, hY, finPr_Y, hwf]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  refine ⟨u, ?_, hinf, ?_⟩
  · refine hsub u hinf fun i j k => ⟨_, hden i j k, ?_⟩
    rw [entry_of_map_eq (finPr D) u _ wf hfin i j, finCoord_natCast_mul, hN, Nat.cast_mul, mul_assoc]
  · rw [hu, actO_u]
    exact hY

theorem levelheight : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ,
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W),
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧
    ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U,
      u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  intro D V W r P
  refine ⟨1, fun U hU => ?_⟩
  obtain ⟨θ, hθ⟩ := (GlobalTheory.Ker.exists_infFam_and_stdChar D).1
  obtain ⟨CV, hCV, hcV⟩ := GlobalTheory.Grow.height_comparison V hθ
  obtain ⟨CW, hCW, hcW⟩ := GlobalTheory.Grow.height_comparison W hθ
  obtain ⟨M₀, hM₀, hsub⟩ := openSubY D V W U hU
  obtain ⟨c, hc0, hc⟩ := exists_denom_mul D
  obtain ⟨dx, hdx, hx⟩ := exists_denom_integral D
  obtain ⟨dP, hdP, hP⟩ := GlobalTheory.HolDict.ShortVec.exists_common_denom (intRing D.host.F)
    (fun q : Fin r × Fin V.rank × Fin (Module.finrank D.host.F D.host.E) =>
      finCoord D ((1 : Af D.host.F) ⊗ₜ[D.host.F] P q.1 q.2.1) q.2.2)
    fun _ => GlobalTheory.HolDict.ShortVec.exists_denom_adele _
  set nV := ⌈CV⌉₊ with hnV
  set nW := ⌈CW⌉₊ with hnW
  have hnV0 : 0 < nV := Nat.ceil_pos.2 hCV
  have hnW0 : 0 < nW := Nat.ceil_pos.2 hCW
  refine ⟨M₀ * c ^ 3 * dx * dP * nW * nV, by positivity, fun g h => ?_⟩
  obtain ⟨dh, hdh0, hdhH, hdh⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := W) h⁻¹
  obtain ⟨dg, hdg0, hdgH, hdg⟩ := GlobalTheory.HolDict.ShortVec.exists_denom_le_height θ (V := V) g
  set D' := c * (c * (c * dh * dx) * dP) * dg with hD'
  refine ⟨M₀ * D', by positivity, ?_, fun x hxi => ?_⟩
  ·
    have h1 : (dh : ℝ) ≤ nW * GlobalTheory.Grow.height W h := by
      have := (hcW h⁻¹).1
      rw [GlobalTheory.Grow.height_inv] at this
      exact hdhH.trans (this.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _)
        (GlobalTheory.Grow.height_pos W h).le))
    have h2 : (dg : ℝ) ≤ nV * GlobalTheory.Grow.height V g :=
      hdgH.trans ((hcV g).1.trans (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (GlobalTheory.Grow.height_pos V g).le))
    rw [pow_one, hD']
    push_cast
    have hpos : (0 : ℝ) ≤ M₀ * c ^ 3 * dx * dP := by positivity
    calc (M₀ : ℝ) * (c * (c * (c * dh * dx) * dP) * dg) = (M₀ * c ^ 3 * dx * dP) * (dh * dg) := by ring
      _ ≤ (M₀ * c ^ 3 * dx * dP) * ((nW * GlobalTheory.Grow.height W h) * (nV * GlobalTheory.Grow.height V g)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (mul_nonneg (by positivity) (GlobalTheory.Grow.height_pos W h).le)) hpos
      _ = _ := by ring
  · exact exists_u P U hsub _ g h x (by
      rw [hD']
      refine den_matMul hc _ _ (den_matMul hc _ _ (den_matMul hc _ _ (fun i j => hdh i j) ?_) ?_) (fun i j => hdg i j)
      · intro i j; exact hx _ (hxi i j)
      · intro i j k; exact hP (i, j, k))
end GlobalTheory.LevelHeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpenSubgroupTranslateHeightBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openSubgroup_translate_height_bound : ∀ (D : D7) (V W : HSp D) (r : ℕ) (P : Matrix (Fin r) (Fin V.rank) D.host.E), ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ u ∈ U, u.map (infPart D) = 0 ∧ actO V W g h u = HMul.hMul (finLift ((N : D.host.E) • x)) (P.map (incA D)) := by
  first | exact @GlobalTheory.LevelHeight.levelheight | exact GlobalTheory.LevelHeight.levelheight | (intros; apply GlobalTheory.LevelHeight.levelheight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevel
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermIntegral

variable {D : D7}

def infLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] e

theorem map_incA_eq {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    x.map (incA D) = finLift x + infLift x := by
  ext a b
  simp only [Matrix.map_apply, Matrix.add_apply, finLift, infLift]
  rw [← TensorProduct.add_tmul]
  have : (pairA D.host.F 0 1 + pairA D.host.F 1 0 : AF D.host.F) = 1 := by
    refine Prod.ext ?_ ?_
    · exact zero_add _
    · exact add_zero _
  rw [this]
  rfl

theorem infLift_finPart {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) :
    (infLift x).map (finPart D) = 0 := by
  ext a b
  simp only [Matrix.map_apply, infLift, Matrix.zero_apply]
  show (sndA D.host.F (pairA D.host.F 1 0)) ⊗ₜ[D.host.F] x a b = 0
  have : sndA D.host.F (pairA D.host.F 1 0) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem compAt_infLift {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (x : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (infLift x) = x.map (tauE D τ) := by
  ext a b
  simp only [compAt, Matrix.map_apply, infLift]
  have : infPart D ((pairA D.host.F 1 0 : AF D.host.F) ⊗ₜ[D.host.F] x a b) =
      (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x a b := rfl
  rw [this]
  exact (hθ τ).1 _

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ τ, 2 * (tauE D τ e).re = ((Algebra.trace ℚ D.host.E e : ℚ) : ℝ) := by
  classical
  have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr] at h4
  have h5 := congrArg Complex.re h4
  simp only [ComplexEmbedding.conjugate_coe_eq, Complex.add_re, Complex.re_sum, Complex.conj_re,
    Complex.ratCast_re] at h5
  rw [← h5, Finset.sum_congr rfl fun τ _ => two_mul _, Finset.sum_add_distrib]

theorem phase_add (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y : Matrix (Fin W.rank) (Fin r) D.host.E)
    (κ κ' : Mx D W.rank r) :
    phase ψ V W C C' y (κ + κ') = phase ψ V W C C' y κ * phase ψ V W C C' y κ' := by
  have h : isoPart V W C (κ + κ') = isoPart V W C κ + isoPart V W C κ' := Matrix.add_mul _ _ _
  unfold phase
  rw [h, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D V W).2.1, AddChar.map_add_eq_mul]

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) :
    isoPart V W C (y.map (incA D)) = ratW W V (y * (adj D C * V.gram)) := by
  show HMul.hMul (y.map (incA D)) ((adj D C * V.gram).map (incA D)) = (y * (adj D C * V.gram)).map (incA D)
  simp only [Matrix.map_mul]

theorem phase_rat (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (V W : HSp D) {r : ℕ}
    (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (y x : Matrix (Fin W.rank) (Fin r) D.host.E) :
    phase ψ V W C C' y (x.map (incA D)) = 1 := by
  unfold phase
  rw [isoPart_rat, isoPart_rat]
  obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D V W (y * (adj D C' * V.gram)) (x * (adj D C * V.gram))
  rw [ha]
  exact hψ.2.2.1 a

theorem trace_tau (τ : D.what₂.Tau) {m n : ℕ} (q : Matrix (Fin m) (Fin n) D.host.E)
    (x : Matrix (Fin n) (Fin m) D.host.E) :
    Matrix.trace (q.map (tauE D τ) * x.map (tauE D τ)) = tauE D τ (Matrix.trace (q * x)) := by
  rw [← Matrix.map_mul (f := tauE D τ)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem ratPair_nat_smul (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) (N : ℕ) :
    ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * ((N : D.host.E) • x))) : ℚ) : ℝ) =
      (N : ℝ) * ratPair W y x := by
  have h : Matrix.trace (pairQ W y * ((N : D.host.E) • x)) = N • Matrix.trace (pairQ W y * x) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, nsmul_eq_mul]
  rw [h, map_nsmul, nsmul_eq_mul, ratPair]
  push_cast
  rfl

theorem integral : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  intro D V V' W r C C' B hs hCC ψ hψ θ hθ μ 𝓨 hY
  obtain ⟨e, he⟩ := GlobalTheory.T.openSubgroup_translate_height_bound D V W r (adj D C * V.gram)
  refine ⟨e, fun U hU => ?_⟩
  obtain ⟨M, hM, hMN⟩ := he U hU
  refine ⟨M, hM, fun g h => ?_⟩
  obtain ⟨N, hN, hNle, hx⟩ := hMN g h
  refine ⟨N, hN, hNle, fun F hF hinv y hy x hxi => ?_⟩
  obtain ⟨u, huU, hufin, hact⟩ := hx x hxi
  have h1 : heisO ψ V W (isoPart V W C (finLift ((N : D.host.E) • x))) F = F := by
    have := hinv u huU hufin
    rw [hact] at this
    exact this
  have h2 := GlobalTheory.T.mixedModelTerm_heisenbergIsotropic_character D V V' W r C C' B hs ψ hψ μ 𝓨 hY F hF y (finLift ((N : D.host.E) • x))
  rw [h1] at h2
  have hph : phase ψ V W C C' y (finLift ((N : D.host.E) • x)) = 1 :=
    mul_right_cancel₀ hy (by rw [one_mul]; exact h2.symm)
  have hinf : phase ψ V W C C' y (infLift ((N : D.host.E) • x)) = 1 := by
    have := phase_rat ψ hψ.1 V W C C' y ((N : D.host.E) • x)
    rw [map_incA_eq, phase_add, hph, one_mul] at this
    exact this
  rw [GlobalTheory.T.mixedModelHeisenbergPhase_eq_cexp_realPoints D V W r C C' hCC ψ hψ θ hθ y _ (infLift_finPart _)] at hinf
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hinf
  have hsum : (∑ τ, 2 * (Matrix.trace ((pairQ W y).map (tauE D τ) *
      compAt θ τ (infLift ((N : D.host.E) • x)))).re : ℝ) = (N : ℝ) * ratPair W y x := by
    rw [← ratPair_nat_smul, ← sum_two_re_tauE]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [compAt_infLift hθ, trace_tau]
  rw [hsum] at hn
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : (((N : ℝ) * ratPair W y x : ℝ) : ℂ) = ((n : ℝ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    push_cast
    ring
  exact_mod_cast h3

end GlobalTheory.MixedTermIntegral

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermBoundedDenominatorsMovedLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerm_bounded_denominators_moved_level : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ e : ℕ, ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ M : ℕ, 0 < M ∧ ∀ (g : GA D V) (h : GA D W), ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ M * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ e ∧ ∀ F : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ V W (actO V W g h u) F = F) → ∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, term ψ V V' W C C' B μ 𝓨 F y ≠ 0 → ∀ x : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ a b, IsIntegral ℤ (x a b)) → ∃ c : ℤ, (N : ℝ) * ratPair W y x = c := by
  first | exact @GlobalTheory.MixedTermIntegral.integral | exact GlobalTheory.MixedTermIntegral.integral | (intros; apply GlobalTheory.MixedTermIntegral.integral <;> assumption)
end
