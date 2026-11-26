module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGroupShiftHalfTorsionRoot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDenOfValLeOne
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.HAtBasis

variable {K : Type} [Field K] [NumberField K]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.HAtBasis.isLattice_of_basisAt {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG)
    {B : GL (Fin n) K} (hB : _root_.Formalism.L2.DIV.IsBasisAt w M B) : Submodule.IsFullLattice K M := by
  haveI : Submodule.IsLattice K M := ⟨hM, fun s hs hli =>
    (LinearIndependent.iff_fractionRing _ _).mp hli⟩
  refine ⟨?_⟩
  have hcol : ∀ j, (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈
      Submodule.span K (M : Set (Fin n → K)) := by
    intro j
    have h1 : (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
      rw [hB]
      apply _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M _).1 h1
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have hs' : s = 0 := by exact_mod_cast h0
      rw [hs']
      exact w.asIdeal.zero_mem
    have h2 := Submodule.smul_mem (Submodule.span K (M : Set (Fin n → K))) ((s : K)⁻¹)
      (Submodule.subset_span hsx)
    convert h2 using 1
    funext i
    simp [Algebra.smul_def, hs0]
  apply top_unique
  intro x hx
  have hrange : LinearMap.range (B : Matrix (Fin n) (Fin n) K).mulVecLin ≤
      Submodule.span K (M : Set (Fin n → K)) := by
    rw [Matrix.range_mulVecLin]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hcol j)
  apply hrange
  refine ⟨(B⁻¹ : GL (Fin n) K).val *ᵥ x, ?_⟩
  change B.val *ᵥ ((B⁻¹).val *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, show B.val * (B⁻¹).val = 1 from B.mul_inv, Matrix.one_mulVec]
variable {ι : Type} [Fintype ι] {a : ℕ}


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
omit [NumberField K] in
theorem _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv (lam : ι → _root_.Formalism.BasicNotions.DomWeight a)
    (B : ι → GL (Fin a) K) (F : _root_.Formalism.L2.DIV.Pol K ι a) :
    _root_.Formalism.L2.DIV.actP lam (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ F =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
        _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F := by
  have hg : ∀ τ, (((fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ τ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (B τ : Matrix (Fin a) (Fin a) K)ᵀ := fun τ => rfl
  simp only [_root_.Formalism.L2.DIV.actP, _root_.Formalism.L2.DIV.trAct, _root_.Formalism.L2.DIV.detTw_eq, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hg,
    Matrix.det_transpose, Matrix.transpose_transpose]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem valuation_coe_eq_one_of_notMem {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : w.valuation K (s : K) = 1 := by
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem exists_notMem_mul_eq_integer_of_valuation_le_one {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : w.valuation K x ≤ 1) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : 𝓞 K, (s : K) * x = (c : K) := by
  have h1 : x ∈ (w.valuation K).valuationSubring := hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h1
  have h3 : x ∈ (HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := h1
  rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h3
  have h2 : x ∈ _root_.GlobalTheory.LatBasisAt.locRing w := by
    unfold _root_.GlobalTheory.LatBasisAt.locRing
    exact h3
  obtain ⟨c, s, hs, rfl⟩ := (_root_.GlobalTheory.LatBasisAt.mem_locRing w x).1 h2
  refine ⟨s, hs, c, ?_⟩
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
  change algebraMap (𝓞 K) K s * (algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K s)⁻¹) =
    algebraMap (𝓞 K) K c
  field_simp


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
theorem _root_.GlobalTheory.HAtBasis.mem_HAt_iff : ∀ (K : Type) [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) (B : ι → GL (Fin a) K),
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.LatWithBasis w M B → ∀ F : _root_.Formalism.L2.DIV.VV K lam,
      F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
        ∀ m, w.valuation K (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
          _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a)).coeff m) ≤ 1 := by
  intro K _ _ w ι _ a lam M B hMB F
  have hB' : ∀ τ, _root_.Formalism.L2.DIV.IsBasisAt w (_root_.Formalism.L2.DIV.dualFr (M τ)) (_root_.Formalism.BasicNotions.inside₂ K a (B τ)) :=
    fun τ => _root_.GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hMB τ).1 (hMB τ).2
  have hlat : ∀ τ, Submodule.IsFullLattice K (_root_.Formalism.L2.DIV.dualFr (M τ)) := fun τ =>
    _root_.GlobalTheory.DualLat.isLattice_dualFr _ (_root_.GlobalTheory.HAtBasis.isLattice_of_basisAt w (hMB τ).1 (hMB τ).2)
  have hloc := (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam
    (fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) hlat w (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ)) hB').1
  have step1 : F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
      (F : _root_.Formalism.L2.DIV.Pol K ι a) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.nabP lam fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt _root_.Formalism.L2.DIV.nabK
    rw [_root_.PI.LocGlobInclWork.mem_localization_iff, _root_.PI.LocGlobInclWork.mem_localization_iff]
    rfl
  rw [step1, hloc, _root_.GlobalTheory.TransLoc.mem_map_actP, _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  set G : _root_.Formalism.L2.DIV.Pol K ι a := (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
    _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a) with hG
  have hcoeff : ∀ (s : 𝓞 K) m, AddMonoidAlgebra.coeff (s • G) m = (s : K) * AddMonoidAlgebra.coeff G m := by
    intro s m
    erw [Algebra.smul_def, MvPolynomial.algebraMap_apply, coeff_C_mul]
  constructor
  · intro hGm m
    obtain ⟨s, hs, hsG⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).1 hGm
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hsG
    have hc : AddMonoidAlgebra.coeff (s • G) m = ((AddMonoidAlgebra.coeff P m : 𝓞 K) : K) := by
      have h' : AddMonoidAlgebra.coeff (_root_.Formalism.L2.DIV.toK K _ P) m = AddMonoidAlgebra.coeff (s • G) m := congrArg (AddMonoidAlgebra.coeff · m) hP
      rw [← h']
      simp [_root_.Formalism.L2.DIV.toK, coeff_map]
    rw [hcoeff] at hc
    have hs0 : (s : K) ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
    have e : AddMonoidAlgebra.coeff G m = (s : K)⁻¹ * ((AddMonoidAlgebra.coeff P m : 𝓞 K) : K) := by
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, map_mul, map_inv₀, valuation_coe_eq_one_of_notMem w hs, inv_one, one_mul]
    exact HeightOneSpectrum.valuation_le_one w _
  · intro hint
    choose sf hsf c hc using fun m => exists_notMem_mul_eq_integer_of_valuation_le_one w _ (hint m)
    refine (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).2 ⟨∏ m ∈ G.support, sf m, ?_, ?_⟩
    · intro hmem
      obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hsf m hm
    · have hGV : G ∈ _root_.Formalism.L2.DIV.VV K lam :=
        Submodule.smul_mem _ _ (_root_.Formalism.L2.DIV.ps_blockAct_mem_VV lam _ F.2)
      refine _root_.GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral K ι a lam (fun _ => 0) _
        (Submodule.smul_of_tower_mem _ _ hGV) fun m => ?_
      simp only [pow_zero, Finset.prod_const_one, one_mul]
      change IsIntegral ℤ (AddMonoidAlgebra.coeff ((∏ m ∈ G.support, sf m) • G) m)
      rw [hcoeff]
      by_cases hm : m ∈ G.support
      · rw [← Finset.mul_prod_erase _ _ hm]
        push_cast
        rw [mul_comm ((sf m : 𝓞 K) : K), mul_assoc, hc m]
        have hI := RingOfIntegers.isIntegral_coe ((∏ i ∈ G.support.erase m, sf i) * c m)
        convert hI using 1
        simp
      · rw [notMem_support_iff.1 hm, mul_zero]
        exact isIntegral_zero

end GlobalTheory.HAtBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemExtLatOfMemLocP
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.ExtLatMatrix

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L}


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in
theorem _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP (h : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1)
    {a : ℕ} (M : Submodule (𝓞 K) (Fin a → K)) (x : Fin a → K) (hx : x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) :
    (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M := by
  obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M x).1 hx
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have hs' : s = 0 := by exact_mod_cast h0
    rw [hs']
    exact w.asIdeal.zero_mem
  have hval : w.valuation K ((s : K)⁻¹) ≤ 1 := by
    rw [map_inv₀]
    have h1 : w.valuation K (s : K) = 1 := by
      rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs
    rw [h1, inv_one]
  have hint : σ ((s : K)⁻¹) ∈ v.integer := (h _).2 hval
  have hmem : (fun i => σ ((s • x) i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M :=
    Submodule.subset_span ⟨s • x, hsx, rfl⟩
  have hsm := Submodule.smul_mem _ (⟨σ ((s : K)⁻¹), hint⟩ : v.integer) hmem
  convert hsm using 1
  funext i
  change σ (x i) = σ ((s : K)⁻¹) * σ ((s : K) * x i)
  rw [← map_mul, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {L Γ : Type} [Field L]
  [LinearOrderedCommGroupWithZero Γ] {v : Valuation L Γ} {σ : K →+* L} in
theorem _root_.GlobalTheory.ExtLatMatrix.extLat_matrix_integral : ∀ (K : Type) [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (L Γ : Type) [Field L] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (σ : K →+* L), (∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) →
    (∀ (a : ℕ) (M : Submodule (𝓞 K) (Fin a → K)), ∀ x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M,
      (fun i => σ (x i)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) ∧
    ∀ (a b : ℕ) (M : Submodule (𝓞 K) (Fin a → K)) (MW : Submodule (𝓞 K) (Fin b → K))
      (B : GL (Fin a) K) (BW : GL (Fin b) K), _root_.Formalism.L2.DIV.IsBasisAt w M B → _root_.Formalism.L2.DIV.IsBasisAt w MW BW →
      ∀ ap : Matrix (Fin a) (Fin b) L,
        (∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW, ap *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M) →
        ∀ i j, v ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap *
          (BW : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1 := by
  intro K _ _ w L Γ _ _ v σ h
  refine ⟨fun a M x hx => _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h M x hx, ?_⟩
  intro a b M MW B BW hB hBW ap hap i j
  have hunit : ∀ t : 𝓞 K, t ∉ w.asIdeal → v (σ ((t : K)⁻¹)) ≤ 1 := by
    intro t ht
    refine (h _).2 ?_
    rw [map_inv₀]
    have h1 : w.valuation K (t : K) = 1 := by
      rw [show (t : K) = algebraMap (𝓞 K) K t from rfl, HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 ht
    rw [h1, inv_one]
  have hint : ∀ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ M, ∀ k,
      v (((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ y) k) ≤ 1 := by
    intro y hy
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      have hm' : m ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.colLat B) := by
        unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
        rw [← hB]
        exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hm
      obtain ⟨t, ht, htm⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal _ m).1 hm'
      unfold _root_.Formalism.L2.DIV.colLat at htm
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 htm
      have ht0 : (t : K) ≠ 0 := by
        intro h0
        apply ht
        have ht' : t = 0 := by exact_mod_cast h0
        rw [ht']
        exact w.asIdeal.zero_mem
      have hBc : (B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K)) = (t : K) • m := by
        funext r
        have hr := congrFun hc r
        simp only [Finset.sum_apply, Pi.smul_apply] at hr
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
        rw [← Algebra.smul_def] at *
        convert hr using 1
        · refine Finset.sum_congr rfl fun k _ => ?_
          rw [Algebra.smul_def, mul_comm]
          try rfl
      have hBm : ((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m =
          (t : K)⁻¹ • fun k => (c k : K) := by
        have e : m = (t : K)⁻¹ • ((B : Matrix (Fin a) (Fin a) K) *ᵥ (fun k => (c k : K))) := by
          rw [hBc, smul_smul, inv_mul_cancel₀ ht0, one_smul]
        rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
        simp
      intro k
      have e : ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ) *ᵥ (fun i => σ (m i))) k =
          σ ((((B⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) *ᵥ m) k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e, hBm, Pi.smul_apply, smul_eq_mul, map_mul, map_mul]
      refine mul_le_one' (hunit t ht) ((h _).2 ?_)
      exact HeightOneSpectrum.valuation_le_one w (c k)
    | zero => simp
    | add y z _ _ hy hz =>
      intro k
      rw [Matrix.mulVec_add, Pi.add_apply]
      exact v.map_add_le (hy k) (hz k)
    | smul c y _ hy =>
      intro k
      rw [Matrix.mulVec_smul, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul]
      exact mul_le_one' c.2 (hy k)
  have hcol : (fun k => σ ((BW : Matrix (Fin b) (Fin b) K) k j)) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.extLat v σ MW := by
    refine _root_.GlobalTheory.ExtLatMatrix.mem_extLat_of_mem_locP h MW _ ?_
    unfold _root_.Formalism.L2.DIV.IsBasisAt at hBW
    rw [hBW]
    exact _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have key := hint _ (hap _ hcol) i
  convert key using 2
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.ExtLatMatrix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.SubstMem

open Formalism.GradedWeylDivisibility

variable {K : Type} [Field K]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl {a b : ℕ} (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h1 : ∀ i, ν' (Fin.castLE hab i) = ν i) (h2 : ∀ j : Fin b, a ≤ (j : ℕ) → ν' j = 0)
    (f : MvPolynomial (Fin a × Fin a) K) (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a ν) :
    rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K b b ν' := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hhom, hinv⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    have hinj : Function.Injective (Prod.map (Fin.castLE hab) (Fin.castLE hab)) :=
      (Fin.castLE_injective hab).prodMap (Fin.castLE_injective hab)
    have hmem : d ∈ (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f).support :=
      mem_support_iff.2 hd
    rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
    obtain ⟨d0, hd0, rfl⟩ := hmem
    have h0 := hhom (mem_support_iff.1 hd0)
    rw [Finsupp.weight_apply] at h0
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
    funext k
    by_cases hk : (k : ℕ) < a
    · have hk' : k = Fin.castLE hab ⟨k, hk⟩ := Fin.ext rfl
      rw [hk', h1, ← h0]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply]
      simp only [Fin.ext_iff, Fin.coe_castLE]
    · rw [h2 k (not_lt.1 hk)]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_eq_zero fun v _ => ?_
      have hne : Fin.castLE hab v.2 ≠ k := by
        intro h; apply hk; rw [← h]; simp
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hne]
  · intro l j hlj
    by_cases hj : (j : ℕ) < a
    · have hl : (l : ℕ) < a := lt_trans hlj hj
      obtain ⟨l', rfl⟩ : ∃ l' : Fin a, Fin.castLE hab l' = l := ⟨⟨l, hl⟩, Fin.ext rfl⟩
      obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castLE hab j' = j := ⟨⟨j, hj⟩, Fin.ext rfl⟩
      have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K (Fin.castLE hab l') (Fin.castLE hab j')).comp
          (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename (Option.map (Prod.map (Fin.castLE hab) (Fin.castLE hab)))).comp
            (_root_.Formalism.GradedWeylDivisibility.colAddGen K (r := a) l' j') := by
        apply MvPolynomial.algHom_ext
        rintro ⟨v1, v2⟩
        by_cases hv : v2 = j'
        · subst hv
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_pos rfl]
          simp only [ite_true, if_true, map_add (f := _), map_mul, rename_X]
          rfl
        · have hv' : Fin.castLE hab v2 ≠ Fin.castLE hab j' :=
            fun h => hv (Fin.castLE_injective hab h)
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_neg hv, if_neg hv']
          rfl
      have e := DFunLike.congr_fun key f
      simp only [AlgHom.comp_apply] at e
      rw [e, hinv l' j' (show l' < j' from hlj), rename_rename, rename_rename]
      rfl
    · have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K l j).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename some).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) := by
        apply MvPolynomial.algHom_ext
        intro v
        have hne : Fin.castLE hab v.2 ≠ j := by
          intro h; apply hj; rw [← h]; exact v.2.isLt
        simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, if_neg hne]
      exact DFunLike.congr_fun key f


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.det_pow_mem (a m : ℕ) :
    _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ m ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a (fun _ => m) := by
  refine _root_.Formalism.GradedWeylDivisibility.dualWeyl_of_eq (_root_.Formalism.GradedWeylDivisibility.dualWeyl_pow (_root_.Formalism.GradedWeylDivisibility.initMinor_mem (R := K) (id : Fin a → Fin a) le_rfl) m) ?_
  funext i
  simp [_root_.Formalism.GradedWeylDivisibility.initW]

def padRows {a b : ℕ} (A : Matrix (Fin a) (Fin b) K) : Matrix (Fin b) (Fin b) K :=
  fun α β => if h : (α : ℕ) < a then A ⟨α, h⟩ β else 0

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.substAdj_blockEmb {ι : Type} {a b : ℕ} (hab : a ≤ b)
    (ap : ι → Matrix (Fin a) (Fin b) K) (τ : ι) (f : MvPolynomial (Fin a × Fin a) K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f)) := by
  have key : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap).comp (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ) = (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ).comp
      ((_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))).comp
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)))) := by
    apply MvPolynomial.algHom_ext
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj, _root_.Formalism.GradedWeylDivisibility.blockEmb, _root_.Formalism.GradedWeylDivisibility.rowAct, _root_.GlobalTheory.SubstMem.padRows, map_sum]
  exact DFunLike.congr_fun key f

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_eq_w_last {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (h : 0 < N) :
    l.detShift = l.w ⟨N - 1, by omega⟩ := by
  unfold _root_.Formalism.BasicNotions.DomWeight.detShift
  rw [dite_eq_left h]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_le_w {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (i : Fin N) : l.detShift ≤ l.w i := by
  rw [DomWeight_detShift_eq_w_last l (Fin.pos i)]
  exact l.anti (Fin.le_def.2 (by simp; omega))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {f : MvPolynomial (Fin r × Fin n) R} {ν : Fin n → ℕ}
    (hf : IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) f ν) :
    IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) (_root_.Formalism.GradedWeylDivisibility.rowAct R g f) ν := by
  rw [← mem_weightedHomogeneousSubmodule]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← support_sum_monomial_coeff f, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule, ← hf (mem_support_iff.1 hd)]
  have e : _root_.Formalism.GradedWeylDivisibility.rowAct R g (monomial d (AddMonoidAlgebra.coeff f d)) =
      C (AddMonoidAlgebra.coeff f d) * d.prod (fun v k => (_root_.Formalism.GradedWeylDivisibility.rowAct R g (X v)) ^ k) := by
    simp only [_root_.Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, aeval_X, algebraMap_eq]
  rw [e, Finsupp.weight_apply, ← zero_add (d.sum fun i c => c • _root_.Formalism.GradedWeylDivisibility.colW r n i)]
  exact (isWeightedHomogeneous_C _ _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (_root_.Formalism.GradedWeylDivisibility.rowAct_X_isWH g v).pow (d v))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem rowAct_mem_dualWeyl_of_mem_dualWeyl {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : _root_.Formalism.GradedWeylDivisibility.rowAct R g f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous g hf.1, fun l j hlj => ?_⟩
  rw [_root_.Formalism.GradedWeylDivisibility.colAddGen_rowAct, hf.2 l j hlj, ← _root_.Formalism.GradedWeylDivisibility.rename_rowAct]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem frDet_eq_blockEmb_initMinor_id {K : Type} [Field K] {ι : Type} (a : ℕ) (τ : ι) :
    _root_.Formalism.L2.Ker.frDet K a τ = _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl) := by
  simp only [_root_.Formalism.L2.Ker.frDet, _root_.Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp [_root_.Formalism.GradedWeylDivisibility.blockEmb]


open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.substAdj_sharp_mem : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι]
    (a b : ℕ) (hab : a < b) (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (lam' : ι → _root_.Formalism.BasicNotions.DomWeight b) (s s' : ι → ℤ)
    (n : ι → ℕ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.WtCompat hab lam lam' s s' n →
    ∀ (ap : ι → Matrix (Fin a) (Fin b) K), ∀ P ∈ _root_.Formalism.L2.DIV.VV K lam,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab.le ap (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) ∈ _root_.Formalism.L2.DIV.VV K lam' := by
  intro K _ ι _ a b hab lam lam' s s' n hc ap P hP
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hd' : ∀ τ, (lam' τ).detShift = -s τ := fun τ => by
    rw [DomWeight_detShift_eq_w_last _ (by omega)]
    exact hc2 τ _ (by simp; omega)
  have hw1 : ∀ τ i, (lam' τ).natW (Fin.castLE hab.le i) = (lam τ).natW i + n τ := by
    intro τ i
    have e1 := hc1 τ i
    have e2 := hc3 τ
    have e3 := DomWeight_detShift_le_w (lam τ) i
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hw2 : ∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).natW j = 0 := by
    intro τ j hj
    have e1 := hc2 τ j hj
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hsharp : ∀ Q : _root_.Formalism.L2.DIV.Pol K ι a, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n Q = Q * ∏ τ, _root_.Formalism.L2.Ker.frDet K a τ ^ n τ :=
    fun Q => rfl
  unfold _root_.Formalism.L2.DIV.VV _root_.Formalism.GradedWeylDivisibility.tensorLat at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [hsharp, ← Finset.prod_mul_distrib, map_prod]
    refine Submodule.subset_span ⟨fun τ => _root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
      (rename (Prod.map (Fin.castLE hab.le) (Fin.castLE hab.le))
        (F τ * _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ n τ)), fun τ => ?_, ?_⟩
    · refine rowAct_mem_dualWeyl_of_mem_dualWeyl _ ?_
      refine _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl hab.le ((lam τ).natW + fun _ => n τ) _
        (fun i => by simp [hw1]) (hw2 τ) _ ?_
      exact _root_.Formalism.GradedWeylDivisibility.dualWeyl_mul (hF τ) (_root_.GlobalTheory.SubstMem.det_pow_mem a (n τ))
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [frDet_eq_blockEmb_initMinor_id, ← map_pow, ← map_mul, _root_.GlobalTheory.SubstMem.substAdj_blockEmb]
  | zero => simp [hsharp]
  | add x y _ _ hx hy =>
    rw [hsharp, add_mul, map_add (f := _)]
    exact add_mem (by rw [← hsharp]; exact hx) (by rw [← hsharp]; exact hy)
  | smul c x _ hx =>
    rw [hsharp, smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ c (by rw [← hsharp]; exact hx)

end GlobalTheory.SubstMem
end
end

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetPoint

section Expand

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

abbrev expL (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : (ι × Fin b × Fin b) →₀ ℕ :=
  μ.comapDomain Sum.inl Sum.inl_injective.injOn

abbrev expR (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) : DVar ι a b →₀ ℕ :=
  μ.comapDomain Sum.inr Sum.inr_injective.injOn

omit [Fintype ι] in
theorem constr_monomial {σ V : Type} [AddCommGroup V] [Module K V] (f : (σ →₀ ℕ) → V) (μ : σ →₀ ℕ) (c : K) :
    (basisMonomials σ K).constr K f (monomial μ c) = c • f μ := by
  have h : (monomial μ c : MvPolynomial σ K) = c • basisMonomials σ K μ := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Module.Basis.constr_basis]

omit [Fintype ι] in
theorem jetLin_eq_sum (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J Q = ∑ μ ∈ Q.support, J (expR μ) • monomial (expL μ) (Q.coeff μ) := by
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [jetLin, constr_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_comm]

theorem jetMap_eq_sum (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J n P = ∑ μ ∈ (subD K ι a b (sharp n P)).support,
      J (expR μ) • monomial (expL μ) ((subD K ι a b (sharp n P)).coeff μ) :=
  jetLin_eq_sum J _

def ptEval (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L) :
    MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K →+* Pol L ι b :=
  eval₂Hom (C.comp σ) (Sum.elim X fun k => C (ap k.1 k.2.2 k.2.1))

theorem ptEval_monomial (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L)
    (μ : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (c : K) :
    ptEval σ ap (monomial μ c) = ptTable ap (expR μ) • monomial (expL μ) (σ c) := by
  rw [ptEval, eval₂Hom_monomial, monomial_eq, ptTable, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, smul_eq_C_mul,
    map_prod]
  simp only [RingHom.comp_apply, Sum.elim_inl, Sum.elim_inr, Finsupp.comapDomain_apply, map_pow]
  ring

omit [Fintype ι] in
theorem ptEval_subD (hab : a ≤ b) (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L) (P : Pol K ι a) :
    ptEval σ ap (subD K ι a b P) = substAdj hab ap (map σ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [ptEval, subD, substAdj]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    have h : v.2.2.1 < b := lt_of_lt_of_le v.2.2.2 hab
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [subD, substAdj, aeval_X, dite_eq_left h, map_sum, map_mul, ptEval, eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    exact Finset.sum_congr rfl fun β _ => mul_comm _ _

theorem sum_ptTable (hab : a ≤ b) (σ : K →+* L) (ap : ι → Matrix (Fin a) (Fin b) L) (P : Pol K ι a) :
    ∑ μ ∈ (subD K ι a b P).support, ptTable ap (expR μ) • monomial (expL μ) (σ ((subD K ι a b P).coeff μ)) =
      substAdj hab ap (map σ P) := by
  rw [← ptEval_subD]
  conv_rhs => rw [(subD K ι a b P).as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun μ _ => (ptEval_monomial σ ap μ _).symm

theorem jetMap_ptTable (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (ptTable ap) n P = substAdj hab ap (sharp n P) := by
  rw [jetMap_eq_sum]
  have h := sum_ptTable hab (RingHom.id K) ap (sharp n P)
  rwa [map_id] at h

theorem jetMap_mem [Infinite K] (hab : a ≤ b) (n : ι → ℕ) (P : Pol K ι a) (U : Submodule K (Pol K ι b))
    (h : ∀ ap : ι → Matrix (Fin a) (Fin b) K, substAdj hab ap (sharp n P) ∈ U) (J : (DVar ι a b →₀ ℕ) → K) :
    jetMap J n P ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set Q := subD K ι a b (sharp n P) with hQ
  have h0 : (∑ μ ∈ Q.support, monomial (expR μ) (φ (monomial (expL μ) (Q.coeff μ))) :
      MvPolynomial (DVar ι a b) K) = 0 := by
    refine MvPolynomial.funext fun x => ?_
    have h1 := hφ _ (h fun τ => Matrix.of fun α β => x (τ, β, α))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← jetMap_ptTable, jetMap_eq_sum, map_sum] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← h1]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [eval_monomial, map_smul, smul_eq_mul, mul_comm]
    rfl
  have h2 := congrArg ((basisMonomials (DVar ι a b) K).constr K J) h0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at h2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [jetMap_eq_sum, map_sum, ← h2]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [constr_monomial, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

theorem coe_jetOp (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (F : VV K lam) (h : jetMap J n (F : Pol K ι a) ∈ VV K lam') :
    ((jetOp lam lam' J n F : VV K lam') : Pol K ι b) = jetMap J n (F : Pol K ι a) := by
  have h1 : retrVV K lam' ((⟨_, h⟩ : VV K lam') : Pol K ι b) = ⟨_, h⟩ := Submodule.projectionOnto_apply_left _ _
  exact congrArg Subtype.val h1

omit [Fintype ι] in
theorem detShift_eq {hab : a < b} {lam : ι → DomWeight a} {lam' : ι → DomWeight b} {s s' : ι → ℤ} {n : ι → ℕ}
    (h : WtCompat hab lam lam' s s' n) (τ : ι) : (lam' τ).detShift = -s τ := by
  rw [DomWeight.detShift, dite_eq_left (by omega)]
  exact h.2.1 τ _ (by simp only; omega)

omit [Fintype ι] in
theorem map_frDet {R : Type} [CommRing R] (φ : Pol K ι a →+* R) (τ : ι) :
    φ (frDet K a τ) = (Matrix.of fun α s : Fin a => φ (X (τ, α, s))).det := by
  rw [frDet, RingHom.map_det]
  rfl


end Expand

section Integral

open Formalism.GradedWeylDivisibility (blockAct)

variable {K L Γ : Type} [Field K] [Field L] [LinearOrderedCommGroupWithZero Γ] {ι : Type} [Fintype ι] {a b : ℕ}

theorem mem_range_iff (v : Valuation L Γ) {τ : Type} (P : MvPolynomial τ L) :
    P ∈ (map (σ := τ) v.integer.subtype).range ↔ ∀ m, v (P.coeff m) ≤ 1 := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]
    exact (Q.coeff m).2
  · intro h
    rw [P.as_sum]
    exact sum_mem fun m _ => ⟨monomial m ⟨_, h m⟩, by rw [map_monomial]; rfl⟩

omit [Fintype ι] in
theorem substAdj_int (v : Valuation L Γ) (hab : a ≤ b) (A : ι → Matrix (Fin a) (Fin b) L)
    (hA : ∀ τ i j, v (A τ i j) ≤ 1) {P : Pol L ι a} (hP : P ∈ (map v.integer.subtype).range) :
    substAdj hab A P ∈ (map v.integer.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [substAdj]⟩
  | add p q hp hq => rw [map_add (f := _), map_add (f := _)]; exact add_mem hp hq
  | mul_X p x hp =>
    rw [map_mul, map_mul, map_X]
    refine mul_mem hp ?_
    rw [substAdj, aeval_X]
    exact sum_mem fun β _ => mul_mem ⟨C ⟨_, hA _ _ _⟩, by rw [map_C]; rfl⟩ ⟨X _, map_X _ _⟩

theorem sharp_int (v : Valuation L Γ) (n : ι → ℕ) {P : Pol L ι a} (hP : P ∈ (map v.integer.subtype).range) :
    sharp n P ∈ (map v.integer.subtype).range := by
  refine mul_mem hP (prod_mem fun τ _ => pow_mem ?_ _)
  rw [frDet, Matrix.det_apply']
  exact sum_mem fun g _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => ⟨X _, map_X _ _⟩)

omit [Fintype ι] in
theorem blockAct_substAdj (hab : a ≤ b) (ap : ι → Matrix (Fin a) (Fin b) L) (g : ι → Matrix (Fin b) (Fin b) L)
    (P : Pol L ι a) : blockAct L g (substAdj hab ap P) = substAdj hab (fun τ => ap τ * g τ) P := by
  have h : (blockAct L g).comp (substAdj hab ap) = substAdj hab (fun τ => ap τ * g τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, blockAct, substAdj, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply]
    simp only [algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  exact congrArg (fun φ => φ P) h

omit [Fintype ι] in
theorem substAdj_blockAct (hab : a ≤ b) (A : ι → Matrix (Fin a) (Fin b) L) (g : ι → Matrix (Fin a) (Fin a) L)
    (P : Pol L ι a) : substAdj hab A (blockAct L g P) = substAdj hab (fun τ => g τ * A τ) P := by
  have h : (substAdj hab A).comp (blockAct L g) = substAdj hab (fun τ => g τ * A τ) := by
    apply MvPolynomial.algHom_ext
    intro x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, blockAct, substAdj, aeval_X, map_sum, map_mul, algHom_C, Matrix.mul_apply]
    simp only [algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [mul_assoc]
  exact congrArg (fun φ => φ P) h

omit [Fintype ι] in
theorem map_blockAct (σ : K →+* L) (g : ι → Matrix (Fin a) (Fin a) K) (P : Pol K ι a) :
    map σ (blockAct K g P) = blockAct L (fun τ => (g τ).map σ) (map σ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [blockAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    simp [blockAct]

theorem map_sharp (σ : K →+* L) (n : ι → ℕ) (P : Pol K ι a) : map σ (sharp n P) = sharp n (map σ P) := by
  simp only [sharp, map_mul, map_prod, map_pow, map_frDet, map_X]
  rfl

theorem blockAct_sharp (g : ι → Matrix (Fin a) (Fin a) K) (n : ι → ℕ) (P : Pol K ι a) :
    blockAct K g (sharp n P) = (∏ τ, (g τ).det ^ n τ) • sharp n (blockAct K g P) := by
  have h : ∀ τ, blockAct K g (frDet K a τ) = C (g τ).det * frDet K a τ := fun τ => by
    have h1 := map_frDet (blockAct K (n := a) g : Pol K ι a →+* Pol K ι a) τ
    rw [RingHom.coe_coe] at h1
    rw [h1, RingHom.map_det, frDet, ← Matrix.det_mul]
    congr 1
    ext1 α t
    simp [blockAct, Matrix.mul_apply]
  simp only [sharp, map_mul, map_prod, map_pow, h, mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul]
  ring

theorem point_int (v : Valuation L Γ) (σ : K →+* L) (hab : a ≤ b) (e s' : ι → ℤ) (n : ι → ℕ)
    (hn : ∀ τ, (n τ : ℤ) = e τ + s' τ) (B : ι → GL (Fin a) K) (BW : ι → GL (Fin b) K)
    (ap : ι → Matrix (Fin a) (Fin b) L)
    (hA : ∀ τ i j, v (((((B τ)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap τ *
      (BW τ : Matrix (Fin b) (Fin b) K).map σ) i j) ≤ 1)
    (F : Pol K ι a) (hF : ∀ m, v (σ (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ e τ) •
      blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F).coeff m)) ≤ 1) :
    ∃ Z : Pol L ι b, (∀ m, v (Z.coeff m) ≤ 1) ∧
      blockAct L (fun τ => (BW τ : Matrix (Fin b) (Fin b) K).map σ) (substAdj hab ap (map σ (sharp n F))) =
        σ (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ) • Z := by
  refine ⟨_, (mem_range_iff v _).mp (substAdj_int v hab _ hA (sharp_int v n ((mem_range_iff v (map σ
    ((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ e τ) •
      blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F))).mpr fun m => by rw [coeff_map]; exact hF m))), ?_⟩
  have h1 : (fun τ => ap τ * (BW τ : Matrix (Fin b) (Fin b) K).map σ) = fun τ =>
      (B τ : Matrix (Fin a) (Fin a) K).map σ * ((((B τ)⁻¹ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K).map σ * ap τ *
      (BW τ : Matrix (Fin b) (Fin b) K).map σ) := by
    funext τ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ σ.map_zero σ.map_one,
      Matrix.one_mul]
  have h2 : (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ n τ) =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ) * ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ e τ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← zpow_add₀ (B τ).det_ne_zero, add_comm, ← hn τ, zpow_natCast]
  rw [blockAct_substAdj, h1, ← substAdj_blockAct, ← map_blockAct, blockAct_sharp, h2, ← map_smul, ← map_sharp]
  congr 1
  simp only [sharp, smul_eq_C_mul, map_mul, map_C]
  ring

end Integral

section Closure

open Formalism.GradedWeylDivisibility (blockAct)

variable {K L Γ : Type} [Field K] [NumberField K] [Field L] [LinearOrderedCommGroupWithZero Γ]

theorem exists_mul_of_approx (w : HeightOneSpectrum (𝓞 K)) (v : Valuation L Γ) (σ : K →+* L)
    (hσ : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) (x c : K)
    (h : ∀ ε : K, ε ≠ 0 → ∃ z : L, v z ≤ 1 ∧ v (σ x - σ c * z) ≤ v (σ ε)) :
    ∃ u : K, w.valuation K u ≤ 1 ∧ x = c * u := by
  have hdiv : ∀ y ε : K, ε ≠ 0 → v (σ y) ≤ v (σ ε) → w.valuation K (y / ε) ≤ 1 := fun y ε hε hy => by
    rw [← hσ, map_div₀, map_div₀]
    exact div_le_one_of_le₀ hy zero_le
  by_cases hc : c = 0
  · subst hc
    refine ⟨0, by simp, ?_⟩
    rw [mul_zero]
    by_contra hx
    obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer K
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact WithZero.exp_ne_zero hπ.symm
    obtain ⟨z, -, hz⟩ := h (x * π) (mul_ne_zero hx hπ0)
    rw [map_zero, zero_mul, sub_zero] at hz
    have h1 := hdiv _ _ (mul_ne_zero hx hπ0) hz
    rw [div_mul_cancel_left₀ hx, map_inv₀, hπ, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  · obtain ⟨z, hz1, hz⟩ := h c hc
    refine ⟨x / c, hdiv _ _ hc ?_, by field_simp⟩
    have h1 : σ x = (σ x - σ c * z) + σ c * z := by ring
    rw [h1]
    refine v.map_add_le hz ?_
    rw [map_mul]
    exact mul_le_of_le_one_right' hz1

theorem closureIntegral : ClosureIntegral := by
  intro K _ _ w L Γ _ _ v σ hσ ι _ a b hab lam lam' s s' n hw M MW B BW hM hMW κ J hJ F hF
  have hmem : jetMap J n (F : Pol K ι a) ∈ VV K lam' :=
    jetMap_mem hab.le n _ _ (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hab lam lam' s s' n hw ap _ F.2) J
  rw [GlobalTheory.HAtBasis.mem_HAt_iff K w ι a lam M B hM] at hF
  set Q := subD K ι a b (sharp n (F : Pol K ι a)) with hQ
  set D := ∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ s' τ with hD
  set T := blockAct K (n := b) (fun τ => (BW τ : Matrix (Fin b) (Fin b) K)) with hT
  set d := fun μ => T (monomial (expL μ) (Q.coeff μ)) with hd
  have hH : T (jetMap J n (F : Pol K ι a)) = ∑ μ ∈ Q.support, J (expR μ) • d μ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [jetMap_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun μ _ => map_smul _ _ _
  have hpt : ∀ ap : ι → Matrix (Fin a) (Fin b) L, admitted v σ M MW ap → ∀ p, ∃ z : L, v z ≤ 1 ∧
      ∑ μ ∈ Q.support, ptTable ap (expR μ) * σ ((d μ).coeff p) = σ D * z := by
    intro ap hap p
    obtain ⟨Z, hZ, hZ'⟩ := point_int v σ hab.le (fun τ => (lam τ).detShift) s' n hw.2.2 B BW ap
      (fun τ => (GlobalTheory.ExtLatMatrix.extLat_matrix_integral K w L Γ v σ hσ).2 a b (M τ) (MW τ) (B τ) (BW τ) (hM τ).2 (hMW τ).2 (ap τ) (hap τ))
      F fun m => (hσ _).mpr (hF m)
    refine ⟨Z.coeff p, hZ p, ?_⟩
    have h1 := congrArg (AddMonoidAlgebra.coeff · p) hZ'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_ptTable, map_sum, coeff_sum, coeff_smul, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [map_smul, coeff_smul, smul_eq_mul, ← map_monomial, ← map_blockAct, coeff_map]
  have hu : ∀ p, ∃ u : K, w.valuation K u ≤ 1 ∧ (T (jetMap J n (F : Pol K ι a))).coeff p = κ * D * u := by
    intro p
    refine exists_mul_of_approx w v σ hσ _ _ fun ε hε => ?_
    obtain ⟨⟨t, ht⟩, htd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) Q.support
      fun μ => (d μ).coeff p
    have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by simpa using nonZeroDivisors.ne_zero ht
    obtain ⟨k, c, ap, hc, hap, happ⟩ := hJ (ε * algebraMap (𝓞 K) K t) (mul_ne_zero hε ht0)
    choose z hz hz' using fun i => hpt (ap i) (hap i) p
    refine ⟨∑ i, c i * z i, v.map_sum_le fun i _ => ?_, ?_⟩
    · rw [map_mul]
      exact mul_le_one' (hc i) (hz i)
    have h1 : σ ((T (jetMap J n (F : Pol K ι a))).coeff p) - σ (κ * D) * ∑ i, c i * z i =
        ∑ μ ∈ Q.support, (σ (J (expR μ)) - σ κ * ∑ i, c i * ptTable (ap i) (expR μ)) * σ ((d μ).coeff p) := by
      have h2 : σ D * ∑ i, c i * z i =
          ∑ μ ∈ Q.support, (∑ i, c i * ptTable (ap i) (expR μ)) * σ ((d μ).coeff p) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_left_comm, ← hz' i, Finset.mul_sum]
        simp only [mul_assoc]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hH, coeff_sum, map_sum, map_mul, mul_assoc, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [coeff_smul, smul_eq_mul, map_mul]
      ring
    rw [h1]
    refine v.map_sum_le fun μ hμ => ?_
    obtain ⟨y, hy⟩ := htd μ hμ
    have h3 : v (σ (algebraMap (𝓞 K) K t * (d μ).coeff p)) ≤ 1 := by
      rw [hσ, ← Algebra.smul_def]
      exact hy ▸ w.valuation_le_one y
    rw [map_mul]
    refine (mul_le_mul_left (happ _ (GlobalTheory.subD_sharp_inDeg K ι a b hab lam lam' s s' n hw _ F.2 μ hμ)) _).trans ?_
    rw [map_mul, map_mul] at h3
    rw [map_mul, map_mul, mul_assoc]
    exact mul_le_of_le_one_right' h3
  have hfac : detFac s s' B BW = D * ∏ τ, (BW τ : Matrix (Fin b) (Fin b) K).det ^ (lam' τ).detShift := by
    simp only [detFac, hD, detShift_eq hw, Finset.prod_mul_distrib]
  have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (B τ).det_ne_zero
  have hW0 : (∏ τ, (BW τ : Matrix (Fin b) (Fin b) K).det ^ (lam' τ).detShift) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (BW τ).det_ne_zero
  by_cases hκ : κ = 0
  · refine ⟨0, zero_mem _, Subtype.ext ?_⟩
    have h0 : T (jetMap J n (F : Pol K ι a)) = 0 := by
      ext p
      obtain ⟨u, -, hu'⟩ := hu p
      rw [hu', hκ, zero_mul, zero_mul, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have h1 := congrArg (blockAct K (n := b) fun τ => (((BW τ)⁻¹ : GL (Fin b) K) : Matrix (Fin b) (Fin b) K)) h0
    rw [map_zero, hT, ← AlgHom.comp_apply, blockAct_comp] at h1
    simp only [Units.mul_inv, blockAct_one, AlgHom.id_apply] at h1
    rw [smul_zero, coe_jetOp _ _ _ _ _ hmem, h1]
    rfl
  · refine ⟨(κ * detFac s s' B BW)⁻¹ • jetOp lam lam' J n F, ?_, ?_⟩
    · rw [GlobalTheory.HAtBasis.mem_HAt_iff K w ι b lam' MW BW hMW]
      intro p
      obtain ⟨u, hu1, hu'⟩ := hu p
      rw [Submodule.coe_smul, coe_jetOp _ _ _ _ _ hmem, map_smul, coeff_smul, coeff_smul, hu', hfac, smul_eq_mul,
        smul_eq_mul]
      convert hu1 using 2
      field_simp
    · rw [smul_inv_smul₀]
      rw [hfac]
      exact mul_ne_zero hκ (mul_ne_zero hD0 hW0)

end Closure

end GlobalTheory.JetPoint
