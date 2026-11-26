module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentLeOfJumpsAtEmbeddingsUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)),
    iotaO O C (ϖ.iB t K f) = dRO l O (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧))) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ C f
  have hS : ∀ τ, ϖ.iSD O K (f τ) = ϖ.iHat O K (GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧)) := fun τ => by
    have hm : ((f τ : invL l (S O K e)) : K⟦X⟧) ∈ Rpi O K l e := invL_S_le_Rpi l e (f τ).2
    refine GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ (f τ) _ ?_
    rw [GlobalTheory.GalStep.hatR_of_mem (O := O) hm]
    exact hat_coe_Rpi l e ⟨_, hm⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PiSys.iB, PiSys.iD, glue_apply, glue_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hI : iotaO O C (idem (constB t) τ) = dRO l O (idem (constD t) τ) :=
    iotaO_toB C (constA t (Pi.single τ 1))
  rw [map_mul, hI, iotaO_iSl ϖ C (f τ), hS, map_mul]
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorInclDeRhamInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.latticeTensorIncl_deRham_injective :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O), Function.Injective (TWincl (dRO l O) T) := by
  intro l _ O K _ _ _ _ _ _ _ T
  classical
  have h0 : Function.Injective (bdRpToBdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  have h1 : Function.Injective (dRO l O) := by
    intro r s h
    let b := Module.Free.chooseBasis ℤ_[l] O
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    apply h0
    rw [← equivFinsuppOfBasisLeft_map_id, ← equivFinsuppOfBasisLeft_map_id]
    exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisLeft b y k) h
  intro w z h
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  apply (TensorProduct.equivFinsuppOfBasisRight bT).injective
  refine Finsupp.ext (fun j => ?_)
  apply h1
  rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
  exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) h
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCoefficientsEqSumOfInverseMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem hat_mulVec' {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
    {ι : Type} [Fintype ι] {Y : Matrix ι ι K⟦X⟧} (hY : ∀ i j, Y i j ∈ RpiE O K l e) {m : ι → K⟦X⟧}
    (hm : ∀ j, m j ∈ RpiE O K l e) (i : ι) :
    hat O l e ((Y *ᵥ m) i) = ∑ j, hat O l e (Y i j) * hat O l e (m j) := by
  have : (Y *ᵥ m) i = ((∑ j, ⟨Y i j, hY i j⟩ * ⟨m j, hm j⟩ : RpiE O K l e) : K⟦X⟧) := by
    simp [Matrix.mulVec, dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [this, hat_coe, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hat_of_mem l e (hY i j), hat_of_mem l e (hm j)]

theorem _root_.UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e),
    (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
    ∀ j, (fun τ => c τ j) = ∑ k, s k * fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P n s m c h j
  funext τ
  apply algebraMap_AhatE_injective l e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h τ j, Finset.sum_apply, map_sum]
  simp only [GlobalTheory.BKGal.JumpDR.hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc (i : ι) : (coordL P (invL l (S O K e)) (m k) i τ : K⟦X⟧) ∈ Rpi O K l e :=
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) (m k) i τ).2
  have hm (i : ι) : (m k).1 τ i ∈ RpiE O K l e := by
    have := congrFun (mx_mulVec_coordL P (invL l (S O K e)) (m k) τ) i
    rw [← this]
    exact Subalgebra.sum_mem _ fun i' _ =>
      mul_mem (invE_A_le_RpiE l e (P.mx_mem τ i i')) (le_away _ _ (hc i'))
  have h1 : (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m k).1 τ) j := rfl
  rw [Pi.mul_apply, map_mul, GlobalTheory.GalStep.hatR_of_mem (hc j), ← hat_coe_Rpi]
  change _ = _ * hat O l e (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)
  rw [h1, hat_mulVec' (fun i i' => invE_A_le_RpiE l e (P.mxInv_mem τ i i')) hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitInvertibleMatrixIdentificationBasis
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsUnitIdentificationSingleIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.tame_identification_unit (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) :
    ∃ u : OA l O, IsUnit (toOD l O u) ∧ ∀ i : ι, ∃ z : TW (OA l O) T,
      I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T z := by
  obtain ⟨⟨ε, hε⟩, hεall⟩ := GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2
  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  refine ⟨ν ^ α, ?_, fun i => ⟨z i, ?_⟩⟩
  · rw [map_pow]
    exact hu.pow α
  · have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← GlobalTheory.DeRhamIdent.inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    rw [hc, hz i]

theorem _root_.UpperTheory.KN.exists_unit_identification_single_integral :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), ∃ u : OA l ↥(OL LL), IsUnit (toOD l ↥(OL LL) u) ∧ ∀ i : ι, ∃ z : TW (OA l ↥(OL LL)) T, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T z := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  exact UpperTheory.KN.tame_identification_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.basis_change_matrices_algebra_map {O R R' M ι : Type} [CommRing O] [CommRing R] [CommRing R']
    [Algebra O R] [Algebra O R'] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq ι]
    (f : R →ₐ[O] R') (b : Module.Basis ι O M) (jD : (ι → R') ≃ₗ[R'] R' ⊗[O] M) (u : R)
    (z : ι → R ⊗[O] M)
    (h : ∀ i, jD (fun j => f ((Pi.single i u : ι → R) j)) =
      TensorProduct.map f.toLinearMap LinearMap.id (z i)) :
    ∃ (m m' : Matrix ι ι R') (r : ι → ι → R), m' * m = 1 ∧ (∀ i, z i = ∑ k, r i k ⊗ₜ[O] b k) ∧
      ∀ i k, f (r i k) = f u * m i k := by
  let bA := Algebra.TensorProduct.basis R b
  let bD := Algebra.TensorProduct.basis R' b
  have hz : ∀ i, z i = ∑ k, bA.repr (z i) k ⊗ₜ[O] b k := by
    intro i
    conv_lhs => rw [← bA.sum_repr (z i)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [bA, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  refine ⟨Matrix.of fun i k => bD.repr (jD (Pi.single i 1)) k, Matrix.of fun k i => jD.symm (bD k) i,
    fun i k => bA.repr (z i) k, ?_, hz, ?_⟩
  · ext k k'
    have h1 : jD.symm (bD k) = ∑ i, jD.symm (bD k) i • (Pi.single i 1 : ι → R') := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 : bD k = ∑ i, jD.symm (bD k) i • jD (Pi.single i 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← jD.apply_symm_apply (bD k), h1, map_sum]
      simp only [map_smul]
    have h3 := congrArg (fun x => bD.repr x k') h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self, Finsupp.single_apply] at h3
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact h3.symm
  · intro i k
    have e1 : (fun j => f ((Pi.single i u : ι → R) j)) = f u • (Pi.single i 1 : ι → R') := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    have e2 : TensorProduct.map f.toLinearMap LinearMap.id (z i) = ∑ k, f (bA.repr (z i) k) • bD k := by
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [hz i, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [bD, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
    have h3 := h i
    rw [e1, e2, map_smul] at h3
    have h4 := congrArg (fun x => bD.repr x k) h3
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_sum_self] at h4
    exact h4.symm

theorem _root_.UpperTheory.KN.exists_unit_invertible_matrix_identification_basis :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (b : Module.Basis ι ↥(OL LL) ↥T.L.T), ∃ (m m' : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) ∧ m' * m = 1 ∧ (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) ∧ ∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I b
  obtain ⟨jD, hjD⟩ := GlobalTheory.DeRhamIdent.main l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I
  obtain ⟨u, hu, hz⟩ := UpperTheory.KN.exists_unit_identification_single_integral l a e ϖ LL ι P T I
  choose z hz using hz
  obtain ⟨m, m', r, h1, h2, h3⟩ := UpperTheory.KN.basis_change_matrices_algebra_map (toOD l ↥(OL LL)) b jD u z
    (fun i => hjD _ _ (hz i))
  refine ⟨m, m', u, r, hu, h1, fun i => (hz i).trans ?_, h3⟩
  exact congrArg (TWincl (inclO l ↥(OL LL)) T) (h2 i)
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrysLatticeBdRPlusActionCompat
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsTensorBdRActionOnLatticeBdR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), ∃ B : OdR l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdR l) (v : T.V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := by
  intro l _ LL T Pl AI Td
  have hz : ∀ z : ℤ_[l], Td.eD.symm (algebraMap ℤ_[l] (Per.BdR l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) :=
    fun z => GlobalTheory.BKGal.JumpDR.cD_algebraMap Td z
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdR l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (Td.eD.symm b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add (f := _), add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdR l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdR l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, hz, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem actDRG {Z Q O P D V R : Type} [CommRing Z] [CommRing Q] [CommRing O] [Algebra Z O]
    [CommRing P] [Algebra Z P] [CommRing D] [Algebra Z D] [AddCommGroup V] [Module Q V]
    [CommRing R] [Algebra Q R] (s : O → V → V) (g : P → D) (cD : P → R) (e : D → R)
    (hg : ∀ b, cD b = e (g b)) (d : O ⊗[Z] P →+ O ⊗[Z] D)
    (hd : ∀ o b, d (o ⊗ₜ[Z] b) = o ⊗ₜ[Z] g b)
    (A : O ⊗[Z] P →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hA : ∀ (o : O) (b : P) (v : V) (c : R), A (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (cD b * c))
    (B : O ⊗[Z] D →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hB : ∀ (o : O) (b : D) (v : V) (c : R), B (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (e b * c))
    (y : O ⊗[Z] P) (w : V ⊗[Q] R) : A y w = B (d y) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [map_add (f := _), AddMonoidHom.add_apply, hx, hx']
    | tmul o b => rw [hd, hA, hB, hg]

private theorem actCrisG {Z Q O P D M V R : Type} [CommRing Z] [CommRing Q] [CommRing O] [Algebra Z O]
    [CommRing P] [Algebra Z P] [CommRing D] [Algebra Z D] [AddCommGroup V] [Module Q V]
    [AddCommGroup M] [Module O M]
    [CommRing R] [Algebra Q R] (s : O → V → V) (hs : ∀ o o' v, s (o * o') v = s o (s o' v))
    (j : M → V) (g : P → D) (cB : P →+* R) (e : D → R)
    (hg : ∀ b, cB b = e (g b)) (d : O ⊗[Z] P →+ O ⊗[Z] D)
    (hd : ∀ o b, d (o ⊗ₜ[Z] b) = o ⊗ₜ[Z] g b)
    (Y : (O ⊗[Z] P) ⊗[O] M →+ V ⊗[Q] R)
    (hY : ∀ (o : O) (b : P) (x : M), Y ((o ⊗ₜ[Z] b) ⊗ₜ[O] x) = (s o (j x)) ⊗ₜ[Q] cB b)
    (B : O ⊗[Z] D →+ (V ⊗[Q] R →+ V ⊗[Q] R))
    (hB : ∀ (o : O) (b : D) (v : V) (c : R), B (o ⊗ₜ[Z] b) (v ⊗ₜ[Q] c) = (s o v) ⊗ₜ[Q] (e b * c))
    (b : O ⊗[Z] P) (z : (O ⊗[Z] P) ⊗[O] M) : Y (b • z) = B (d b) (Y z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add v w hv hw => simp only [smul_add, map_add (f := _), hv, hw]
  | tmul u x =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    induction b using TensorProduct.induction_on with
    | zero => simp only [zero_mul, zero_tmul, map_zero, AddMonoidHom.zero_apply]
    | add y y' hy hy' => simp only [add_mul, add_tmul, map_add (f := _), AddMonoidHom.add_apply, hy, hy']
    | tmul o' b' =>
      induction u using TensorProduct.induction_on with
      | zero => simp only [mul_zero, zero_tmul, map_zero]
      | add y y' hy hy' => simp only [mul_add, add_tmul, map_add (f := _), hy, hy']
      | tmul o b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hY, hY, hd, hB, map_mul, hs, hg b']

private theorem hcB {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (C : GlobalTheory.MemLoc.Core l) (β : Per.Bcris l) : GlobalTheory.BKGal.JumpDR.cB Td β = Td.eD.symm (C.ι β) := by
  have e0 := GlobalTheory.FundSeq.eq_core_of_isCrisDR Td.incl C
  rw [← e0]
  exact (Td.eD.symm_apply_apply _).symm

private theorem hcD {l : ℕ} [Fact l.Prime] {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (β : Per.BdRp l) : GlobalTheory.BKGal.JumpDR.cD Td β = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) β) := rfl

private theorem hdR {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (b : Per.BdRp l) :
    dRO l O (o ⊗ₜ[ℤ_[l]] b) = o ⊗ₜ[ℤ_[l]] algebraMap (Per.BdRp l) (Per.BdR l) b := rfl

private theorem hio {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (o : O) (b : Per.Bcris l) :
    iotaO O C (o ⊗ₜ[ℤ_[l]] b) = o ⊗ₜ[ℤ_[l]] C.ι b := rfl

private theorem mainG {l : ℕ} [Fact l.Prime] {O M V : Type} [CommRing O] [Algebra ℤ_[l] O]
    [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup M] [Module O M]
    {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)
    (s : O → V → V) (hs : ∀ o o' v, s (o * o') v = s o (s o' v)) (j : M → V)
    (Y : OB l O ⊗[O] M →+ V ⊗[ℚ_[l]] Pl.R.BdR)
    (hY : ∀ (o : O) (b : Per.Bcris l) (x : M), Y ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[O] x) = (s o (j x)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b)
    (act : OD l O →+ (V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR))
    (hact : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (s o v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (B : OdR l O →+ (V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR))
    (hB : ∀ (o : O) (b : Per.BdR l) (v : V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (s o v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c))
    (C : GlobalTheory.MemLoc.Core l) (b : OB l O) (y : OD l O) (hby : iotaO O C b = dRO l O y) (z : OB l O ⊗[O] M) :
    Y (b • z) = act y (Y z) := by
  have h1 : act y (Y z) = B (dRO l O y) (Y z) :=
    actDRG s (algebraMap (Per.BdRp l) (Per.BdR l))
      (GlobalTheory.BKGal.JumpDR.cD Td) Td.eD.symm (hcD Td) (AddMonoidHom.mk' (dRO l O) (map_add _))
      hdR act hact B hB y (Y z)
  have h2 : Y (b • z) = B (iotaO O C b) (Y z) :=
    actCrisG s hs j C.ι
      (GlobalTheory.BKGal.JumpDR.cB Td) Td.eD.symm (hcB Td C) (AddMonoidHom.mk' (iotaO O C) (map_add _))
      (hio C) Y hY B hB b z
  exact h2.trans (hby ▸ h1.symm)

theorem _root_.UpperTheory.KN.crysLattice_bdRPlus_action_compat :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (Y : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), Y ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) →
    ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)),
    (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) →
    ∀ (C : GlobalTheory.MemLoc.Core l) (b : OB l ↥(OL LL)) (y : OD l ↥(OL LL)), iotaO ↥(OL LL) C b = dRO l ↥(OL LL) y → ∀ z : TW (OB l ↥(OL LL)) T, Y (b • z) = act y (Y z) := by
  intro l _ LL T Pl AI Td Y hY act hact C b y hby z
  obtain ⟨B, hB⟩ := UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR l LL T Pl AI Td
  exact mainG Td (fun (o : ↥(OL LL)) (v : T.V) => (o : ↥LL.1) • v)
    (fun o o' v => mul_smul (o : ↥LL.1) (o' : ↥LL.1) v) (fun x : ↥T.L.T => (x : T.V)) Y hY act hact B hB C b y hby z
end
