module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrisms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizer
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCrystallineComparisonOfIsCrisCmp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationJumpsBreuilKisinSubsetGaloisJumps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorDeRhamCrysRelationGaloisStable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private noncomputable def gdR {l : ℕ} [Fact l.Prime] (g : GQ l) : Per.BdR l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := Per.σD g
  commutes' z := (GlobalTheory.MemLoc.FilLaws.σD_alg g (algebraMap ℤ_[l] (Per.BdRp l) z)).trans
    (congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) ((GlobalTheory.GalStep.galD g).commutes z))

private noncomputable def gOdR {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) :
    OdR l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (gdR g)

private theorem gOdR_dRO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OD l O) :
    gOdR O g (dRO l O x) = dRO l O (GlobalTheory.GalStep.galOD O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.MemLoc.FilLaws.σD_alg g w)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem gOdR_iotaO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (g : GQ l) (x : OB l O) :
    gOdR O g (iotaO O C x) = iotaO O C (galOB O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.BKGal.FilStable.ι_σB C g w).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem act_incl {O G Qp LL R R' : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (i : R →ₐ[O] R') (f : R →ₐ[O] R) (f' : R' →ₐ[O] R') (h : ∀ r, f' (i r) = i (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWact f' T g (TWincl i T z) = TWincl i T (TWact f T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem _root_.UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (g : Gl l) (y : TW (OD l O) T) (b : TW (OB l O) T) (x : OD l O),
    TWincl (dRO l O) T y = dRO l O x • TWincl (iotaO O C) T b →
    TWincl (dRO l O) T (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g y) =
      dRO l O (GlobalTheory.GalStep.galOD O (sQ l g) x) • TWincl (iotaO O C) T (TWact (galOB O (sQ l g)) T g b) := by
  intro l _ O K _ _ _ _ _ _ _ T C g y b x h
  have h1 := act_incl (dRO l O) (GlobalTheory.GalStep.galOD O (sQ l g)) (gOdR O (sQ l g)) (gOdR_dRO O (sQ l g)) T g y
  have h2 := act_incl (iotaO O C) (galOB O (sQ l g)) (gOdR O (sQ l g)) (gOdR_iotaO O C (sQ l g)) T g b
  have h3 := GlobalTheory.GalStep.TWact_smul_of (gOdR O (sQ l g)) T g (dRO l O x) (TWincl (iotaO O C) T b)
  have h4 := gOdR_dRO O (sQ l g) x
  refine h1.symm.trans ((congrArg (TWact (gOdR O (sQ l g)) T g) h).trans (h3.trans ?_))
  rw [h4, h2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyOperatorMapsIntoCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinGaloisScalesDeRhamPeriodsByUnitPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T)
    (ε : OCb l) (hε : IsEps ε) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz t ϖ (sQ l) P jB)
    (hjD : ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z)
    (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (v : OD l O)
    (hv : GlobalTheory.GalStep.galOD O (sQ l g) (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v) (d : P.D) :
    jD.symm (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g (jD (GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • P.xi d)))) =
      v ^ α • GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • P.xi d) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have hd : P.xi d ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 (cst d)).2
    (GlobalTheory.GalStep.cst_mem_Mext P d)
  have h1 := UpperTheory.KN.phiMod_crystalline_comparison_of_isCrisCmp l a e O K t ϖ ι P T I jB jD C ε hε hCmp hjD α hα ⟨P.xi d, hd⟩
  have h2 := UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable l O K T C g _ _ (GlobalTheory.GalStep.ED K t ϖ ^ α) (h1.trans (by rw [map_pow]))
  have h3 : TWact (galOB O (sQ l g)) T g (jB (toBcris t ϖ P ⟨P.xi d, hd⟩)) =
      jB (toBcris t ϖ P ⟨P.xi d, hd⟩) := hHor g hg d hd
  rw [h3, map_pow, hv, mul_pow, mul_comm, map_mul, mul_smul, map_pow (dRO l O) (GlobalTheory.GalStep.ED K t ϖ), ← h1,
    ← BasisCoord.tWincl_smul'] at h2
  have h4 := UpperTheory.KN.latticeTensorIncl_deRham_injective l O K T h2
  rw [← jD.map_smul] at h4
  exact (congrArg jD.symm h4).trans (jD.symm_apply_apply _)

theorem _root_.GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ v : OD l ↥(OL LL), GlobalTheory.GalStep.galOD ↥(OL LL) (sQ l g) (GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ) = GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ * v → ∀ d : P.D, GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xi d)) = v ^ α • GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xi d) := by
  intro _ l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI _ hCmp hHor jD hjD α hα g hg v hv d
  obtain ⟨-, ε, -, hε, -⟩ := GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer l a e ϖ hl2
  exact gen (thetaW a LL) ϖ P T I jB jD ε hε hCmp hHor hjD α hα g hg v hv d
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

section Scal

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem galOD_crisToOD (g : GQ l) (x : OCr l O) :
    galOD O g (crisToOD l O x) = crisToOD l O (galOCr O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w =>
    exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y)
      ((GlobalTheory.MemLoc.crisP_unique_equivariant l (crisP l) (isCrisP_crisP l)).2.1 g w).symm
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isUnit_natCast_OD {n : ℕ} (hn : n ≠ 0) : IsUnit (n : OD l O) := by
  have h0 : ((n : ℕ) : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  have h1 := congrArg (algebraMap ℤ_[l] (OD l O)) (PadicInt.unitCoeff_spec h0)
  rw [map_natCast, map_mul, map_pow, map_natCast] at h1
  rw [h1]
  exact ((PadicInt.unitCoeff h0).isUnit.map _).mul (isUnit_l_OD.pow _)

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]


variable (O K) in
theorem dvd_toOD_mu (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) :
    ϖ.iAl O K (EIn l e _) ∣ toOD l O (1 ⊗ₜ ϖ.mu g) := by
  have hξ : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  have hmem : ϖ.mu g ∈ Ideal.span {ϖ.ev 1 (eis l 1 e)} := by
    rw [ϖ.span_ev_eis 1]
    exact ϖ.theta_mu (ϖ.gal_pi a g)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨1 ⊗ₜ ainfToBdRp l c, ?_⟩
  rw [hξ, ← hc]
  change (1 : O) ⊗ₜ[ℤ_[l]] ainfToBdRp l (c * _) = _
  rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]


variable (O) in
theorem crisToOD_muDiv (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    crisToOD l O (ϖ.muDiv a O g i) = toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) := by
  have h1 := congrArg (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O)
    (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
  rw [map_mul, map_natCast, map_pow] at h1
  have h2 := congrArg (crisToOD l O) h1
  rw [map_mul, map_natCast, map_pow, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.includeRight_apply, ← toOCr_tmul, crisToOD_toOCr] at h2
  have hu := isUnit_natCast_OD (l := l) (O := O) i.factorial_ne_zero
  rw [← h2, mul_comm, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rfl


variable (K) in
theorem taylor_S_mod (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (s : S O K e) (R : ℕ) :
    ϖ.iAl O K (EIn l e _) ^ R ∣ galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
  obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ R
  refine GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ R _ fun k => ?_
  obtain ⟨M₀, hM₀⟩ := ϖ.taylor_S a O K g s (N + k)
  obtain ⟨z, hz⟩ := hM₀ (max M₀ R) (le_max_left _ _)
  obtain ⟨y, hy⟩ := hN z
  refine ⟨y, ?_⟩
  have hz' := congrArg (crisToOD l O) hz
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, map_mul, map_pow, map_natCast, crisToOD_muDiv] at hz'
  rw [← galOD_crisToOD, ← Finset.sum_range_add_sum_Ico _ (le_max_right M₀ R)] at hz'
  have key : galOD O g (crisToOD l O (ϖ.iS O K s)) -
      ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) - (l : OD l O) ^ k * toOD l O y =
      (l : OD l O) ^ k * ((l : OD l O) ^ N * crisToOD l O z - toOD l O y) +
        ∑ i ∈ Finset.Ico R (max M₀ R), toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    linear_combination hz'
  rw [key]
  refine dvd_add (Dvd.dvd.mul_left hy _) (Finset.dvd_sum fun i hi => ?_)
  have hi' : R ≤ i := (Finset.mem_Ico.1 hi).1
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right ((pow_dvd_pow _ hi').trans
    (pow_dvd_pow_of_dvd (dvd_toOD_mu O K ϖ g) i)) _) _

end Scal

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

section Scal2

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [TameDescentExponentData K l e a] [CompleteSpace K]

theorem taylor_invL_mod (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) {f : K⟦X⟧}
    (hf : f ∈ invL l (S O K e)) (R : ℕ) :
    galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i *
      Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f)) ∈
      Ideal.span {ϖ.iAl O K (EIn l e _) ^ R} := by
  have hiHat : ∀ (f' : K⟦X⟧) (hf' : f' ∈ invL l (S O K e)), ϖ.iHat O K (hatR O f') = ϖ.iSD O K ⟨f', hf'⟩ :=
    fun f' hf' => (GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ ⟨f', hf'⟩ (hatR O f') (by
      rw [hatR_of_mem (O := O) (invL_S_le_Rpi l e hf')]
      exact hat_coe_Rpi l e ⟨f', invL_S_le_Rpi l e hf'⟩)).symm
  obtain ⟨n, hn⟩ := hf
  have hC : ((l : S O K e) : K⟦X⟧) ^ n = C ((l : K) ^ n) := by simp
  have hlin : ∀ (i : ℕ) (x : K⟦X⟧), ((l : S O K e) : K⟦X⟧) ^ n * descN K i x =
      descN K i (((l : S O K e) : K⟦X⟧) ^ n * x) := fun i x => by
    rw [hC, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  have hdesc : ∀ i : ℕ, descN K i f ∈ invL l (S O K e) := fun i =>
    ⟨n, by rw [hlin]; exact descN_mem_S e i hn⟩
  set s : S O K e := ⟨_, hn⟩ with hs
  have e0 : (l : OD l O) ^ n * ϖ.iSD O K ⟨f, ⟨n, hn⟩⟩ = crisToOD l O (ϖ.iS O K s) := by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨f, ⟨n, hn⟩⟩ = algebraMap (S O K e) (invL l (S O K e)) s :=
      Subtype.ext (by simp [s])
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K s.2 _
  have ei : ∀ i : ℕ, (l : OD l O) ^ n * ϖ.iSD O K ⟨descN K i f, hdesc i⟩ =
      crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := fun i => by
    have h1 : (l : invL l (S O K e)) ^ n * ⟨descN K i f, hdesc i⟩ =
        algebraMap (S O K e) (invL l (S O K e)) ⟨descN K i s, descN_mem_S e i s.2⟩ :=
      Subtype.ext (by
        change ((l : K⟦X⟧)) ^ n * descN K i f = descN K i (((l : S O K e) : K⟦X⟧) ^ n * f)
        rw [← hlin]
        simp)
    have h2 := congrArg (ϖ.iSD O K) h1
    rw [map_mul, map_pow, map_natCast] at h2
    rw [h2]
    exact ϖ.iSD_of_mem O K (descN_mem_S e i s.2) _
  have g0 := congrArg (galOD O g) e0
  rw [map_mul, map_pow, map_natCast] at g0
  have key : (l : OD l O) ^ n * (galOD O g (ϖ.iHat O K (hatR O f)) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iHat O K (hatR O (descN K i f))) =
      galOD O g (crisToOD l O (ϖ.iS O K s)) -
        ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          crisToOD l O (ϖ.iS O K ⟨descN K i s, descN_mem_S e i s.2⟩) := by
    rw [hiHat f ⟨n, hn⟩, ← g0, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hiHat _ (hdesc i), ← ei i]
    ring
  have hW := Ideal.mem_span_singleton.2 (taylor_S_mod K ϖ g s R)
  rw [← key] at hW
  exact (Ideal.unit_mul_mem_iff_mem _ (isUnit_l_OD.pow n)).1 hW

theorem galOD_idem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (τ : ZMod a) :
    galOD O g (idem (constD t) τ) = idem (constD t) τ := by
  have h : ∀ x ∈ Kunr l a, (g : GQ l) x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (ϖ.Kunr_le_field a hx)
  change galOD O g (toOD l O (constA t _)) = toOD l O (constA t _)
  rw [← crisToOD_toOCr, galOD_crisToOD, galOCr_toOCr, galOA_constA t h]

end Scal2

theorem taylor_iD_mod_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ g hg f hf R
  let g' : ↥(GK (ϖ.field a)) := ⟨g, hg⟩
  have hED : ED K t ϖ = ϖ.iAl O K (EIn l e _) := (glue_const _ _ _).trans (ϖ.iHat_ofAl O K _)
  rw [hED]
  have hfix : ∀ τ, galOD O g (idem (constD t) τ) = idem (constD t) τ := galOD_idem t ϖ g'
  have hsplit : galOD O g (ϖ.iD t K (fun τ => hatR O (f τ))) - ∑ i ∈ Finset.range R,
      toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
        ϖ.iD t K (fun τ => hatR O (descN K i (f τ))) =
      ∑ τ, idem (constD t) τ * (galOD O g (ϖ.iHat O K (hatR O (f τ))) - ∑ i ∈ Finset.range R,
        toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) *
          ϖ.iHat O K (hatR O (descN K i (f τ)))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [PiSys.iD, glue_apply, map_sum, map_mul, hfix, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  exact Ideal.sum_mem _ fun τ _ => Ideal.mul_mem_left _ _ (taylor_invL_mod t ϖ g' (hf τ) R)

end GlobalTheory.GalStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_formula_pi_invPrime_mod_eisenstein_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ invL l (S O K e)) → ∀ R : ℕ, GlobalTheory.GalStep.galOD O g (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ))) - ∑ i ∈ Finset.range R, toOD l O (1 ⊗ₜ ϖ.mu g) ^ i * Ring.inverse (i.factorial : OD l O) * ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (descN K i (f τ))) ∈ Ideal.span {GlobalTheory.GalStep.ED K t ϖ ^ R} := by
  first | exact @GlobalTheory.GalStep.taylor_iD_mod_ED | exact GlobalTheory.GalStep.taylor_iD_mod_ED | (intros; apply GlobalTheory.GalStep.taylor_iD_mod_ED <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem teich_pow_sub_one_eq_ED_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ε c hε hc
  have hd : ED K t ϖ = toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) := by
    rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨⟨ξ, hξ, hμ⟩, -, hθδ, -⟩ := (GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)
  set G : Ainf l := ∑ i ∈ Finset.range c, WittVector.teichmuller l ε ^ i with hG
  set w : Ainf l := (v : Ainf l) * (muOf δ * G) with hwdef
  have hkey : WittVector.teichmuller l ε ^ c - 1 = ϖ.ev a (eis l a e) * w := by
    have h1 : WittVector.teichmuller l ε ^ c - 1 = muOf ε * G := by
      rw [muOf, hG, mul_comm, geom_sum_mul]
    rw [h1, hμ, ← hv, hwdef]
    ring
  have hθG : ((Per.θ l G : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hG, map_sum]
    simp only [map_pow, WittVector.fontaineTheta_teichmuller, hε.1, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  have hθw : ((Per.θ l w : Per.OC l) : ℂ_[l]) ≠ 0 := by
    have h1 : ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
      (v.isUnit.map (Per.θ l)).ne_zero (Subtype.ext (h.trans rfl))
    have h2 : ((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h => hθδ (Subtype.ext (h.trans rfl))
    have h3 : (c : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc
    have h4 : ((Per.θ l w : Per.OC l) : ℂ_[l]) =
        ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) * (((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) *
          ((Per.θ l G : Per.OC l) : ℂ_[l])) := by
      rw [hwdef, map_mul, map_mul]
      rfl
    rw [h4, hθG]
    exact mul_ne_zero h1 (mul_ne_zero h2 h3)
  have hwu : IsUnit (ainfToBdRp l w) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
    change Per.θD l (GlobalTheory.MemLoc.aDp l w) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact hθw)
  refine ⟨toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O), ?_, ?_⟩
  · have h2 : toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O) =
        (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O) (ainfToBdRp l w) := by
      simp [toOD]
    rw [h2]
    exact hwu.map _
  · have h3 : ((1 : O) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ε : OA l O) ^ c - 1 =
        ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) * ((1 : O) ⊗ₜ[ℤ_[l]] w) := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hkey,
        Algebra.TensorProduct.one_def, TensorProduct.tmul_sub]
    rw [hd, ← map_mul, ← h3, map_sub, map_pow, map_one]

end GlobalTheory.GalStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  first | exact @GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul | exact GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul | (intros; apply GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMemStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfEvalNatCastAdd
namespace GlobalTheory.EvalNatCastZero

open Polynomial

theorem eq_zero_of_eval_natCast_add {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (n : ℕ) (F : Polynomial R) (hF : F.natDegree ≤ n)
    (m : ℕ) (h : ∀ k : ℕ, Polynomial.eval ((m + k : ℕ) : R) F = 0) : F = 0 := by
  nontriviality R
  induction n generalizing F m with
  | zero =>
    have h0 := h 0
    rw [eq_C_of_natDegree_le_zero hF] at h0 ⊢
    rw [eval_C] at h0
    rw [h0, C_0]
  | succ n ih =>
    have hroot : F.IsRoot (m : R) := by simpa using h 0
    have hfac : (X - C (m : R)) * (F /ₘ (X - C (m : R))) = F :=
      mul_divByMonic_eq_iff_isRoot.2 hroot
    have hdeg : (F /ₘ (X - C (m : R))).natDegree ≤ n := by
      rw [natDegree_divByMonic F (monic_X_sub_C _), natDegree_X_sub_C]
      omega
    have hG : F /ₘ (X - C (m : R)) = 0 := by
      refine ih _ hdeg (m + 1) fun k => ?_
      have h1 := h (k + 1)
      rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h1
      have e1 : ((m + (k + 1) : ℕ) : R) - (m : R) = ((k + 1 : ℕ) : R) := by push_cast; ring
      have e2 : m + 1 + k = m + (k + 1) := by ring
      rw [e1] at h1
      rw [e2]
      exact (hR (k + 1) (Nat.succ_ne_zero k)).mul_right_eq_zero.1 h1
    rw [← hfac, hG, mul_zero]

end GlobalTheory.EvalNatCastZero
end

open Polynomial

namespace GlobalTheory.FilCoeff

theorem poly_eq_zero_of_eval_nat {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) :
    ∀ (n : ℕ) (F : R[X]), F.natDegree ≤ n → ∀ m : ℕ,
      (∀ k : ℕ, F.eval ((m + k : ℕ) : R) = 0) → F = 0 := by
  first
  | exact @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add
  | (apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EvalNatCastZero.eq_zero_of_eval_natCast_add ..)

noncomputable def binPoly {R : Type} [CommRing R] (y : R) (s : ℕ) : R[X] :=
  ∑ j ∈ Finset.range s, C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j

theorem eval_binPoly {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (k : ℕ) :
    (binPoly y s).eval ((k : ℕ) : R) = (1 + y) ^ k := by
  have hterm : ∀ j ∈ Finset.range s,
      eval ((k : ℕ) : R) (C (y ^ j * Ring.inverse ((j.factorial : ℕ) : R)) * descPochhammer R j)
        = y ^ j * ((k.choose j : ℕ) : R) := by
    intro j _
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial,
      Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc, ← mul_assoc (Ring.inverse _),
      Ring.inverse_mul_cancel _ (hR _ (Nat.factorial_ne_zero j)), one_mul]
  rw [binPoly, eval_finsetSum, Finset.sum_congr rfl hterm, add_comm, add_pow]
  simp only [one_pow, mul_one]
  have h1 : ∑ j ∈ Finset.range s, y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [pow_eq_zero_of_le hj hy, zero_mul]
  have h2 : ∑ j ∈ Finset.range (k + 1), y ^ j * ((k.choose j : ℕ) : R)
      = ∑ j ∈ Finset.range (s + k + 1), y ^ j * ((k.choose j : ℕ) : R) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    rw [Finset.mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
  rw [h1, h2]

theorem smul_coeff_one_eq_zero {R : Type} [CommRing R] (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (y : R) (s : ℕ) (hy : y ^ s = 0) (c : ℕ → R)
    (h : ∀ k : ℕ, ∑ i ∈ Finset.range s, ((1 + y) ^ k - 1) ^ i * c i = 0) :
    y * c 1 = 0 := by
  rcases s with _ | _ | t
  · have h1 : (1 : R) = 0 := by simpa using hy
    calc y * c 1 = y * c 1 * 1 := (mul_one _).symm
      _ = 0 := by rw [h1, mul_zero]
  · rw [zero_add, pow_one] at hy; rw [hy, zero_mul]
  set P : R[X] := binPoly y (t + 2) - 1 with hPdef
  have hP : ∀ k : ℕ, P.eval ((k : ℕ) : R) = (1 + y) ^ k - 1 := by
    intro k; rw [hPdef, eval_sub, eval_one, eval_binPoly hR y _ hy k]
  set F : R[X] := ∑ i ∈ Finset.range (t + 2), P ^ i * C (c i) with hFdef
  have hF : F = 0 := by
    apply poly_eq_zero_of_eval_nat hR F.natDegree F le_rfl 0
    intro k
    rw [zero_add, hFdef, eval_finsetSum]
    simp only [eval_mul, eval_pow, eval_C, hP]
    exact h k
  have h0 : P.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]; simpa using hP 0
  obtain ⟨Q, hQ⟩ := X_dvd_iff.2 h0
  have hF1 : F.coeff 1 = Q.coeff 0 * c 1 := by
    rw [hFdef, finsetSum_coeff]
    simp only [coeff_mul_C, hQ, mul_pow, coeff_X_pow_mul']
    rw [Finset.sum_eq_single 1]
    · simp
    · intro i _ hi
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · have : i = 0 := by omega
        subst this; simp [coeff_one]
      · rw [if_neg (by omega), zero_mul]
    · intro hn; exact absurd (Finset.mem_range.2 (by omega)) hn
  have hL : P.coeff 1 = Q.coeff 0 := by rw [hQ, coeff_X_mul]
  have hL2 : P.coeff 1 = y * (1 + (∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
    rw [hPdef, coeff_sub, coeff_one, if_neg one_ne_zero, sub_zero, binPoly, finsetSum_coeff]
    simp only [coeff_C_mul]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [zero_add, pow_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      Ring.inverse_one, descPochhammer_one, descPochhammer_zero, coeff_X_one, coeff_one,
      if_neg one_ne_zero, mul_zero, add_zero, mul_one, one_mul]
    have e : ∀ j ∈ Finset.range t, y ^ (j + 1 + 1) * Ring.inverse (((j + 1 + 1).factorial : ℕ) : R)
        * (descPochhammer R (j + 1 + 1)).coeff 1
        = y * ((y ^ j * Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) := by
      intro j _; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hnil : IsNilpotent ((∑ j ∈ Finset.range t, y ^ j *
      Ring.inverse (((j + 2).factorial : ℕ) : R) * (descPochhammer R (j + 2)).coeff 1) * y) :=
    (Commute.all _ y).isNilpotent_mul_left ⟨_, hy⟩
  have hc := congrArg (fun G : R[X] => G.coeff 1) hF
  simp only [hF1, coeff_zero] at hc
  rw [← hL, hL2, mul_comm, ← mul_assoc, mul_comm (c 1), mul_comm _ (1 + _)] at hc
  have := (hnil.isUnit_one_add).mul_right_eq_zero.1 hc
  rw [mul_comm] at this ⊢; exact (mul_comm (c 1) y) ▸ this

theorem d_mul_x_one_mem_span_pow :
    ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u →
      q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B),
      (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i
        ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  intro B _ hB d q u hu hq s x hx
  set I : Ideal B := Ideal.span {d ^ s} with hI
  have hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B ⧸ I) := fun n hn => by
    simpa using (hB n hn).map (Ideal.Quotient.mk I)
  have hy : (Ideal.Quotient.mk I q - 1) ^ s = 0 := by
    rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      mul_pow]
    exact I.mul_mem_right _ (Ideal.subset_span rfl)
  have key := smul_coeff_one_eq_zero hR (Ideal.Quotient.mk I q - 1) s hy
    (fun i => Ideal.Quotient.mk I (Ring.inverse (i.factorial : B) * x i)) (by
      intro k
      rw [add_sub_cancel]
      have := (Ideal.Quotient.eq_zero_iff_mem).2 (hx k)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      simpa only [map_mul, map_pow, map_sub, map_one, mul_assoc] using this)
  simp only [Nat.factorial_one, Nat.cast_one, Ring.inverse_one, one_mul] at key
  rw [← map_one (Ideal.Quotient.mk I), ← map_sub, hq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at key
  obtain ⟨v, rfl⟩ := hu
  have : d * x 1 = d * ↑v * x 1 * ↑v⁻¹ := by
    rw [mul_right_comm d, mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact I.mul_mem_right _ key

end GlobalTheory.FilCoeff
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_difference_ideal_power_mem : ∀ (B : Type) [CommRing B], (∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) → ∀ (d q u : B), IsUnit u → q - 1 = d * u → ∀ (s : ℕ) (x : ℕ → B), (∀ k : ℕ, ∑ i ∈ Finset.range s, (q ^ k - 1) ^ i * Ring.inverse (i.factorial : B) * x i ∈ Ideal.span {d ^ s}) → d * x 1 ∈ Ideal.span {d ^ s} := by
  first | exact @GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | exact GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow | (intros; apply GlobalTheory.FilCoeff.d_mul_x_one_mem_span_pow <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnit
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem ED_nzd_and_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e),
    (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ
  refine ⟨fun y hy => ?_, fun n hn => ?_⟩
  · have hd : ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
      rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
      exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
    set d := GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))
    have hinj : Function.Injective (LinearMap.mulLeft ℤ_[l] d) := by
      intro x z hxz
      rw [← sub_eq_zero]
      apply GlobalTheory.BKReal.HatDescent.aDp_ev_eis_mul_eq_zero (a := a) ϖ
      simp only [LinearMap.mulLeft_apply] at hxz
      rw [mul_sub, hxz, sub_self]
    have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := O) _ hinj
    have hmul : ∀ z : OD l O, (LinearMap.mulLeft ℤ_[l] d).lTensor O z = ((1 : O) ⊗ₜ[ℤ_[l]] d) * z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul o β => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add x w hx hw => rw [map_add (f := _), hx, hw, mul_add]
    apply hT
    rw [hmul, map_zero, ← hd, hy]
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).one_lt.ne'
    have hmu : IsUnit (m : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
    have hmu' : IsUnit (m : OD l O) := by
      simpa only [map_natCast] using hmu.map (algebraMap ℤ_[l] (OD l O))
    rw [Nat.cast_mul, Nat.cast_pow]
    exact (isUnit_l_OD.pow k).mul hmu'

end GlobalTheory.GalStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnitStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  first | exact @GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | exact GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | (intros; apply GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlus
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

theorem ED_eq (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e)) := by
  rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))

theorem σA_ev_eis_eq {e : ℕ} [NeZero e] (ϖ : PiSys l e) (g : GQ l) :
    ∃ u : Ainf l, IsUnit u ∧ Per.σA g (ϖ.ev 1 (eis l 1 e)) = ϖ.ev 1 (eis l 1 e) * u := by
  set d := ϖ.ev 1 (eis l 1 e) with hd
  have hdvd : ∀ h : GQ l, d ∣ Per.σA h d := fun h => by
    rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA, ϖ.theta_ev_eis 1, map_zero]
  obtain ⟨u, hu⟩ := hdvd g
  obtain ⟨u', hu'⟩ := hdvd g⁻¹
  by_cases hd0 : d = 0
  · refine ⟨1, isUnit_one, ?_⟩
    rw [hd0, map_zero, zero_mul]
  · refine ⟨u, ?_, hu⟩
    have h1 : d = d * (u * Per.σA g u') := by
      calc d = Per.σA g (Per.σA g⁻¹ d) := by rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one]
        _ = d * (u * Per.σA g u') := by rw [hu', map_mul, hu, mul_assoc]
    have h2 : u * Per.σA g u' = 1 := by
      have h3 : d * (u * Per.σA g u' - 1) = 0 := by rw [mul_sub, ← h1, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hd0)
    exact IsUnit.of_mul_eq_one _ h2

end GlobalTheory.GalStep


open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.galOD_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g _
  obtain ⟨u, hu, hσ⟩ := σA_ev_eis_eq ϖ g
  refine ⟨(1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l u, ?_, ?_⟩
  · exact hu.map ((Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O).comp (ainfToBdRp l))
  · rw [ED_eq a e O K t ϖ]
    change (1 : O) ⊗ₜ[ℤ_[l]] Per.σDp g (GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e))) = _
    rw [GlobalTheory.MemLoc.ActLaws.σDp_aDp, hσ, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  first | exact @GlobalTheory.GalStep.galOD_ED | exact GlobalTheory.GalStep.galOD_ED | (intros; apply GlobalTheory.GalStep.galOD_ED <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.taylor_rho : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ v : OD l ↥(OL LL), IsUnit v ∧ ∀ w ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)), ∀ (R : ℕ) (j : ι), GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt w)) j - v ^ α * ∑ i ∈ Finset.range R, toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL)) * GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (w τ k))) j ∈ Ideal.span {GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ ^ R} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg
  obtain ⟨v, hv, hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg
  refine ⟨v, hv, fun w hw R j => ?_⟩
  exact taylor_vec (thetaW a LL) ϖ P α (descN_mem_Mext P) (E_pow_xiExt_mem_Man P α hα)
    (galOD ↥(OL LL) (sQ l g)) (rhoDHom T jD g) (rhoD_smul T jD g) (v ^ α)
    (GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg v hED)
    (fun i => toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL))) R _
    (fun f hf => GlobalTheory.T.taylor_formula_pi_invPrime_mod_eisenstein_pow l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg f hf R) hw j


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.key_sums (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (hl2 : l ≠ 2) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (hStd : IsStd Pl AI) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz (thetaW a LL) ϖ (sQ l) P jB) (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (hjD : ∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z)
    (α b : ℕ) (hα : ∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (ε : OCb l) (c : ℕ)
    (hk : ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k)) {m : Vec ↥LL.1 a ι} (hm : m ∈ P.M)
    {wx : Vec ↥LL.1 a ι} (hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e))) (hwxdef : P.xiExt wx = E ↥LL.1 l e ^ b • m) (j : ι)
    (k : ℕ) : ∑ i ∈ Finset.range (α + b), ((toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1) ^ i *
      Ring.inverse (i.factorial : OD l ↥(OL LL)) *
      YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
  have hgk : sQ l (g ^ k) ∈ GK (ϖ.field a) := by rw [map_pow]; exact Subgroup.pow_mem _ hg k
  obtain ⟨v, hv, htay⟩ := taylor_rho hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα (g ^ k) hgk
  have h1 := htay wx hwx (α + b) j
  obtain ⟨v', hv', hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l (g ^ k)) hgk
  have hxe : E ↥LL.1 l e ^ α • P.xiExt wx = E ↥LL.1 l e ^ (α + b) • m := by
    rw [hwxdef, smul_smul, ← pow_add]
  have h2 : rhoD T jD (g ^ k) (YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt wx)) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
    rw [hxe, YD_E_pow_smul (thetaW a LL) ϖ (P.M_le_Man hm) (α + b), rhoD_smul, Pi.smul_apply, smul_eq_mul, map_pow,
      hED, mul_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h3 : toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l (g ^ k))) = (toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1 := by
    rw [PiSys.mu, hk k, TensorProduct.tmul_sub, map_sub, ← Algebra.TensorProduct.one_def, map_one,
      ← pow_mul, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow, map_pow (WittVector.teichmuller l)]
  rw [h3] at h1
  have h4 := sub_mem h2 h1
  rw [sub_sub_cancel] at h4
  have h5 := Ideal.mul_mem_left _ (↑(hv.pow α).unit⁻¹ : OD l ↥(OL LL)) h4
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h5


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD m hm n hn w hw j
  obtain ⟨α, β₀, hα, hβ₀⟩ := P.exists_exponents
  have hβ : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.L := by
    have h1 := P.L.smul_mem (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) (hβ₀ m hm)
    have h2 : E ↥LL.1 l e ^ (β₀ + n) • m =
        (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) • E ↥LL.1 l e ^ β₀ • m := by
      rw [pow_add, mul_comm, mul_smul]
      rfl
    rw [h2]
    exact h1
  obtain ⟨g, ε, c, hε, hc, hg, hk⟩ := GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer l a e ϖ hl2
  obtain ⟨u, hu, hq⟩ := GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ε c hε hc
  obtain ⟨hnz, hnat⟩ := GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ
  have hxM : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.MMl := P.ext_mono (le_trans (A_le_S l e) (le_away _ _)) hβ
  have hsurj := P.xiExt.surjective (E ↥LL.1 l e ^ (β₀ + n) • m)
  obtain ⟨wx, hwxdef⟩ := hsurj
  have hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)) :=
    ((GlobalTheory.BK.xi_trivialises_invL_S ↥(OL LL) ↥LL.1 l e a ι P).2 wx).1 (by rw [hwxdef]; exact hxM)
  have hD1 := GlobalTheory.T.divided_difference_ideal_power_mem (OD l ↥(OL LL)) hnat (ED ↥LL.1 (thetaW a LL) ϖ) _ u hu hq (α + (β₀ + n))
    (fun i => YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j)
    (key_sums hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α (β₀ + n) hα g hg ε c hk hm hwx hwxdef j)
  have hfin := tail_step (thetaW a LL) ϖ P hnz (E_pow_xiExt_mem_Man P) (descN_mem_Mext P) α β₀ n hα hm hn hwx hwxdef j hD1
  rw [← iD_eq_YD (thetaW a LL) ϖ hn j (fun τ => w τ j) (fun τ => hw τ j)] at hfin
  exact hfin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromy_image_mem_BdRplus_lattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  first | exact @GlobalTheory.GalStep.main | exact GlobalTheory.GalStep.main | (intros; apply GlobalTheory.GalStep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisin
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_E_smul_EN_mem_Man : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι),
    ∃ n : ℕ, ∀ m ∈ P.M, E K l e ^ n • P.EN m ∈ P.Man := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  have hk : 1 / ((e : ℝ) * l) < 1 / (e : ℝ) := by
    have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact one_div_lt_one_div_of_lt he (by nlinarith)

  have hL : ∀ v ∈ P.L, E K l e ^ α • P.conn v ∈ P.Man := by
    intro v hv
    have hv' : v ∈ P.Lk (1 / (e : ℝ)) := P.ext_mono (A_le_Rpi l e) hv
    obtain ⟨w, rfl⟩ := P.xiExt.surjective v
    have hw : w ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P (1 / (e : ℝ)) hk w).1 hv'
    have hNw : (fun τ i => N K (w τ i)) ∈ P.Mext (R O K l (1 / (e : ℝ))) :=
      mem_tot.2 fun τ i => N_mem (derivative_mem_R l (mem_tot.1 hw τ i))
    have h1 : P.conn (P.xiExt w) ∈ P.ext (Rpi O K l e) := by
      rw [PhiMod.conn_xiExt]
      exact (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P (1 / (e : ℝ)) hk _).2 hNw
    exact P.smul_mem_Mext_of_basis (fun i => hα _ (P.phi_mem_L (P.bas_mem_M i))) (A_le_Rpi l e) h1
  refine ⟨α + β, fun m hm => ?_⟩
  have hv := hL _ (hβ m hm)
  rw [PhiMod.conn_smul, smul_add, smul_smul, smul_smul, ← pow_add] at hv
  have h2 : (E K l e ^ α * N K (E K l e ^ β)) • m ∈ P.Man :=
    P.smul_mem_Man (mul_mem (pow_mem (E_mem l e _) α) (N_mem (derivative_mem_R l (pow_mem (E_mem l e _) β))))
      (P.M_le_Man hm)
  have h3 : E K l e ^ (α + β) • P.conn m ∈ P.Man := by
    have := sub_mem hv h2
    rwa [add_sub_cancel_left] at this
  rw [PhiMod.EN_apply, smul_comm]
  exact P.smul_mem_Man (E_mem l e _) h3

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowSmulMonodromyMemBreuilKisinStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisensteinPow_smul_monodromy_mem_breuilKisin : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), ∃ n : ℕ, ∀ m ∈ P.M, E K l e ^ n • P.EN m ∈ P.Man := by
  first | exact @GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man | exact GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man | (intros; apply GlobalTheory.BK.exists_pow_E_smul_EN_mem_Man <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyOperatorMapsIntoCompletion
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalENM

theorem EN_mem_Man : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ m ∈ P.M, P.EN m ∈ P.Man := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH m hm
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_eisensteinPow_smul_monodromy_mem_breuilKisin ↥(OL LL) ↥LL.1 l e a ι P
  have hv := hn m hm
  obtain ⟨jD, hjD⟩ := GlobalTheory.T.kisinModule_tensor_bdRPlus_eq_lattice l a e _ _ (thetaW a LL) ϖ ι P T I
  let w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e := fun τ i =>
    toHat _ _ l e ⟨(E ↥LL.1 l e ^ n • P.EN m) τ i, mem_tot.1 hv τ i⟩
  have hw : ∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) =
      hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i) := fun τ i => (hat_coe_Rpi l e _).symm
  clear_value w
  have h3 := GlobalTheory.T.monodromy_image_mem_BdRplus_lattice hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH jD hjD m hm n hv w hw
  choose y hy using fun i => GlobalTheory.T.ideal_power_membership_divisible l a e _ _ (thetaW a LL) ϖ n (fun τ => w τ i) (h3 i)
  have hE : P.EN m ∈ P.Mext (RpiE ↥(OL LL) ↥LL.1 l e) := P.mem_Mext_invE_of_mem_divE hv
  rw [← P.hatTot_mem_Mhat_iff hE, P.mem_Mhat]
  intro τ i
  refine ⟨y i τ, ?_⟩
  have h1 := congrFun (hy i) τ
  have h2 := hw τ i
  have h4 := hat_E_pow_mul (O := ↥(OL LL)) l e n (mem_tot.1 hE τ i)

  have h1' : w τ i = Ehat ↥(OL LL) ↥LL.1 l e ^ n * y i τ := by rw [h1]; rfl
  have h5 : (E ↥LL.1 l e ^ n • P.EN m) τ i = E ↥LL.1 l e ^ n * P.EN m τ i := rfl
  have h7 := ((congrArg (algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e)) h1').symm.trans h2).trans
    ((congrArg (hat ↥(OL LL) l e) h5).trans h4)
  have h8 := (map_mul (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)) _ _).symm.trans h7
  have hu : IsUnit (algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e ^ n)) := by
    rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (Ehat ↥(OL LL) ↥LL.1 l e)).pow n
  exact hu.mul_left_cancel h8

end GlobalTheory.NgalENM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyOperatorMapsIntoCompletionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monodromyOperator_maps_into_completion : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ m ∈ P.M, P.EN m ∈ P.Man := by
  first | exact @GlobalTheory.NgalENM.EN_mem_Man | exact GlobalTheory.NgalENM.EN_mem_Man | (intros; apply GlobalTheory.NgalENM.EN_mem_Man <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.NgalFil

theorem ENStable_and_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  intro hB l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I jB Pl AI hS hC hH
  have h1 := GlobalTheory.T.monodromyOperator_maps_into_completion hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH
  exact ⟨h1, GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps hB l a e ϖ LL hl ι P T I jB Pl AI hS hC hH h1⟩

end GlobalTheory.NgalFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeStableAndHodgeTateJumpsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_lattice_stable_and_hodgeTate_jumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) ∧ ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  first | exact @GlobalTheory.NgalFil.ENStable_and_jumps | exact GlobalTheory.NgalFil.ENStable_and_jumps | (intros; apply GlobalTheory.NgalFil.ENStable_and_jumps <;> assumption)
end
