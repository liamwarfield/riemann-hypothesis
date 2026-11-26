module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SummableNormCosetOut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
open MeasureTheory

namespace GlobalTheory.HaarAlg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] in
theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def avg (F : K → Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => ∫ g, F g a b ∂κ

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem mul_avg {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    M * avg κ F = avg κ fun g => M * F g := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem avg_mul {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    avg κ F * M = avg κ fun g => F g * M := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι] in
theorem avg_const (M : Matrix ι ι ℂ) : avg κ (fun _ => M) = M := by
  ext a b
  simp [avg]

variable [κ.IsMulLeftInvariant]

omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι] in
theorem avg_left (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by
  ext a b
  exact integral_mul_left_eq_self (fun g => F g a b) h

theorem rho_mul_avg (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by
  rw [mul_avg κ hρ, ← avg_left κ ρ h]
  simp only [map_mul]

theorem avg_mul_rho (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by
  have hc : Continuous fun g : K => ρ g⁻¹ := hρ.comp continuous_inv
  have h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹ := fun h => by
    rw [avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]
    simp only [mul_inv_rev, inv_inv, map_mul]
  have h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ := by
    rw [avg_mul κ hc]
    simp only [rho_mul_avg κ ρ hρ, avg_const]
  have h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹ := by
    rw [mul_avg κ hρ]
    simp only [h1, avg_const]
  rw [h2.symm.trans h3, h1]

theorem isAlgebraic_integral (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (Γ : Set K) (hΓ : Dense Γ)
    (halg : ∀ γ ∈ Γ, ∀ a b, IsAlgebraic ℚ (ρ γ a b)) (a b : ι) : IsAlgebraic ℚ (∫ g, ρ g a b ∂κ) := by
  set P := avg κ ρ with hP
  let Q := algebraicClosure ℚ ℂ
  have key : ∀ s : ℂ ≃ₐ[Q] ℂ, P * P.map s = P.map s ∧ P.map s * P = P.map s := fun s => by
    have hfix : ∀ γ ∈ Γ, (ρ γ).map s = ρ γ := fun γ hγ => by
      ext a b
      exact s.commutes (⟨ρ γ a b, mem_algebraicClosure_iff.2 (halg γ hγ a b)⟩ : Q)
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    have l : ∀ g, ρ g * P.map s = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => ρ g * P.map s) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show ρ γ * P.map s = P.map s
          rw [← hfix γ hγ, ← hm, hP, rho_mul_avg κ ρ hρ]) g
    have r : ∀ g, P.map s * ρ g = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => P.map s * ρ g) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show P.map s * ρ γ = P.map s
          rw [← hfix γ hγ, ← hm, hP, avg_mul_rho κ ρ hρ]) g
    constructor
    · conv_lhs => rw [hP]
      rw [avg_mul κ hρ]
      simp only [← hP, l, avg_const]
    · conv_lhs => rw [hP]
      rw [mul_avg κ hρ]
      simp only [← hP, r, avg_const]
  have fix : ∀ s : ℂ ≃ₐ[Q] ℂ, P.map s = P := fun s => by
    have h1 := congrArg (fun M : Matrix ι ι ℂ => M.map s) (key s.symm).1
    have e : (P.map s.symm).map s = P := by ext a b; simp
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    simp only [hm, e] at h1
    rw [← (key s).2, h1]
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := Q) (P a b)
    fun s => congrFun (congrFun (fix s) a) b
  have : P a b ∈ Q := hq ▸ q.2
  exact mem_algebraicClosure_iff.1 this

end GlobalTheory.HaarAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupLatticeLocalisationOfUnitBall
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSmulMemSupLattice
open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory.DenominatorExistenceTwistedOperators

theorem abs_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ∉ v.asIdeal) : FinitePlace.mk v (x : K) = 1 := by
  rw [FinitePlace.mk_apply]
  have h1 := FinitePlace.norm_le_one K v x
  have h2 := (FinitePlace.norm_lt_one_iff_mem K v x).not.mpr hx
  exact le_antisymm h1 (not_lt.mp h2)

theorem exists_prime_to_part {R : Type} [CommRing R] [IsDedekindDomain R] (p : HeightOneSpectrum R) (d : R)
    (hd : d ≠ 0) : ∃ s ∉ p.asIdeal, ∀ q : HeightOneSpectrum R, q ≠ p → ∃ t ∉ q.asIdeal, ∃ u, t * s = u * d := by
  have hI : Ideal.span {d} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hd
  obtain ⟨n, J, hJ, hfac⟩ := WfDvdMonoid.max_power_factor hI p.irreducible
  rw [Ideal.dvd_iff_le] at hJ
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJ
  refine ⟨s, hsp, fun q hq => ?_⟩
  have hnle : ¬ p.asIdeal ^ n ≤ q.asIdeal := by
    intro h
    have := q.isPrime
    have h1 : p.asIdeal ≤ q.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨t, htq, ?_⟩
  have : t * s ∈ Ideal.span {d} := by
    rw [hfac]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, hu.symm⟩

theorem exists_denominator {R K M : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M] (N : Submodule R M) (x : M)
    (hx : x ∈ Submodule.span K (N : Set M)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
    have hwK : algebraMap R K w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw0, ?_⟩
    have : (a * w) • (algebraMap R K u / algebraMap R K w) • x = u • a • x := by
      rw [← algebraMap_smul K (a * w), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [this]
    exact N.smul_mem _ hx

theorem exists_smul_mem_supLattice (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type)
    [(σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [(σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [Group G]
    (Φ : FormsL LL Ks WL W G) (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK)
    (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK) (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s ∉ la.asIdeal, s • (f : WL) ∈ Φ.MK := by
  obtain ⟨d, hd, hdf⟩ := exists_denominator (K := Ks) Φ.MK (f : WL) (by rw [hspan]; exact f.2)
  obtain ⟨s, hs, hq⟩ := exists_prime_to_part la d hd
  refine ⟨s, hs, ?_⟩
  have hsm : ∀ (a : 𝓞 Ks) (g : WL), a • g = (a : Ks) • g := fun a g => (algebraMap_smul Ks a g).symm
  have hm : s • (f : WL) ∈ Φ.WK := by rw [hsm]; exact Φ.WK.smul_mem _ f.2
  refine ⟨hm, fun q y => ?_⟩
  by_cases h : q = la
  · subst h
    have h1 : (⟨s • (f : WL), hm⟩ : Φ.WK) = (s : Ks) • f := Subtype.ext (hsm s f)
    rw [h1, Φ.nrm_smul, abs_eq_one q s hs, one_mul]
    exact hf y
  · obtain ⟨t, ht, u, htu⟩ := hq q h
    have hmem : t • s • (f : WL) ∈ Φ.MK := by
      rw [smul_smul, htu, mul_smul]; exact Φ.MK.smul_mem _ hdf
    obtain ⟨hw, hb⟩ := hmem
    have h1 : (⟨t • s • (f : WL), hw⟩ : Φ.WK) = (t : Ks) • ⟨s • (f : WL), hm⟩ := Subtype.ext (hsm t _)
    have h2 := hb q y
    rwa [h1, Φ.nrm_smul, abs_eq_one q t ht, one_mul] at h2

end GlobalTheory.DenominatorExistenceTwistedOperators
end

open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory

theorem supLattice_localisation_of_unitBall (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks]
    [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] [Group G] (Φ : FormsL LL Ks WL W G)
    (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK) (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK)
    (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s : 𝓞 Ks, s ∉ la.asIdeal ∧ s • (f : WL) ∈ Φ.MK := by
  first
  | exact @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice
  | (apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorExistenceTwistedOperators.exists_smul_mem_supLattice ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomain
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_eq_of_fundamentalDomain (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (Γ N : Subgroup H) (hΓ : Countable Γ) (hNc : IsClosed (N : Set H)) (κ : Measure N) (𝓝 : Set N)
    (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ) (hfin : κ 𝓝 ≠ ⊤) (n₀ : N) :
    κ.map (· * n₀) = κ := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨((x : N) : H), x.2⟩ : Γ)) ?_
    intro a b h
    have h' : ((a : N) : H) = ((b : N) : H) := congrArg (fun y : Γ => (y : H)) h
    exact Subtype.ext (Subtype.ext h')
  haveI : (κ.map (· * n₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right κ n₀
  have hc := Measure.isMulLeftInvariant_eq_smul (κ.map (· * n₀)) κ
  set c := Measure.haarScalarFactor (κ.map (· * n₀)) κ
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf N) ((· * n₀) ⁻¹' 𝓝) κ := by
    refine h𝓝.preimage_of_equiv (quasiMeasurePreserving_mul_right κ n₀) (e := id) bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : κ ((· * n₀) ⁻¹' 𝓝) = κ 𝓝 := h𝓝'.measure_eq h𝓝
  have h0 : κ 𝓝 ≠ 0 := h𝓝.measure_ne_zero (NeZero.ne κ)
  have hmap : (κ.map (· * n₀)) 𝓝 = κ ((· * n₀) ⁻¹' 𝓝) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight n₀) 𝓝
  have h1 : (c : ENNReal) * κ 𝓝 = 1 * κ 𝓝 := by
    calc (c : ENNReal) * κ 𝓝 = (c • κ) 𝓝 := by simp [Measure.smul_apply]
      _ = (κ.map (· * n₀)) 𝓝 := by rw [hc]
      _ = 1 * κ 𝓝 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarMapMulRightEqOfFiniteFundamentalDomainStatement
open MeasureTheory Function
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_map_mul_right_eq_of_finite_fundamentalDomain : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → κ 𝓝 ≠ ⊤ → ∀ n₀ : N, κ.map (· * n₀) = κ := by
  first | exact @GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | exact GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain | (intros; apply GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMul
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    substF h g (substF h' g' P) = substF (h * h') (g * g') P := by
  have key : (substF h g).comp (substF h' g') = substF (h * h') (g * g') := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, substF_X, substF_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, substF_X, algHom_C, algebraMap_eq, Pi.mul_apply, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun _ => Finset.univ) (t' := Finset.univ) (s' := fun _ => Finset.univ) (by simp)]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun x => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  exact congrArg (fun f => f P) key

end GlobalTheory.CompactHowe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMulStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul : ∀ {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin N × Fin n) ℂ), GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) = GlobalTheory.CompactHowe.substF (h * h') (g * g') P := by
  first | exact @GlobalTheory.CompactHowe.substF_mul | exact GlobalTheory.CompactHowe.substF_mul | (intros; apply GlobalTheory.CompactHowe.substF_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubsti
noncomputable section

open MvPolynomial

namespace GlobalTheory.CompactHowe

theorem weight_fst_eq_mapDomain {ι κ : Type} (k : ι × κ →₀ ℕ) :
    Finsupp.weight (fun p : ι × κ => (Finsupp.single p.1 1 : ι →₀ ℕ)) k = Finsupp.mapDomain Prod.fst k := by
  rw [Finsupp.weight_apply, Finsupp.mapDomain]
  refine Finsupp.sum_congr fun p _ => ?_
  simp

theorem substF_X_isWeightedHomogeneous {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (X p)) (Finsupp.single p.1 1) := by
  rw [substF_X]
  refine IsWeightedHomogeneous.sum _ _ _ fun k _ => IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
  have h1 := isWeightedHomogeneous_X ℂ (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ)) (p.1, k, l)
  have h2 := (isWeightedHomogeneous_C (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
    (h p.1 k p.2.1 * g p.1 l p.2.2)).mul h1
  rwa [zero_add] at h2

theorem mapDomain_fst_eq_of_coeff_substF_ne_zero {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ)
    (hk : AddMonoidAlgebra.coeff (substF h g (MvPolynomial.monomial k 1)) k' ≠ 0) :
    Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  have key : IsWeightedHomogeneous (fun p : ι × Fin N × Fin n => (Finsupp.single p.1 1 : ι →₀ ℕ))
      (substF h g (MvPolynomial.monomial k 1)) (Finsupp.mapDomain Prod.fst k) := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod, ← weight_fst_eq_mapDomain, Finsupp.weight_apply,
      Finsupp.sum]
    refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
    rw [map_pow]
    exact (substF_X_isWeightedHomogeneous h g p).pow (k p)
  rw [← weight_fst_eq_mapDomain]
  exact key hk

end GlobalTheory.CompactHowe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero : ∀ {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (k k' : ι × Fin N × Fin n →₀ ℕ), AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k' ≠ 0 → Finsupp.mapDomain Prod.fst k' = Finsupp.mapDomain Prod.fst k := by
  first | exact @GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero | (intros; apply GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCo
open MvPolynomial

namespace GlobalTheory.SubstCoeff

variable {σ : Type}

theorem continuous_coeff_mul {Y : Type} [TopologicalSpace Y] (F G : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (F y) m) (hG : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (G y) m) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (F y * G y) m := by
  classical
  simp only [coeff_mul]
  exact continuous_finsetSum _ fun x _ => (hF _).mul (hG _)

theorem continuous_coeff_pow {Y : Type} [TopologicalSpace Y] (F : Y → MvPolynomial σ ℂ)
    (hF : ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (F y) m) (e : ℕ) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (F y ^ e) m := by
  induction e generalizing m with
  | zero =>
    classical
    simp only [pow_zero, coeff_one]
    exact continuous_const
  | succ e ih =>
    simp only [pow_succ]
    exact continuous_coeff_mul _ _ ih hF m

theorem continuous_coeff_prod {Y κ : Type} [TopologicalSpace Y] (s : Finset κ) (f : κ → Y → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, Continuous fun y => AddMonoidAlgebra.coeff (f q y) m) (m : σ →₀ ℕ) :
    Continuous fun y => AddMonoidAlgebra.coeff (∏ q ∈ s, f q y) m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact continuous_const
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact continuous_coeff_mul _ _ (hf a (Finset.mem_insert_self a s))
      (fun m' => ih (fun q hq => hf q (Finset.mem_insert_of_mem hq)) m') m

theorem isAlgebraic_sum {κ : Type} (s : Finset κ) (f : κ → ℂ) (hf : ∀ q ∈ s, IsAlgebraic ℚ (f q)) :
    IsAlgebraic ℚ (∑ q ∈ s, f q) :=
  Finset.sum_induction f (IsAlgebraic ℚ) (fun _ _ ha hb => ha.add hb) isAlgebraic_zero hf

theorem isAlgebraic_coeff_mul (P Q : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m)) (hQ : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff Q m)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (P * Q) m) := by
  classical
  rw [coeff_mul]
  exact isAlgebraic_sum _ _ fun x _ => (hP _).mul (hQ _)

theorem isAlgebraic_coeff_one (m : σ →₀ ℕ) : IsAlgebraic ℚ (AddMonoidAlgebra.coeff (1 : MvPolynomial σ ℂ) m) := by
  classical
  rw [coeff_one]
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem isAlgebraic_coeff_pow (P : MvPolynomial σ ℂ)
    (hP : ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m)) (e : ℕ) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (P ^ e) m) := by
  induction e generalizing m with
  | zero => simpa only [pow_zero] using isAlgebraic_coeff_one m
  | succ e ih =>
    rw [pow_succ]
    exact isAlgebraic_coeff_mul _ _ ih hP m

theorem isAlgebraic_coeff_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial σ ℂ)
    (hf : ∀ q ∈ s, ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff (f q) m)) (m : σ →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (∏ q ∈ s, f q) m) :=
  Finset.prod_induction f (fun P => ∀ m, IsAlgebraic ℚ (AddMonoidAlgebra.coeff P m))
    (fun _ _ ha hb => isAlgebraic_coeff_mul _ _ ha hb) isAlgebraic_coeff_one hf m

variable {ι : Type} {N n : ℕ}

theorem substF_monomial_one (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF h g (monomial k 1) = ∏ q ∈ k.support, (GlobalTheory.CompactHowe.substF h g (X q)) ^ k q := by
  rw [monomial_eq, map_mul, C_1, map_one, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow]

theorem continuous_coeff_substF_X (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    Continuous fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) =>
      AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (X q)) m := by
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const
  · exact ((continuous_apply q.1).comp continuous_fst).matrix_elem a q.2.1
  · exact ((continuous_apply q.1).comp continuous_snd).matrix_elem b q.2.2

theorem isAlgebraic_coeff_substF_X (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (hh : ∀ i a b, IsAlgebraic ℚ (h i a b)) (hg : ∀ i a b, IsAlgebraic ℚ (g i a b))
    (q : ι × Fin N × Fin n) (m : ι × Fin N × Fin n →₀ ℕ) :
    IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (X q)) m) := by
  classical
  simp only [GlobalTheory.CompactHowe.substF_X, coeff_sum, coeff_C_mul]
  refine isAlgebraic_sum _ _ fun a _ => isAlgebraic_sum _ _ fun b _ => ?_
  refine ((hh _ _ _).mul (hg _ _ _)).mul ?_
  rw [coeff_X']
  split_ifs
  · exact isAlgebraic_one
  · exact isAlgebraic_zero

theorem coeff_substF_monomial_continuous_algebraic :
    ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  intro ι N n k k'
  refine ⟨?_, fun h g hh hg => ?_⟩
  · simp only [substF_monomial_one]
    exact continuous_coeff_prod _ _ (fun q _ m => continuous_coeff_pow _ (continuous_coeff_substF_X q) _ m) k'
  · rw [substF_monomial_one]
    exact isAlgebraic_coeff_prod _ _
      (fun q _ m => isAlgebraic_coeff_pow _ (isAlgebraic_coeff_substF_X h g hh hg q) _ m) k'

end GlobalTheory.SubstCoeff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic : ∀ {ι : Type} {N n : ℕ} (k k' : ι × Fin N × Fin n →₀ ℕ), Continuous (fun p : (ι → Matrix (Fin N) (Fin N) ℂ) × (ι → Matrix (Fin n) (Fin n) ℂ) => AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF p.1 p.2 (MvPolynomial.monomial k 1)) k') ∧ ∀ (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ), (∀ i a b, IsAlgebraic ℚ (h i a b)) → (∀ i a b, IsAlgebraic ℚ (g i a b)) → IsAlgebraic ℚ (AddMonoidAlgebra.coeff (GlobalTheory.CompactHowe.substF h g (MvPolynomial.monomial k 1)) k') := by
  first | exact @GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | exact GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic | (intros; apply GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvester
namespace GlobalTheory.SylvesterInertia

open Matrix Module
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

def qf (J : Matrix n n ℂ) (x : n → ℂ) : ℂ := star x ⬝ᵥ J *ᵥ x

def inlMap (a b : ℕ) : (Fin a → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim z 0
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

def inrMap (a b : ℕ) : (Fin b → ℂ) →ₗ[ℂ] (Fin a ⊕ Fin b → ℂ) where
  toFun z := Sum.elim 0 z
  map_add' x y := by ext k; cases k <;> simp
  map_smul' c x := by ext k; cases k <;> simp

lemma inlMap_injective (a b : ℕ) : Function.Injective (inlMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inl i)

lemma inrMap_injective (a b : ℕ) : Function.Injective (inrMap a b) := by
  intro z z' h; funext i; exact congrFun h (Sum.inr i)

def chg {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    (Fin a ⊕ Fin b → ℂ) →ₗ[ℂ] (n → ℂ) :=
  LinearMap.funLeft ℂ ℂ e ∘ₗ (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ).mulVecLin

lemma chg_apply {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) (y : Fin a ⊕ Fin b → ℂ) :
    chg e P y = ((P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y) ∘ e := rfl

lemma chg_injective {a b : ℕ} (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ) :
    Function.Injective (chg e P) := by
  intro y y' h
  have h1 : (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y = (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ y' := by
    have := congrArg (fun v => v ∘ e.symm) h
    simpa [chg_apply, Function.comp_def] using this
  have h2 := congrArg (fun v => ((P⁻¹ : GL (Fin a ⊕ Fin b) ℂ) : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) *ᵥ v) h1
  simpa [mulVec_mulVec] using h2

lemma qf_chg {a b : ℕ} (J : Matrix n n ℂ) (e : n ≃ Fin a ⊕ Fin b) (P : GL (Fin a ⊕ Fin b) ℂ)
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b) (y : Fin a ⊕ Fin b → ℂ) :
    qf J (chg e P y) = star y ⬝ᵥ Formalism.UG.Jpq a b *ᵥ y := by
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ := (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ)
  have hc : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by ext i j; rfl
  rw [← h, hc]
  set w := M *ᵥ y
  have h1 : J *ᵥ (w ∘ e) = (J.reindex e e *ᵥ w) ∘ e := by
    rw [reindex_apply, submatrix_mulVec_equiv]
    ext i; simp [Function.comp_def]
  have h2 : qf J (chg e P y) = star w ⬝ᵥ (J.reindex e e *ᵥ w) := by
    rw [qf, chg_apply, h1]
    simp only [dotProduct, Function.comp_apply, Pi.star_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [h2]
  simp only [w, star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, Matrix.mul_assoc]

lemma jpq_inl (a b : ℕ) (z : Fin a → ℂ) :
    star (inlMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inlMap a b z = star z ⬝ᵥ z := by
  simp [inlMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def]

lemma jpq_inr (a b : ℕ) (z : Fin b → ℂ) :
    star (inrMap a b z) ⬝ᵥ Formalism.UG.Jpq a b *ᵥ inrMap a b z = -(star z ⬝ᵥ z) := by
  simp [inrMap, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, neg_mulVec, Finset.sum_neg_distrib]

lemma pos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inlMap a b)) (hx0 : x ≠ 0) : 0 < qf J x := by
  obtain ⟨z, rfl⟩ := hx
  have hz : z ≠ 0 := by rintro rfl; exact hx0 (map_zero _)
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inl]
  exact dotProduct_star_self_pos_iff.mpr hz

lemma nonpos_of_mem {a b : ℕ} {J : Matrix n n ℂ} {e : n ≃ Fin a ⊕ Fin b} {P : GL (Fin a ⊕ Fin b) ℂ}
    (h : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) * J.reindex e e *
      (P : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) ℂ) = Formalism.UG.Jpq a b)
    {x : n → ℂ} (hx : x ∈ LinearMap.range (chg e P ∘ₗ inrMap a b)) : qf J x ≤ 0 := by
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.comp_apply, qf_chg J e P h, jpq_inr]
  exact neg_nonpos.mpr (dotProduct_star_self_nonneg z)

theorem fst_le_of_hasSignature {J : Matrix n n ℂ} {a b a' b' : ℕ}
    (h : Formalism.UG.HasSignature J a b) (h' : Formalism.UG.HasSignature J a' b') : a ≤ a' := by
  obtain ⟨e, P, hP⟩ := h
  obtain ⟨e', P', hP'⟩ := h'
  by_contra hlt
  push_neg at hlt
  set U := LinearMap.range (chg e P ∘ₗ inlMap a b)
  set N := LinearMap.range (chg e' P' ∘ₗ inrMap a' b')
  have hU : finrank ℂ U = a := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e P).comp (inlMap_injective a b))]
    simp
  have hN : finrank ℂ N = b' := by
    rw [LinearMap.finrank_range_of_inj (by rw [LinearMap.coe_comp]; exact (chg_injective e' P').comp (inrMap_injective a' b'))]
    simp
  have hcard : Fintype.card n = a' + b' := by simpa using Fintype.card_congr e'
  have hsup : finrank ℂ ↥(U ⊔ N) ≤ Fintype.card n := by
    have := Submodule.finrank_le (U ⊔ N)
    simpa using this
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U N
  have hinf : U ⊓ N ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hsum
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  have h1 := pos_of_mem hP (Submodule.mem_inf.1 hx).1 hx0
  have h2 := nonpos_of_mem hP' (Submodule.mem_inf.1 hx).2
  exact lt_irrefl _ (lt_of_lt_of_le h1 h2)

theorem hasSignature_fst_unique : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ},
    Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' :=
  fun h h' => le_antisymm (fst_le_of_hasSignature h h') (fst_le_of_hasSignature h' h)

end GlobalTheory.SylvesterInertia
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFstUniqueSylvesterStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSignature_fst_unique_sylvester : ∀ {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {a b a' b' : ℕ}, Formalism.UG.HasSignature J a b → Formalism.UG.HasSignature J a' b' → a = a' := by
  first | exact @GlobalTheory.SylvesterInertia.hasSignature_fst_unique | exact GlobalTheory.SylvesterInertia.hasSignature_fst_unique | (intros; apply GlobalTheory.SylvesterInertia.hasSignature_fst_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClasses
open GlobalTheory

namespace GlobalTheory.ShuffleCount

open MvPolynomial

private theorem aeval_killCompl {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (h0 : ∀ Δ ∉ U, φ Δ = 0) (P : MvPolynomial S ℚ) :
    aeval (fun Δ : U => φ Δ) (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P) = aeval φ P := by
  classical
  have key : (aeval (fun Δ : U => φ Δ)).comp (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S))) = aeval φ := by
    apply MvPolynomial.algHom_ext
    intro Δ
    by_cases hΔ : Δ ∈ U
    · have hX : (X Δ : MvPolynomial S ℚ) = rename Subtype.val (X (⟨Δ, hΔ⟩ : U)) := by rw [rename_X]
      rw [AlgHom.comp_apply]
      conv_lhs => rw [hX]
      rw [killCompl_rename_app, aeval_X, aeval_X]
    · rw [AlgHom.comp_apply, aeval_X, h0 Δ hΔ, X, killCompl_monomial_eq_zero_of_not_subset, map_zero]
      intro h
      obtain ⟨⟨_, hmem⟩, rfl⟩ := h (by simp : Δ ∈ (↑(Finsupp.single Δ 1).support : Set S))
      exact hΔ hmem
  exact AlgHom.congr_fun key P

private theorem coeff_killCompl_comapDomain {S : Type*} (U : Set S) (P : MvPolynomial S ℚ) (m : S →₀ ℕ)
    (hm : ↑m.support ⊆ Set.range (Subtype.val : U → S)) :
    AddMonoidAlgebra.coeff (killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P)
      (m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn) = AddMonoidAlgebra.coeff P m := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n r =>
    by_cases hn : ↑n.support ⊆ Set.range (Subtype.val : U → S)
    · rw [killCompl_monomial_eq_monomial_comapDomain_of_subset _ _ hn, coeff_monomial, coeff_monomial]
      have hiff : n.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn =
          m.comapDomain (Subtype.val : U → S) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)).injOn ↔ n = m := by
        constructor
        · intro h
          rw [← Finsupp.mapDomain_comapDomain _ Subtype.val_injective n hn,
            ← Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hm, h]
        · rintro rfl
          rfl
      simp only [hiff]
    · rw [killCompl_monomial_eq_zero_of_not_subset _ _ hn, AddMonoidAlgebra.coeff_zero,
        coeff_monomial]
      split_ifs with h
      · subst n
        exact (hn hm).elim
      · rfl
  | add P Q hP hQ => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hP, hQ]

theorem coeff_eq_zero_of_aeval_eq_zero {S B : Type*} [CommRing B] [Algebra ℚ B] (U : Set S)
    (φ : S → B) (hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ)) (h0 : ∀ Δ ∉ U, φ Δ = 0)
    (P : MvPolynomial S ℚ) (hP : aeval φ P = 0) (m : S →₀ ℕ) (hm : ∀ Δ ∈ m.support, Δ ∈ U) :
    AddMonoidAlgebra.coeff P m = 0 := by
  classical
  have hm' : ↑m.support ⊆ Set.range (Subtype.val : U → S) := fun Δ hΔ =>
    ⟨⟨Δ, hm Δ (Finset.mem_coe.1 hΔ)⟩, rfl⟩
  rw [← coeff_killCompl_comapDomain U P m hm']
  have hQ : killCompl (R := ℚ) (Subtype.val_injective : Function.Injective (Subtype.val : U → S)) P = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 hind
    rw [map_zero, aeval_killCompl U φ h0 P, hP]
  rw [hQ]
  simp

theorem separates_of_shuffle_count : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  intro I S A _ _ Ψ M U ℓ φ hinj hU hφ0 hcnt n p c hp hne hc
  classical
  let Rh : List A → (I →₀ ℤ) →+ ℤ := fun w =>
    Finsupp.liftAddHom fun x => AddMonoidHom.mulRight ((M x w).toNat : ℤ)
  have hRs : ∀ w x a, Rh w (Finsupp.single x a) = a * ((M x w).toNat : ℤ) := fun w x a => by
    simp [Rh]
  have hRsum : ∀ w (y : I →₀ ℤ), Rh w y = y.sum fun x a => a * ((M x w).toNat : ℤ) := fun w y => by
    simp [Rh, Finsupp.liftAddHom_apply]
  have K0 : ∀ (y : I →₀ ℤ) (w : List A) (N : ℕ), 0 ≤ y →
      (y.sum fun x a => (a.toNat : ℕ∞) * M x w) = (N : ℕ∞) → Rh w y = N := by
    intro y w N hy hN
    rw [Finsupp.sum] at hN
    have hfin : ∀ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w ≠ ⊤ := by
      intro x hx htop
      have hle : ((y x).toNat : ℕ∞) * M x w ≤ ∑ x ∈ y.support, ((y x).toNat : ℕ∞) * M x w :=
        Finset.single_le_sum (f := fun x => ((y x).toNat : ℕ∞) * M x w) (fun _ _ => zero_le) hx
      rw [hN, htop] at hle
      exact ENat.natCast_ne_top N (top_le_iff.1 hle)
    have h1 := congrArg ENat.toNat hN
    rw [ENat.toNat_sum hfin, ENat.toNat_natCast] at h1
    simp only [ENat.toNat_mul, ENat.toNat_natCast] at h1
    rw [hRsum, Finsupp.sum, ← h1, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.cast_mul, Int.toNat_of_nonneg (Finsupp.le_def.1 hy x)]
  have K1 : ∀ (w : List A) (P : MvPolynomial S ℤ),
      (ShuffleAlgebra.wordBasis ℚ A).repr (aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P)) w =
        ((Rh w (Ψ.symm P) : ℤ) : ℚ) := by
    intro w P
    induction P using MvPolynomial.induction_on' with
    | monomial m r =>
      obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
      have hmr : (MvPolynomial.monomial m r : MvPolynomial S ℤ) = r • MvPolynomial.monomial m 1 := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [MvPolynomial.map_monomial, MvPolynomial.aeval_monomial, ← hs2, ← Algebra.smul_def, map_smul,
        Finsupp.smul_apply, Lyndon.repr_sum_word, hmr, map_zsmul, map_zsmul, K0 _ w _ hpos (hs1 w),
        smul_eq_mul, smul_eq_mul]
      simp only [eq_intCast, Int.cast_mul, Int.cast_natCast]
      congr
    | add P Q hP hQ =>
      simp only [map_add (f := _), Finsupp.add_apply, hP, hQ, Int.cast_add]
  have K2 : ∀ m : S →₀ ℕ, (∃ Δ ∈ m.support, Δ ∉ U) →
      ∀ x, Ψ.symm (MvPolynomial.monomial m 1) x ≠ 0 → ∀ w, M x w = 0 := by
    rintro m ⟨Δ, hΔ, hΔU⟩ x hx w
    obtain ⟨hpos, s, hs1, hs2⟩ := hcnt m
    have hprod : (m.prod fun Δ e => φ Δ ^ e) = 0 :=
      Finset.prod_eq_zero hΔ (by show φ Δ ^ m Δ = 0; rw [hφ0 Δ hΔU, zero_pow (Finsupp.mem_support_iff.1 hΔ)])
    have hcount : s.count w = 0 := by
      have h := Lyndon.repr_sum_word ℚ s w
      rw [hs2, hprod, map_zero, Finsupp.zero_apply] at h
      have h'' := Nat.cast_eq_zero.1 h.symm
      convert h''
    have h1 := hs1 w
    rw [hcount, Finsupp.sum, Nat.cast_zero, Finset.sum_eq_zero_iff] at h1
    have h2 := h1 x (Finsupp.mem_support_iff.2 hx)
    rcases mul_eq_zero.1 h2 with h | h
    · exfalso
      have hnn := Finsupp.le_def.1 hpos x
      have h0 : (Ψ.symm (MvPolynomial.monomial m 1) x).toNat = 0 := by exact_mod_cast h
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hnn
      omega
    · exact h
  have hind : AlgebraicIndependent ℚ (fun Δ : U => φ Δ) := by
    have hR := Published.radfordShufflePolynomial_holds.algebraicIndependent ℚ A
    have he : Function.Injective
        (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      intro a b hab
      exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))
    have hcomp := hR.comp _ he
    have heq : (fun Δ : U => φ Δ) =
        (fun l : {w : List A // IsLyndon w} => ShuffleAlgebra.word ℚ l.1) ∘
          (fun Δ : U => (⟨ℓ Δ, (hU Δ Δ.2).1⟩ : {w : List A // IsLyndon w})) := by
      funext Δ
      exact (hU Δ Δ.2).2
    rw [heq]
    exact hcomp
  have K3 : ∀ k : Fin n → ℤ, (∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0) → ∀ i, k i = 0 := by
    intro k hk i
    by_contra hki
    set y : I →₀ ℤ := ∑ j, Finsupp.single (p j) (k j) with hy
    have hRy : ∀ w, Rh w y = 0 := fun w => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy, map_sum]
      simp only [hRs]
      exact hk w
    set P := Ψ y with hPdef
    have hEv : aeval φ (MvPolynomial.map (Int.castRingHom ℚ) P) = 0 := by
      apply (ShuffleAlgebra.wordBasis ℚ A).repr.injective
      rw [map_zero]
      ext w
      rw [K1, hPdef, AddEquiv.symm_apply_apply, hRy, Int.cast_zero, Finsupp.zero_apply]
    have hcoef : ∀ m : S →₀ ℕ, (∀ Δ ∈ m.support, Δ ∈ U) → P.coeff m = 0 := by
      intro m hm
      have h := coeff_eq_zero_of_aeval_eq_zero U φ hind hφ0 _ hEv m hm
      rw [MvPolynomial.coeff_map, eq_intCast, Int.cast_eq_zero] at h
      exact h
    have hyP : y = ∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1) := by
      have h : y = Ψ.symm P := by rw [hPdef, AddEquiv.symm_apply_apply]
      conv_lhs => rw [h, P.as_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_zsmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have hyi : y (p i) = k i := by
      rw [hy, Finsupp.finsetSum_apply, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Finsupp.single_apply, if_neg]
        exact fun h => hji (hp h)
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hne0 : (∑ m ∈ P.support, P.coeff m • Ψ.symm (MvPolynomial.monomial m 1)) (p i) ≠ 0 := by
      rw [← hyP, hyi]
      exact hki
    rw [Finsupp.finsetSum_apply] at hne0
    obtain ⟨m, _, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
    rw [Finsupp.smul_apply, smul_eq_mul] at hm0
    have hc0 : P.coeff m ≠ 0 := left_ne_zero_of_mul hm0
    have hx0 : Ψ.symm (MvPolynomial.monomial m 1) (p i) ≠ 0 := right_ne_zero_of_mul hm0
    have hout : ∃ Δ ∈ m.support, Δ ∉ U := by
      by_contra h
      push_neg at h
      exact hc0 (hcoef m h)
    obtain ⟨w, hw⟩ := hne i
    exact hw (K2 m hout (p i) hx0 w)
  have KQ : ∀ q : Fin n → ℚ, (∀ w, ∑ j, q j * ((M (p j) w).toNat : ℚ) = 0) → ∀ i, q i = 0 := by
    intro q hq i
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ)
      (Finset.univ : Finset (Fin n)) q
    choose k hk using fun j => RingHom.mem_rangeS.1 (hb j (Finset.mem_univ j))
    have hk' : ∀ j, (k j : ℚ) = ((b : ℤ) : ℚ) * q j := fun j => by
      simpa [Algebra.smul_def] using hk j
    have hkrel : ∀ w, ∑ j, k j * ((M (p j) w).toNat : ℤ) = 0 := by
      intro w
      have h : ((∑ j, k j * ((M (p j) w).toNat : ℤ) : ℤ) : ℚ) = 0 := by
        push_cast
        simp only [hk', mul_assoc, ← Finset.mul_sum, hq w, mul_zero]
      exact_mod_cast h
    have hki := K3 k hkrel i
    have hb0 : ((b : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero b
    have h2 := hk' i
    rw [hki, Int.cast_zero] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left hb0
  intro i
  have hq : ∀ ψ : Module.Dual ℚ ℂ, ∀ j, ψ (c j) = 0 := by
    intro ψ
    apply KQ (fun j => ψ (c j))
    intro w
    have h := congrArg ψ (hc w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    show ψ (c j) * _ = ψ (c j * _)
    rw [mul_comm (c j), ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_comm]
  exact (Module.forall_dual_apply_eq_zero_iff ℚ (c i)).1 fun ψ => hq ψ i

end GlobalTheory.ShuffleCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShuffleCountLinearIndependentClassesStatement
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shuffle_count_linearIndependent_classes : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  first | exact @GlobalTheory.ShuffleCount.separates_of_shuffle_count | exact GlobalTheory.ShuffleCount.separates_of_shuffle_count | (intros; apply GlobalTheory.ShuffleCount.separates_of_shuffle_count <;> assumption)
end
end
