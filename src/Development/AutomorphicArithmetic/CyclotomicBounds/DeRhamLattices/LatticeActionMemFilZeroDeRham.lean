module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FilZeroEqRangeCDAndCDInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem mem_FilD_zero (l : ℕ) [Fact l.Prime] (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ y : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) y = x :=
  ⟨fun h => let ⟨z, _, e⟩ := GlobalTheory.RingIface.exists_of_mem_FilD_nat l (n := 0) h; ⟨z, e⟩,
    fun ⟨y, e⟩ => e ▸ GlobalTheory.RingIface.alg_mem_FilD_zero l y⟩

theorem _root_.UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (K : FinExt l), (∀ x : Pl.R.BdR, x ∈ (Pl.PD K).Fil 0 ↔ ∃ y : Per.BdRp l, x = GlobalTheory.BKGal.JumpDR.cD Td y) ∧ Function.Injective (GlobalTheory.BKGal.JumpDR.cD Td) := by
  intro l _ Pl AI Td K
  refine ⟨fun x => ?_, fun y z h => ?_⟩
  · rw [Td.fil, mem_FilD_zero]
    refine exists_congr fun y => ?_
    change _ ↔ x = Td.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) y)
    rw [RingEquiv.eq_symm_apply, eq_comm]
  · exact (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 (Td.eD.symm.injective h)
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeActionMemFilZeroDeRham
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.latticeAction_mem_filZero_deRham :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (d : OD l ↥(OL LL)) (v : T.V), act d (v ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) := by
  intro l _ LL T Pl AI Td act hact d v
  have hfil := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td (Formalism.MainNotions.ElementDenominator.qlExt l)).1
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul o b =>
    rw [hact, mul_one]
    have hb : (JumpDR.cD Td) b ∈ (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0 := (hfil _).2 ⟨b, rfl⟩
    rw [FilV.eq_1]
    exact ⟨((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] ⟨_, hb⟩, by simp⟩
  | add x y hx hy =>
    rw [map_add (f := _), AddMonoidHom.add_apply]
    exact Submodule.add_mem _ hx hy
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlProductBasisOfZlLattice
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsSumTmul
theorem UpperTheory.Reformulated.B.Qj2.exists_sum_tmul :
    ∀ {R O B σ : Type} [inst : CommRing R]
    [inst_1 : AddCommGroup O] [inst_2 : _root_.Module R O] [inst_3 : AddCommGroup B] [inst_4 : _root_.Module R B]
    [inst_5 : Fintype σ] (ω : Module.Basis σ R O) (x : TensorProduct R O B),
    ∃ (y : σ → B), x = ∑ s : σ, (ω : σ → O) s ⊗ₜ[R] y s := by
  intro R O B σ _ _ _ _ _ _ ω x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o b =>
    refine ⟨fun s => ω.repr o s • b, ?_⟩
    conv_lhs => rw [← ω.sum_repr o]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun s _ => TensorProduct.smul_tmul _ _ _
  | add x₁ x₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    refine ⟨y₁ + y₂, ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => (TensorProduct.tmul_add _ _ _).symm
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LinearIndependentQlIntegerBasisSmulLatticeBasis
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem linearIndependent_smul_basis_pairs {Z Q O L V κ σ : Type*} [CommRing Z] [Field Q] [Algebra Z Q] [IsFractionRing Z Q]
    [CommRing O] [Field L] [Algebra O L] [Algebra Z O] [Algebra Q L] [Algebra Z L]
    [IsScalarTower Z O L] [IsScalarTower Z Q L] [AddCommGroup V] [Module L V] [Module O V] [Module Q V]
    [IsScalarTower O L V] [IsScalarTower Q L V] (M : Submodule O V) (b : Module.Basis κ O M)
    (ω : Module.Basis σ Z O) :
    LinearIndependent Q (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) := by
  letI : Module Z V := Module.compHom V (algebraMap Z L)
  haveI : IsScalarTower Z Q V := ⟨fun z q v => by
    show (z • q) • v = algebraMap Z L z • (q • v)
    rw [← algebraMap_smul L (z • q) v, ← algebraMap_smul L q v, smul_smul, Algebra.smul_def z q,
      map_mul, ← IsScalarTower.algebraMap_apply Z Q L]⟩
  haveI : IsScalarTower Z O V := ⟨fun z o v => by
    show (z • o) • v = algebraMap Z L z • (o • v)
    rw [Algebra.smul_def z o, mul_smul, ← algebraMap_smul L (algebraMap Z O z) (o • v),
      ← IsScalarTower.algebraMap_apply Z O L]⟩
  have hc : LinearIndependent O (fun k => ((b k : M) : V)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hZ : LinearIndependent Z (fun p : σ × κ => ω p.1 • ((b p.2 : M) : V)) :=
    linearIndependent_smul ω.linearIndependent hc
  have hQ := (LinearIndependent.iff_fractionRing Z Q).mp hZ
  have hf : (fun p : σ × κ => (algebraMap O L (ω p.1)) • ((b p.2 : M) : V)) =
      fun p => ω p.1 • ((b p.2 : M) : V) := funext fun p => algebraMap_smul L (ω p.1) _
  rw [hf]
  exact hQ

theorem _root_.UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (κ σ : Type) [Fintype κ] [Fintype σ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T) (ω : Module.Basis σ ℤ_[l] ↥(OL LL)), LinearIndependent ℚ_[l] (fun p : σ × κ => ((ω p.1 : ↥(OL LL)) : ↥LL.1) • ((b p.2 : ↥T.L.T) : T.V)) := by
  intro l _ LL T κ σ _ _ b ω
  exact linearIndependent_smul_basis_pairs (Z := ℤ_[l]) (Q := ℚ_[l]) (L := ↥LL.1) T.L.T b ω
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CoeffEqZeroOfSumTmulLinearIndependentEqZero
open TensorProduct

theorem _root_.UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero :
    ∀ (K V C ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup C] [Module K C] [Fintype ι] (v : ι → V), LinearIndependent K v → ∀ c : ι → C, ∑ i, v i ⊗ₜ[K] c i = 0 → ∀ i, c i = 0 := by
  intro K V C ι _ _ _ _ _ _ v hv c hsum i
  classical
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
  have hfv : ∀ j, f (v j) = if j = i then 1 else 0 := by
    intro j
    have h1 : f (v j) = (Module.Basis.span hv).coord i ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
      rw [← hf]
      rfl
    rw [h1, ← Module.Basis.span_apply hv j, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  have h2 := congrArg (⇑((TensorProduct.lid K C).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id)) hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, hfv, map_zero] at h2
  simpa using h2
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem exists_sum_tmul {R O B σ : Type} [CommRing R] [AddCommGroup O] [Module R O]
    [AddCommGroup B] [Module R B] [Fintype σ] (ω : Module.Basis σ R O) (x : O ⊗[R] B) :
    ∃ y : σ → B, x = ∑ s, ω s ⊗ₜ[R] y s :=
  _root_.UpperTheory.Reformulated.B.Qj2.exists_sum_tmul ω x

private theorem abstract_indep {R K O B V C σ κ : Type} [CommRing R] [Field K] [AddCommGroup O]
    [Module R O] [AddCommGroup B] [Module R B] [AddCommGroup V] [Module K V] [AddCommGroup C]
    [Module K C] [Fintype σ] [Fintype κ] (ω : Module.Basis σ R O)
    (act : O ⊗[R] B →+ (V ⊗[K] C →+ V ⊗[K] C)) (e : κ → V ⊗[K] C) (w : σ × κ → V) (f : B → C)
    (hf : ∀ y, f y = 0 → y = 0) (hw : LinearIndependent K w)
    (hact : ∀ s k y, act (ω s ⊗ₜ[R] y) (e k) = w (s, k) ⊗ₜ[K] f y)
    (d : κ → O ⊗[R] B) (hd : ∑ k, act (d k) (e k) = 0) (k : κ) : d k = 0 := by
  choose y hy using fun k => exists_sum_tmul ω (d k)
  have h : ∑ p : σ × κ, w p ⊗ₜ[K] f (y p.2 p.1) = 0 := by
    rw [← hd, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy k, map_sum]
    have hsum (S : Finset σ) :
        (∑ s ∈ S, act (ω s ⊗ₜ[R] y k s)) (e k) =
          ∑ s ∈ S, act (ω s ⊗ₜ[R] y k s) (e k) := by
      classical
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih => simp [ha, ih]
    rw [hsum]
    exact Finset.sum_congr rfl fun s _ => (hact s k _).symm
  have h0 := UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero K V C (σ × κ) w hw _ h
  rw [hy k]
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hf _ (h0 (s, k)), TensorProduct.tmul_zero]

theorem _root_.UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hact κ _ b d hd k
  haveI : Module.Free ℤ_[l] ↥(OL LL) := inferInstance
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := inferInstance
  have hinj := (UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td LL).2
  refine abstract_indep (Module.Free.chooseBasis ℤ_[l] ↥(OL LL)) act
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) _
    (fun y => GlobalTheory.BKGal.JumpDR.cD Td y) (fun y hy => hinj (hy.trans (map_zero _).symm))
    (UpperTheory.KN.linearIndependent_Ql_integerBasis_smul_latticeBasis l LL T κ _ b (Module.Free.chooseBasis ℤ_[l] ↥(OL LL))) ?_ d hd k
  intro s k y
  refine (hact _ _ _ _).trans ?_
  rw [mul_one]
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsBdRPlusCoeffsOfMemFilZeroDeRham
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticePowerSmul
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowSmulMemAlt
private theorem UpperTheory.pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (c : K) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℚ_[l] c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hspec := PadicInt.unitCoeff_spec hy
  set u := PadicInt.unitCoeff hy
  have h3 : ((l : ℤ_[l]) ^ y.valuation) = (↑u⁻¹ : ℤ_[l]) * y := by
    rw [Units.eq_inv_mul_iff_mul_eq]
    exact hspec.symm
  have h4 : (l : K) ^ y.valuation * c = (↑u⁻¹ : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, ← h3, Algebra.smul_def, map_pow, map_natCast]
  rw [h4]
  exact hint.smul _

theorem UpperTheory.exists_pow_smul_mem_alt :
    ∀ {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K] {O : Type} [CommRing O] [Algebra O K] {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (T : Submodule O V), (∀ c : K, IsIntegral ℤ_[l] c → ∃ o : O, algebraMap O K o = c) → Submodule.span K (T : Set V) = ⊤ → ∀ v : V, ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  intro l _ K _ _ _ _ _ O _ _ V _ _ _ _ T hO hT v
  have hpow : ∀ (m : ℕ) (w : V), w ∈ T → (l : K) ^ m • w ∈ T := by
    intro m w hw
    have h : (l : K) ^ m = algebraMap O K ((l : O) ^ m) := by
      rw [map_pow, map_natCast]
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := hT ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact hpow _ _ ha
    · rw [pow_add, mul_smul]
      exact hpow _ _ hb
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨n, hn⟩ := UpperTheory.pow_mul_isIntegral (l := l) c
    obtain ⟨o, ho⟩ := hO _ hn
    refine ⟨n + a, ?_⟩
    have h : (l : K) ^ (n + a) • c • x = o • ((l : K) ^ a • x) := by
      rw [← algebraMap_smul K o, ho, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ ha
end

theorem UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (LL : Formalism.BasicNotions.Loc.FinExt l) (T : GlobalTheory.BKGal.QLat LL) (v : T.V),
      ∃ (n : ℕ), (↑l : ↥(↑LL : IntermediateField ℚ_[l] (Formalism.BasicNotions.Loc.Om l))) ^ n • v ∈ T.L.T := by
  intro l inst LL T v
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact UpperTheory.exists_pow_smul_mem_alt T.L.T (fun c hc => ⟨⟨c, hc⟩, rfl⟩) T.L.span v
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsPrimePowSmulMemLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem UpperTheory.KN.exists_pow_smul_mem_lattice_alt {l : ℕ} [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T :=
  _root_.UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt LL T v

theorem _root_.UpperTheory.KN.exists_prime_pow_smul_mem_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ (n : ℕ) (x : ↥T.L.T), (x : T.V) = ((l : ℚ_[l]) ^ n) • v := by
  intro l _ LL T v
  obtain ⟨n, hn⟩ := UpperTheory.KN.exists_pow_smul_mem_lattice_alt LL T v
  refine ⟨n, ⟨_, hn⟩, ?_⟩
  rw [← algebraMap_smul ↥LL.1 ((l : ℚ_[l]) ^ n) v, map_pow, map_natCast]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem span_abs {Q Z O D B V κ : Type} [CommRing Q] [CommRing Z] [CommRing O] [CommRing D]
    [CommRing B] [Algebra Z O] [Algebra Z D] [Algebra Q B] [AddCommGroup V] [Module Q V] [Module O V]
    [Fintype κ] (T : Submodule O V) (b : Module.Basis κ O T) (F : Submodule Q B) (c : D →+* B)
    (act : O ⊗[Z] D →+ (V ⊗[Q] B →+ V ⊗[Q] B))
    (hact : ∀ (o : O) (d : D) (v : V) (e : B),
      act (o ⊗ₜ[Z] d) (v ⊗ₜ[Q] e) = (o • v) ⊗ₜ[Q] (c d * e))
    (hF : ∀ x ∈ F, ∃ y, x = c y)
    (hT : ∀ (v : V) (y : D), ∃ (q : Q) (x : T) (y1 : D), (x : V) = q • v ∧ c y = q • c y1)
    (f : V ⊗[Q] F →+ V ⊗[Q] B) (hf : ∀ (v : V) (x : F), f (v ⊗ₜ[Q] x) = v ⊗ₜ[Q] (x : B))
    (y : V ⊗[Q] F) :
    ∃ d : κ → O ⊗[Z] D, f y = ∑ k, act (d k) (((b k : T) : V) ⊗ₜ[Q] (1 : B)) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a a' ha ha' =>
    obtain ⟨d, hd⟩ := ha
    obtain ⟨d', hd'⟩ := ha'
    refine ⟨d + d', ?_⟩
    rw [map_add (f := _), hd, hd', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, map_add (f := _), AddMonoidHom.add_apply]
  | tmul v x =>
    obtain ⟨y0, hy0⟩ := hF x x.2
    obtain ⟨q, t, y1, ht, hy⟩ := hT v y0
    refine ⟨fun k => b.repr t k ⊗ₜ[Z] y1, ?_⟩
    have h1 : (t : V) = ∑ k, b.repr t k • ((b k : T) : V) := by
      have h2 := congrArg T.subtype (b.sum_repr t).symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h2
      simpa only [map_smul, Submodule.subtype_apply] using h2
    rw [hf, hy0, hy, ← TensorProduct.smul_tmul, ← ht, h1, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hact, mul_one]

theorem _root_.UpperTheory.KN.exists_BdRPlus_coeffs_of_mem_filZero_deRham :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), ∀ v : T.V ⊗[ℚ_[l]] Pl.R.BdR, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) → ∃ d : κ → OD l ↥(OL LL), v = ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ LL T Pl AI Td act hact κ _ b v hv
  obtain ⟨y, rfl⟩ := hv
  refine span_abs (Q := ℚ_[l]) (Z := ℤ_[l]) T.L.T b
    (((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0).restrictScalars ℚ_[l]) (GlobalTheory.BKGal.JumpDR.cD Td) act
    ?_ ?_ ?_ (AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V)
      (((Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).Fil 0).restrictScalars ℚ_[l]).subtype).toAddMonoidHom ?_ y
  · intro o d v e
    refine (hact o d v e).trans ?_
    congr 1
    first | done | rfl | exact (algebraMap_smul (↥LL.1) o v)
  · intro x hx
    exact ((UpperTheory.KN.fil_zero_eq_range_cD_and_cD_injective l Pl AI Td (Formalism.MainNotions.ElementDenominator.qlExt l)).1 x).1 hx
  · intro v y
    obtain ⟨n, x, hx⟩ := UpperTheory.KN.exists_prime_pow_smul_mem_lattice l LL T v
    obtain ⟨z, hz⟩ := ((GlobalTheory.MemLoc.isUnit_l_BdRp l).pow n).exists_right_inv
    refine ⟨(l : ℚ_[l]) ^ n, x, z * y, hx, ?_⟩
    have h : y = ((l : ℕ) : Per.BdRp l) ^ n * (z * y) := by rw [← mul_assoc, hz, one_mul]
    conv_lhs => rw [h]
    rw [map_mul, map_pow, map_natCast, Algebra.smul_def, map_pow, map_natCast]
  · intro v x
    rfl
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonImageEisensteinPowPhiInvColumns
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonTransferBasisCoordinates
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonToBSmulEqDeRhamAct
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonAinfEqDeRhamComparison
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (w : Ainf l), GlobalTheory.BKGal.JumpDR.cB Td (acrisToBcris l (ainfToAcris l w)) = GlobalTheory.BKGal.JumpDR.cD Td (ainfToBdRp l w) := by
  intro l _ Pl AI Td w
  refine Td.eD.injective ?_
  have h := GlobalTheory.CrisIncl.incl_aB l _ Td.incl w
  refine Eq.trans h ?_
  exact (Td.eD.apply_symm_apply _).symm
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem smul_abstract {Z O A B D M N : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing B]
    [CommRing D] [Algebra Z O] [Algebra Z A] [Algebra Z B] [Algebra Z D] [AddCommGroup M] [Module O M]
    [AddCommGroup N] (fB : O ⊗[Z] A →ₐ[O] O ⊗[Z] B) (fD : O ⊗[Z] A →ₐ[O] O ⊗[Z] D)
    (gB : A → B) (gD : A → D) (hB : ∀ o w, fB (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gB w)
    (hD : ∀ o w, fD (o ⊗ₜ[Z] w) = o ⊗ₜ[Z] gD w)
    (X : (O ⊗[Z] B) ⊗[O] M →+ N) (act : O ⊗[Z] D →+ (N →+ N))
    (h : ∀ (o o' : O) (w : A) (b : B) (x : M),
      X (((o * o') ⊗ₜ[Z] (gB w * b)) ⊗ₜ[O] x) = act (o ⊗ₜ[Z] gD w) (X ((o' ⊗ₜ[Z] b) ⊗ₜ[O] x)))
    (c : O ⊗[Z] A) (y : (O ⊗[Z] B) ⊗[O] M) : X (fB c • y) = act (fD c) (X y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' hc hc' => rw [map_add (f := _), add_smul, map_add (f := _), hc, hc', map_add (f := _), map_add (f := _), AddMonoidHom.add_apply]
  | tmul o w =>
    rw [hB, hD]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => rw [smul_add, map_add (f := _), hy, hy', map_add (f := _), map_add (f := _)]
    | tmul r x =>
      induction r using TensorProduct.induction_on with
      | zero => simp
      | add r r' hr hr' => rw [TensorProduct.add_tmul, smul_add, map_add (f := _), hr, hr', map_add (f := _), map_add (f := _)]
      | tmul o' b =>
        rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, h]

theorem _root_.UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (c : OA l ↥(OL LL)) (y : TW (OB l ↥(OL LL)) T), X (toB l ↥(OL LL) c • y) = act (toOD l ↥(OL LL) c) (X y) := by
  intro l _ LL T Pl AI Td X hX act hact c y
  refine smul_abstract (toB l ↥(OL LL)) (toOD l ↥(OL LL)) (fun w => acrisToBcris l (ainfToAcris l w))
    (fun w => ainfToBdRp l w) (fun _ _ => rfl) (fun _ _ => rfl) X act (fun o o' w b x => ?_) c y
  refine (hX _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg (act _) (hX o' b x)).symm
  refine Eq.trans ?_ (hact _ _ _ _).symm
  have h1 : ((o * o' : ↥(OL LL)) : ↥LL.1) = (o : ↥LL.1) * (o' : ↥LL.1) := rfl
  rw [h1, mul_smul, map_mul, UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison l Pl AI Td w]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

private theorem sum_through_tensor_basis {O A B M V ι κ : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module O M] [AddCommGroup V] [Fintype ι] [DecidableEq ι] [Fintype κ]
    (f : A →ₐ[O] B) (jB : (ι → B) ≃ₗ[B] B ⊗[O] M) (X : B ⊗[O] M →+ V) (F : A → V → V)
    (hF : ∀ (c : A) (y : B ⊗[O] M), X (f c • y) = F c (X y))
    (c : ι → A) (r : κ → A) (x : κ → M)
    (h : jB (fun i => f (c i)) = TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k)) :
    ∑ j, F (c j) (X (jB (Pi.single j 1))) = ∑ k, F (r k) (X ((1 : B) ⊗ₜ[O] x k)) := by
  have e1 : (fun i => f (c i)) = ∑ j, f (c j) • (Pi.single j 1 : ι → B) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : TensorProduct.map f.toLinearMap LinearMap.id (∑ k, r k ⊗ₜ[O] x k) =
      ∑ k, f (r k) • ((1 : B) ⊗ₜ[O] x k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [TensorProduct.smul_tmul']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, e2, map_sum] at h
  have h2 := congrArg X h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hF] at h2
  exact h2

theorem _root_.UpperTheory.KN.crisComparison_transfer_basis_coordinates :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (c : ι → OA l ↥(OL LL)) (r : κ → OA l ↥(OL LL)) (x : κ → ↥T.L.T), I.j (inclL (thetaW a LL) ϖ P c) = TWincl (inclO l ↥(OL LL)) T (∑ k, r k ⊗ₜ[↥(OL LL)] x k) → ∑ j, act (toOD l ↥(OL LL) (c j)) (X (jB (Pi.single j 1))) = ∑ k, act (toOD l ↥(OL LL) (r k)) (((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact κ _ c r x h
  have hF := UpperTheory.KN.crisComparison_toB_smul_eq_deRham_act l LL T Pl AI Td X hX act hact
  have h1 := hcmp c _ h
  have h2 := sum_through_tensor_basis (toB l ↥(OL LL)) jB X (fun c v => act (toOD l ↥(OL LL) c) v) hF c r x h1
  refine h2.trans (Finset.sum_congr rfl fun k _ => ?_)
  have h3 : X ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x k) =
      ((x k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR) := by
    refine (hX 1 1 (x k)).trans ?_
    rw [map_one, OneMemClass.coe_one, one_smul]
  exact congrArg (fun v => act (toOD l ↥(OL LL) (r k)) v) h3
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.InclLEisensteinPowPhiInvEqSingle
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), inclL (thetaW a LL) ϖ P (fun j => ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩)) = Pi.single i (inclO l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩))) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P β hβ i
  ext i'
  rw [inclL_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, ← ϖ.iW_of_mem (thetaW a LL) ↥LL.1, frobMat, Matrix.map_apply,
    Matrix.of_apply, ← map_mul, ← map_sum]
  simp only [Pi.single_apply]
  have key : ∀ i' i τ, ∑ j, P.mx τ i' j * (E ↥LL.1 l e ^ β * P.mxInv τ j i) =
      E ↥LL.1 l e ^ β * (1 : Matrix ι ι _) i' i := by
    intro i' i τ
    rw [← P.mx_mul_mxInv τ, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  split_ifs with h
  · subst h
    refine congrArg _ (funext fun τ => Subtype.ext ?_)
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i' τ
    rw [Matrix.one_apply_eq, mul_one] at h1
    exact h1
  · have hz : ∀ F : ZMod a → invE l e (A ↥(OL LL) ↥LL.1), (∀ τ, ((F τ : invE l e (A ↥(OL LL) ↥LL.1)) : PowerSeries ↥LL.1) = 0) →
        ϖ.iW (thetaW a LL) ↥LL.1 F = 0 := fun F hF => by
      have hF0 : F = 0 := funext fun τ => Subtype.ext (hF τ)
      rw [hF0]
      exact map_zero _
    refine hz _ fun τ => ?_
    rw [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]
    have h1 := key i' i τ
    rw [Matrix.one_apply_ne h, mul_zero] at h1
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ITotEisensteinPowEqIDEisensteinHatPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (β : ℕ), toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩)) = ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β := by
  intro l _ a e _ _ ϖ LL _ _ β
  refine (ϖ.iD_ofA (thetaW a LL) ↥LL.1 _).symm.trans ?_
  refine Eq.trans ?_ (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) _ β)
  refine congrArg (ϖ.iD (thetaW a LL) ↥LL.1) ?_
  funext τ
  exact map_pow (ofA ↥(OL LL) ↥LL.1 l e) ⟨E ↥LL.1 l e, E_mem l e _⟩ β
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

private theorem tensor_inclusion_smul_sum {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (s : R) {κ : Type} [Fintype κ] (r : κ → R) (x : κ → ↥T.L.T) :
    TWincl f T (∑ k, (s * r k) ⊗ₜ[O] x k) = f s • TWincl f T (∑ k, r k ⊗ₜ[O] x k) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [TWincl, TensorProduct.smul_tmul']

private theorem ennreal_volume_ratio_step_cancel {R W ι : Type} [CommRing R] [AddCommGroup W] [Fintype ι] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u : R) (hu : IsUnit u) (y z y' z' : ι → R) (v w : ι → W) (hy : ∀ j, y' j = u * y j)
    (hz : ∀ j, z' j = u * z j) (h : ∑ j, act (y' j) (v j) = ∑ k, act (z' k) (w k)) :
    ∑ j, act (y j) (v j) = ∑ k, act (z k) (w k) := by
  obtain ⟨u, rfl⟩ := hu
  have h2 := congrArg (act ((u⁻¹ : Rˣ) : R)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hy, hz, ← hmul, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact h2

private theorem tame_lattice_inclusion (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (i : ι) (y : ι → OA l O) (s u : OA l O)
    (r : ι → OA l O) (x : ι → ↥T.L.T) (hI : inclL t ϖ P y = Pi.single i (inclO l O s))
    (hj : I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T (∑ k, r k ⊗ₜ[O] x k)) :
    I.j (inclL t ϖ P (fun j => u * y j)) = TWincl (inclO l O) T (∑ k, (s * r k) ⊗ₜ[O] x k) := by
  have h1 : inclL t ϖ P (fun j => u * y j) = inclO l O s • inclV l O ι (Pi.single i u) := by
    have h2 : inclL t ϖ P (fun j => u * y j) = inclO l O u • inclL t ϖ P y := by
      rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
      congr 1
      funext j
      simp
    rw [h2, hI]
    funext j
    change inclO l O u * _ = inclO l O s * inclO l O ((Pi.single i u : ι → OA l O) j)
    by_cases hij : j = i
    · subst hij
      rw [Pi.single_eq_same, Pi.single_eq_same, mul_comm]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero, mul_zero, mul_zero]
  rw [h1, I.j.map_smul, hj]
  exact (tensor_inclusion_smul_sum (inclO l O) T s r x).symm

private theorem cancel_unit_in_sum_action {A R W ι : Type} [CommRing A] [CommRing R] [AddCommGroup W] [Fintype ι]
    (f : A → R) (hf : ∀ x y, f (x * y) = f x * f y) (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u s : A) (s' : R) (hs : f s = s') (hu : IsUnit (f u)) (y r : ι → A) (m : ι → R)
    (hr : ∀ k, f (r k) = f u * m k) (v w : ι → W)
    (h : ∑ j, act (f (u * y j)) (v j) = ∑ k, act (f (s * r k)) (w k)) :
    ∑ j, act (f (y j)) (v j) = ∑ k, act (s' * m k) (w k) :=
  ennreal_volume_ratio_step_cancel act hmul hone (f u) hu _ _ _ _ v w (fun j => hf _ _)
    (fun k => by rw [hf, hs, hr, mul_left_comm]) h

theorem _root_.UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (b : Module.Basis ι ↥(OL LL) ↥T.L.T) (m : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) → (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) → (∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k) → ∀ (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))) = ∑ k, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β * m i k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact b m u r hu hj hr β hβ i
  have hact' := GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hact
  have hI := UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single l a e ϖ LL ι P β hβ i
  have hE := UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow l a e ϖ LL β
  have h3 := tame_lattice_inclusion l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I i _ _ u (r i) (fun k => b k) hI (hj i)
  have h4 := UpperTheory.KN.crisComparison_transfer_basis_coordinates l a e ϖ LL ι P T I jB Pl AI Td hcmp X hX act hact ι _ _ _ h3
  have h5 := cancel_unit_in_sum_action (toOD l ↥(OL LL)) (map_mul (toOD l ↥(OL LL))) act hact'.1 hact'.2 u _ _ hE hu _ (r i) (m i)
    (hr i) _ _ h4
  exact h5
end
