module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.CrystallineCyclotomic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocUnitApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Formalism.GaloisCohomology.Statement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdealCharacterLContinuationNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqMulIntegralClosureOfSeparableInvolutionAlgebra
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedOddDegreeQuadraticLocalExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem aeval_ne_zero_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : aeval π p ≠ 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have hπ0 : π ≠ 0 := by
    rw [← norm_pos_iff, hπ]; positivity
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  intro h
  rw [aeval_eq_sum_range' (Nat.lt_succ_self _)] at h
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = 0 := by
    rw [← h]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs, nnnorm_zero] at h6
  have hm : p.natDegree ∈ p.support := natDegree_mem_support_of_nonzero hp
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hm
  rw [← h6] at h7
  obtain ⟨n, hn⟩ := key _ hm
  have h8 : ‖p.coeff p.natDegree • π ^ p.natDegree‖ ≤ 0 := h7
  rw [hn] at h8
  exact absurd h8 (not_le.2 (by positivity))

theorem minpoly_unramifiedSubfield_eq_cyclotomic (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) : minpoly ↥(K0 K) ζ = cyclotomic (l ^ j) ↥(K0 K) := by
  have hlp : l.Prime := Fact.out
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot : aeval ζ (cyclotomic (l ^ j) ↥(K0 K)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
    (minpoly.dvd _ _ hroot)
  rw [natDegree_cyclotomic]
  by_contra hlt
  push_neg at hlt
  refine aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 (minpoly ↥(K0 K) ζ)) ?_ ?_ ?_
  · intro h
    exact minpoly.ne_zero hint (taylor_injective 1 (by rw [h, map_zero]))
  · rwa [natDegree_taylor]
  · rw [taylor_apply, aeval_comp]
    simp

theorem exists_primitiveRoot_Om (j : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ j) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  haveI : CharZero (Om l) := algebraRat.charZero _
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ j)

theorem Ks_eq_restrictScalars (K : FinExt l) (j : ℕ) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    Ks K j = ((↥(K0 K))⟮ζ⟯).restrictScalars ℚ_[l] := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, Ks]
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

theorem finrank_Ks (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ]
  have h1 : Module.finrank ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯) = (l - 1) * l ^ (j - 1) := by
    rw [IntermediateField.adjoin.finrank hint, minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ,
      natDegree_cyclotomic, Nat.totient_prime_pow hlp hj, mul_comm]
  rw [← h1]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯)).symm

theorem exists_chi_approx (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) (j : ℕ) (hj : 1 ≤ j) :
    ∃ g ∈ (K0 K).fixingSubgroup, ‖(χ g : ℚ_[l]) - u‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  let z : ℤ_[l] := ⟨u, hu.le⟩
  set a := z.appr j with ha
  have hza : ‖u - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).2 (PadicInt.appr_spec j z)
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  have hlt : (l : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hl1 (by omega)
  have hna : ‖(a : ℚ_[l])‖ = 1 := by
    have h1 : (a : ℚ_[l]) = u + -(u - a) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, hu, norm_neg,
      max_eq_left (hza.trans hlt.le)]
    rw [hu, norm_neg]
    exact (hza.trans_lt hlt).ne'
  have hcop : a.Coprime (l ^ j) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hlp.coprime_iff_not_dvd]
    intro hd
    have : ‖((a : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (by exact_mod_cast hd)
    rw [Int.cast_natCast, hna] at this
    exact lt_irrefl _ this
  have hζa := hζ.pow_of_coprime a hcop
  have hconj : IsConjRoot ↥(K0 K) (ζ ^ a) ζ := by
    unfold IsConjRoot
    rw [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, minpoly_unramifiedSubfield_eq_cyclotomic K j hj _ hζa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ.restrictScalars ℚ_[l], fun x => σ.commutes x, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hχ (σ.restrictScalars ℚ_[l]) j ζ hζ.pow_eq_one
  have hab : ζ ^ a = ζ ^ b := hσ.symm.trans hb'
  have hmod : a ≡ b [MOD l ^ j] := by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hpos.ne').pow_eq_pow_iff_modEq.1 hab
  have hba : ‖(b : ℚ_[l]) - a‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd ((b : ℤ) - a) j (p := l)).2
      (by exact_mod_cast hmod.dvd)
    simpa using this
  have h1 : (χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - u =
      ((χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - b) + (((b : ℚ_[l]) - a) + -(u - a)) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hba ?_)
  rwa [norm_neg]

theorem exists_chi_eq (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) : ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hcont := (cyc_basic l χ hχ).2.1
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  have hcl : IsClosed ((K0 K).fixingSubgroup : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed _
  have hc := (hcl.isCompact.image hcont).isClosed
  have hmem : u ∈ (fun g => (χ g : ℚ_[l])) '' ((K0 K).fixingSubgroup : Set (GQ l)) := by
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
    obtain ⟨g, hg, hg'⟩ := exists_chi_approx K χ hχ u hu (n + 1) (by omega)
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine hg'.trans_lt (lt_of_le_of_lt ?_ hn)
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hl1.le (by push_cast; omega)
  exact hmem

theorem finrank_Ks_and_chi_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧
    ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 →
      ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u :=
  fun _ _ K => ⟨finrank_Ks K, exists_chi_eq K⟩

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cyclotomicExt_and_cyclotomicChar_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) = Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧ ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 → ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  first | exact @GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | exact GlobalTheory.Cyc.finrank_Ks_and_chi_surjective | (intros; apply GlobalTheory.Cyc.finrank_Ks_and_chi_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.KernelDictionary
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} (R : Fr l O)

def diag (n : ℕ) (a : O⟦X⟧) : LetA O n := fun _ => a

def KillsN {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (i : ZMod n) (a : O⟦X⟧) : Prop :=
  ∀ y ∈ W.Nl T' i, ∃ x ∈ W.Nl T i, W.map f x = diag n a • y

variable [NeZero n] {R} (jE : R.EE →ₐ[O] W.EE)

def vec {T : LocLat G Qp LL O} {r : ℕ} (b : ZMod n → Fin r → W.DD T) (x : DD R n r) : W.DD T :=
  ∑ i, ∑ k, jE (x i k) • b i k

end Generic

variable {l : ℕ} [Fact l.Prime]

instance finiteDimensional_maxUnramifiedSubfield (K : FinExt l) : FiniteDimensional ℚ_[l] ↥(K0 K) :=
  haveI := K.2
  FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))

end GlobalTheory.IndefiniteRowSideFullHecke.KernelDictionary
end
end

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB

namespace GlobalTheory.TrivCrys

open Module TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

private theorem lid_rTensor_map_id_eq {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] (f : V →ₗ[Qp] Qp) (σ : B →ₗ[Qp] B) (x : V ⊗[Qp] B) :
    TensorProduct.lid Qp B (LinearMap.rTensor B f
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) σ x)) =
      σ (TensorProduct.lid Qp B (LinearMap.rTensor B f x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [AlgebraTensorModule.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem eq_sum_basis_tmul_coord {V : Type} [AddCommGroup V] [Module Qp V] {ι : Type}
    [Fintype ι] (b : Basis ι Qp V) (x : V ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
    simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem _root_.GlobalTheory.TrivCrys.dcris_of_trivial {V : Type} [AddCommGroup V] [Module Qp V]
    [Module LL V] [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) :
    _root_.Formalism.WeaklyAdmissibleFiltrations.Dcris PD ρ =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  have hid : ∀ g, ρ g = LinearMap.id := fun g => LinearMap.ext (hρ g)
  ext x
  rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.mem_Dcris, LinearMap.mem_range]
  constructor
  · intro hx
    let b := Module.finBasis Qp V
    have hc : ∀ i, ∃ k : K₀, algebraMap K₀ B k =
        TensorProduct.lid Qp B (LinearMap.rTensor B (b.coord i) x) := by
      intro i
      refine (_root_.GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.invariantsEq PD _).mp fun g => ?_
      have h := hx g
      unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB at h
      rw [hid g] at h
      conv_rhs => rw [← h]
      rw [lid_rTensor_map_id_eq]
      rfl
    choose k hk using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] k i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, eq_sum_basis_tmul_coord b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [AlgebraTensorModule.map_tmul, ← hk i]
    rfl
  · rintro ⟨y, rfl⟩ g
    unfold _root_.Formalism.WeaklyAdmissibleFiltrations.actVB
    rw [hid g]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem _root_.GlobalTheory.TrivCrys.isCrys_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) : _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply PD.not_mem_filtration_two
    rw [Subsingleton.elim PD.t 0, map_zero]
    exact zero_mem _
  have key : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) =
      ⇑(LinearMap.lTensor V (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m k => simp [AlgebraTensorModule.map_tmul]
    | add u w hu hw => simp only [map_add (f := _), hu, hw]
  have hinj : Function.Injective (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
    rw [key]
    exact Module.Flat.lTensor_preserves_injective_linearMap _
      (fun a c h => (algebraMap K₀ B).injective h)
  unfold _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys
  rw [_root_.GlobalTheory.TrivCrys.dcris_of_trivial PD ρ hρ, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_tensorProduct, mul_comm]

theorem _root_.GlobalTheory.TrivCrys.isCrys_lat_of_trivial : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] [FiniteDimensional Qp LL] (U : _root_.Formalism.BasicNotions.LocLat G Qp LL O), (∀ g x, U.ρ g x = x) → _root_.Formalism.WeaklyAdmissibleFiltrations.IsCrys PD U.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ U hU
  haveI := U.fdim
  haveI : FiniteDimensional Qp U.V := Module.Finite.trans LL U.V
  exact _root_.GlobalTheory.TrivCrys.isCrys_of_trivial PD U.ρ hU

end GlobalTheory.TrivCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKer
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem units_adicCompletion_hom_ext (F : Type) [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B)
    (hf : IsOpen (f.ker : Set (v.adicCompletion F)ˣ))
    (hg : IsOpen (g.ker : Set (v.adicCompletion F)ˣ))
    (hc : ∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) =
      g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) :
    ∀ x, f x = g x := by
  intro x
  set S : Set (v.adicCompletion F)ˣ :=
    (fun y => x⁻¹ * y) ⁻¹' ((f.ker : Set (v.adicCompletion F)ˣ) ∩ g.ker) with hS
  have hSo : IsOpen S := (hf.inter hg).preimage (continuous_const.mul continuous_id)
  have hxS : x ∈ S := by simp [hS, MonoidHom.mem_ker]
  obtain ⟨U, hU, hUS⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hSo
  have hxU : (x : v.adicCompletion F) ∈ U := by
    rw [← hUS] at hxS; exact hxS
  have hU0 : IsOpen (U ∩ {0}ᶜ) := hU.inter isOpen_compl_singleton
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open
    hU0 ⟨x, hxU, by simp⟩
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hk.2 (by simp)
  set c : Fˣ := Units.mk0 k hk0
  have hcS : Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c ∈ S := by
    rw [← hUS]; simpa [c] using hk.1
  simp only [hS, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, MonoidHom.mem_ker,
    map_mul, map_inv] at hcS
  have h1 : f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = f x := by
    have := hcS.1; rw [inv_mul_eq_one] at this; exact this.symm
  have h2 : g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g x := by
    have := hcS.2; rw [inv_mul_eq_one] at this; exact this.symm
  rw [← h1, ← h2, hc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitsAdicCompletionHomExtOfIsOpenKerStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (B : Type) [Group B] (f g : (v.adicCompletion F)ˣ →* B), IsOpen (f.ker : Set (v.adicCompletion F)ˣ) → IsOpen (g.ker : Set (v.adicCompletion F)ˣ) → (∀ c : Fˣ, f (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c) = g (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom c)) → ∀ x, f x = g x := by
  first | exact @GlobalTheory.units_adicCompletion_hom_ext | exact GlobalTheory.units_adicCompletion_hom_ext | (intros; apply GlobalTheory.units_adicCompletion_hom_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycle
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

theorem exists_descend_pair_quotient {Γ M : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [TopologicalSpace M] (N : Subgroup Γ) (w : Γ × Γ → M)
    (hw : Continuous w) (h : ∀ g h : Γ, ∀ n ∈ N, ∀ n' ∈ N, w (g * n, h * n') = w (g, h)) :
    ∃ W : (Γ ⧸ N) × (Γ ⧸ N) → M, Continuous W ∧
      ∀ g h : Γ, W ((g : Γ ⧸ N), (h : Γ ⧸ N)) = w (g, h) := by
  refine ⟨fun p => Quotient.liftOn₂' p.1 p.2 (fun a b => w (a, b)) ?_, ?_, fun g h => rfl⟩
  · intro a b a' b' ha hb
    have e := h a b _ (QuotientGroup.leftRel_apply.1 ha) _ (QuotientGroup.leftRel_apply.1 hb)
    simpa using e.symm
  · rw [((QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
      (QuotientGroup.isOpenQuotientMap_mk (N := N))).isQuotientMap.continuous_iff]
    exact hw

theorem sum_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  intro hPT F Ω _ _ _ _ _ _ l _ ζ hζ
  obtain ⟨inv, hinv, H⟩ := hPT.annihilators F Ω l 1 one_pos ζ hζ
  refine ⟨inv, hinv, fun S hS Av hA w hw wl hwl => ?_⟩
  obtain ⟨μ, hμ⟩ := exists_lift_cycMod (Ω := Ω) (r := 1) hS
  obtain ⟨W, hWc, hW⟩ := exists_descend_pair_quotient _ w.1 w.2.1 hw
  have hmem : W ∈ Z2 (charRep μ) := by
    refine ⟨hWc, fun g h k => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective h
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
    have e := w.2.2 g h k
    have e2 : μ (g : G F Ω ⧸ _) = cycMod F Ω l 1 g := DFunLike.congr_fun hμ g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hW, hW, hW, hW, charRep_apply, e2]
    exact e
  have e := (H S hS (fun v => Av v.1) (fun v => hA v.1) μ hμ).1
    (Submodule.Quotient.mk ⟨W, hmem⟩)
  rw [← Finset.sum_coe_sort]
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) e
  refine congrArg (inv (Av v.1)) ?_
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => ?_))
  exact (hwl v.1 p.1 p.2).trans (hW _ _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumInvEqZeroOfUnramifiedCocycleStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_local_inv_eq_zero_of_unramified_cocycle : PoitouTateTotallyComplex → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ζ : Ω), IsPrimitiveRoot ζ (l ^ 1) → ∃ inv : InvFam F Ω l 1, IsLocalInvariants ζ inv ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ContainsAbove S l → ∀ Av : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v) → ∀ w : Z2 (muRep F Ω l 1), (∀ g h : G F Ω, ∀ n ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), ∀ n' ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 F))), w.1 (g * n, h * n') = w.1 (g, h)) → ∀ wl : ∀ v, Z2 (muLoc F l 1 (Av v)), (∀ v (g h : Dec (F := F) (Av v)), (wl v).1 (g, h) = w.1 ((g : G F Ω), (h : G F Ω))) → ∑ v ∈ S, inv (Av v) (Submodule.Quotient.mk (wl v)) = 0 := by
  first | exact @GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | exact GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle | (intros; apply GlobalTheory.sum_inv_eq_zero_of_unramified_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZero
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory

private lemma dedekindZeta_eq_exp_tsum_neg_log (K : Type) [Field K] [NumberField K] (s : ℂ)
    (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  have hs0 : -s ≠ 0 := by
    intro h
    rw [neg_eq_zero.mp h] at hs
    norm_num at hs
  have key := _root_.GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs
  rw [_root_.GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs]
  convert key using 1
  · refine tsum_congr fun I => ?_
    by_cases hI : I = ⊥
    · simp [hI, Complex.zero_cpow hs0]
    · simp [hI]
  · congr 1
    refine tsum_congr fun P => ?_
    simp [P.ne_bot]

theorem _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero :
    ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  intro K _ _
  obtain ⟨Z, hZd, hZ⟩ := _root_.GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire K
  refine ⟨Z, hZd, ?_, hZ⟩
  have h1 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := hZd.continuous.comp Complex.continuous_ofReal
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
    refine (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < (s : ℂ).re := by simpa using hs
    rw [hZ s hs', dedekindZeta_eq_exp_tsum_neg_log K s hs']
  rw [tendsto_nhds_unique h1 h2]
  exact_mod_cast dedekindZeta_residue_ne_zero K

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZeroStatement
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  exact @GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLatDVR

theorem isReduced_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) :
    IsReduced A := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨f, rfl⟩ := exists_aeval_eq_of_charpoly_separable g hP a
  obtain ⟨m, hm⟩ := ha
  have hf : aeval (LinearMap.mulLeft E g) (f ^ m) = 0 := by
    have h2 : aeval g (f ^ m) = 0 := by rw [map_pow, hm]
    have := aeval_algHom_apply (Algebra.lmul E A) g (f ^ m)
    rw [h2, map_zero] at this
    exact this
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  rw [← pow_mul] at h1
  obtain ⟨q, hq⟩ := hP.squarefree.isRadical _ _ h1
  have hc : aeval g (LinearMap.mulLeft E g).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g)
    have h' : Algebra.lmul E A (aeval g (LinearMap.mulLeft E g).charpoly) = 0 := by
      rw [← aeval_algHom_apply]; exact h
    simpa using congrArg (fun F : Module.End E A => F 1) h'
  rw [hq, map_mul, hc, zero_mul]

theorem isPrincipalIdealRing_integralClosure_field {O E L : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [Field L]
    [Algebra E L] [Algebra O L] [IsScalarTower O E L] [FiniteDimensional E L] :
    IsPrincipalIdealRing (integralClosure O L) := by
  haveI : IsDedekindDomain (integralClosure O L) :=
    GlobalTheory.isDedekindDomain_integralClosure_of_dimensionLEOne E
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O E L]
    exact (algebraMap E L).injective.comp (IsFractionRing.injective O E)
  haveI : Module.IsTorsionFree O (integralClosure O L) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => hinj (congrArg Subtype.val h)
  apply IsPrincipalIdealRing.of_finite_primes
  have hfin := IsDedekindDomain.primesOver_finite (IsLocalRing.maximalIdeal O) (integralClosure O L)
  refine (hfin.insert ⊥).subset ?_
  intro P hP
  by_cases h : P = ⊥
  · exact Or.inl h
  · right
    haveI : P.IsPrime := hP
    have hne : P.comap (algebraMap O (integralClosure O L)) ≠ ⊥ := fun h0 => h (Ideal.eq_bot_of_comap_eq_bot h0)
    have hmax : (P.comap (algebraMap O (integralClosure O L))).IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime hne inferInstance
    refine ⟨hP, ⟨?_⟩⟩
    exact (IsLocalRing.eq_maximalIdeal hmax).symm

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    exact isPrincipalIdealRing_integralClosure_field (E := E)
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (PrincipalLat.isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N →
    (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) →
    ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep N hN hst
  haveI := isReduced_of_charpoly_separable g hsep
  haveI := isPrincipalIdealRing_integralClosure (O := O) (E := E) (A := A)
  exact PrincipalLat.eq_mulLat_of_isPrincipalIdealRing N hN hst

end GlobalTheory.UnitLemma.PrincipalLatDVR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparablStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N → (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) → ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | exact GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | (intros; apply GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnity
open Polynomial IsLocalRing

namespace GlobalTheory.UnitLemma.InvolRes

theorem residue_pow_and_roots : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ),
    Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) →
    (∃ x, residue S (τ x) ≠ residue S x) →
    (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  intro S _ _ _ M hM τ hττ hne
  let e : S ≃+* S := RingEquiv.ofRingHom τ τ (RingHom.ext hττ) (RingHom.ext hττ)
  let s := ResidueField.mapEquiv e
  have hs : ∀ x, s (residue S x) = residue S (τ x) := fun x => rfl
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  haveI := hp
  haveI : Fact p.Prime := ⟨CharP.char_is_prime (ResidueField S) p⟩
  obtain ⟨-, hsq⟩ := GlobalTheory.UnitLemma.UnrExt.invol_eq_pow p hM s (fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [hs, hs, hττ]) (by
    obtain ⟨x, hx⟩ := hne
    exact ⟨residue S x, by rw [hs]; exact hx⟩)
  have h1 : ∀ x, residue S (τ x) = residue S x ^ M := fun x => by rw [← hs, hsq]
  refine ⟨h1, fun w hw => ?_⟩
  have hcard2 : 2 ≤ M ^ 2 := by
    have : 1 < Nat.card (ResidueField S) := Finite.one_lt_card
    omega
  set N := M ^ 2 - 1 with hN
  have hNk : (N : ResidueField S) ≠ 0 := by
    haveI := Fintype.ofFinite (ResidueField S)
    have h0 : ((N + 1 : ℕ) : ResidueField S) = 0 := by
      rw [show N + 1 = M ^ 2 by omega, ← hM, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    intro h
    simp [h] at h0
  refine GlobalTheory.UnitLemma.UnrExt.root_unique (residue S) (ker_residue) (X ^ N - 1 : S[X])
    (by simpa using X_pow_sub_one_separable_iff.2 hNk) (a := τ w) (b := w ^ M) ?_ ?_ ?_
  · simp [← map_pow, hw]
  · simp only [eval_sub, eval_pow, eval_X, eval_one]
    rw [← pow_mul, mul_comm, pow_mul, hw, one_pow, sub_self]
  · rw [h1, map_pow]

end GlobalTheory.UnitLemma.InvolRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionResiduePowAndRootsOfUnityStatement
open Polynomial IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.involution_residue_pow_and_roots_of_unity : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ), Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) → (∃ x, residue S (τ x) ≠ residue S x) → (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by
  first | exact @GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | exact GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots | (intros; apply GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZero
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_pos_of_totallyPositive (E E' : Type) [Field E] [NumberField E] [Field E']
    [NumberField E'] [Algebra E E'] (a : E') (ha : a ≠ 0) (hpos : ∀ φ : E' →+* ℝ, 0 < φ a)
    (φ : E →+* ℝ) : 0 < φ (Algebra.norm E a) := by
  letI : Algebra E ℂ := (Complex.ofRealHom.comp φ).toAlgebra
  have hmap : ∀ x, algebraMap E ℂ x = ((φ x : ℝ) : ℂ) := fun x => rfl
  have key := Algebra.norm_eq_prod_embeddings E ℂ a
  let g : (E' →ₐ[E] ℂ) → (E' →ₐ[E] ℂ) := fun σ =>
    { (starRingEnd ℂ).comp σ.toRingHom with
      commutes' := fun x => by
        show (starRingEnd ℂ) (σ (algebraMap E E' x)) = algebraMap E ℂ x
        rw [σ.commutes, hmap, Complex.conj_ofReal] }
  have hg : ∀ σ x, g σ x = (starRingEnd ℂ) (σ x) := fun σ x => rfl
  have hne : ∀ σ : E' →ₐ[E] ℂ, σ a ≠ 0 := fun σ => (map_ne_zero σ).2 ha
  have hnorm : ∀ σ : E' →ₐ[E] ℂ, ((‖σ a‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    exact_mod_cast (norm_ne_zero_iff.2 (hne σ))
  have h1 : ∏ σ : E' →ₐ[E] ℂ, σ a / ((‖σ a‖ : ℝ) : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => g σ) ?_ ?_ (fun _ _ => Finset.mem_univ _) ?_
    · intro σ _
      rw [hg, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj, div_eq_one_iff_eq
        (mul_ne_zero (hnorm σ) (hnorm σ)), Complex.normSq_eq_norm_sq]
      push_cast; ring
    · intro σ _ hf hgs
      apply hf
      have hreal : ComplexEmbedding.IsReal σ.toRingHom := by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact congrArg (fun τ : E' →ₐ[E] ℂ => τ x) hgs
      have hc : σ a = ((hreal.embedding a : ℝ) : ℂ) := (hreal.coe_embedding_apply a).symm
      have hp := hpos hreal.embedding
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
      exact div_self (by exact_mod_cast hp.ne')
    · intro σ _
      ext x
      simp [hg]
  rw [Finset.prod_div_distrib, div_eq_one_iff_eq (Finset.prod_ne_zero_iff.2 fun σ _ => hnorm σ)]
    at h1
  rw [h1, hmap] at key
  have hr : φ (Algebra.norm E a) = ∏ σ : E' →ₐ[E] ℂ, ‖σ a‖ := by
    apply Complex.ofReal_injective
    rw [key]; push_cast; rfl
  rw [hr]
  exact Finset.prod_pos fun σ _ => norm_pos_iff.2 (hne σ)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTotallyPositiveOfTotallyPositiveNeZeroStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (a : E'), a ≠ 0 → (∀ φ : E' →+* ℝ, 0 < φ a) → ∀ φ : E →+* ℝ, 0 < φ (Algebra.norm E a) := by
  first | exact @GlobalTheory.norm_pos_of_totallyPositive | exact GlobalTheory.norm_pos_of_totallyPositive | (intros; apply GlobalTheory.norm_pos_of_totallyPositive <;> assumption)
end
end
