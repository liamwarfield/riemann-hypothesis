module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtension
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

variable {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E}

def intMap (hU : IsUnrExt K K' d φ) : K.O →+* K'.O where
  toFun a := Classical.choose (exists_int_image hU a)
  map_one' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 1)]; simp)
  map_mul' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a * b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_mul, h2, h3])
  map_zero' := IsFractionRing.injective K'.O K'.E (by
    rw [Classical.choose_spec (exists_int_image hU 0)]; simp)
  map_add' a b := IsFractionRing.injective K'.O K'.E (by
    have h1 := Classical.choose_spec (exists_int_image hU (a + b))
    have h2 := Classical.choose_spec (exists_int_image hU a)
    have h3 := Classical.choose_spec (exists_int_image hU b)
    rw [h1]; simp only [map_add (f := _), h2, h3])

theorem intMap_spec (hU : IsUnrExt K K' d φ) (a : K.O) :
    algebraMap K'.O K'.E (intMap hU a) = φ (algebraMap K.O K.E a) :=
  Classical.choose_spec (exists_int_image hU a)

theorem intMap_injective (hU : IsUnrExt K K' d φ) : Function.Injective (intMap hU) := by
  intro a b h
  apply IsFractionRing.injective K.O K.E
  apply φ.injective
  rw [← intMap_spec hU, ← intMap_spec hU, h]

theorem val_mul_ne (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]; ring

theorem val_irreducible (K : UQ) {ϖ : K.O} (h : Irreducible ϖ) : val K.O (algebraMap K.O K.E ϖ) = 1 := by
  unfold val
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ h.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 h), WithZero.log_exp]; rfl

theorem val_pow_ne (K : UQ) {x : K.E} (hx : x ≠ 0) (n : ℕ) : val K.O (x ^ n) = n * val K.O x := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_ne K (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem val_isUnit (K : UQ) {u : K.O} (hu : IsUnit u) : val K.O (algebraMap K.O K.E u) = 0 := by
  obtain ⟨w, rfl⟩ := hu
  have h1 : (algebraMap K.O K.E (w : K.O)) ≠ 0 := by simp
  have h2 : (algebraMap K.O K.E ((w⁻¹ : K.Oˣ) : K.O)) ≠ 0 := by simp
  have h := val_mul_ne K h1 h2
  rw [← map_mul, Units.mul_inv, map_one] at h
  have h3 := val_algebraMap_nonneg K (w : K.O)
  have h4 := val_algebraMap_nonneg K ((w⁻¹ : K.Oˣ) : K.O)
  have h5 : val K.O (1 : K.E) = 0 := by simp [val]
  omega

theorem irreducible_of_val_one (K : UQ) {x : K.O} (hx : val K.O (algebraMap K.O K.E x) = 1) :
    Irreducible x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp [val] at hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have hu0 : algebraMap K.O K.E (u : K.O) ≠ 0 := by simp
  rw [map_mul, map_pow, val_mul_ne K hu0 (pow_ne_zero _ hϖ0), val_pow_ne K hϖ0,
    val_isUnit K u.isUnit, val_irreducible K hϖ] at hx
  have hn : n = 1 := by omega
  subst hn
  rw [pow_one]
  exact (irreducible_units_mul u).2 hϖ

theorem map_maximalIdeal (hU : IsUnrExt K K' d φ) :
    Ideal.map (intMap hU) (IsLocalRing.maximalIdeal K.O) = IsLocalRing.maximalIdeal K'.O := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have h1 := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have h2 : Irreducible (intMap hU ϖ) :=
    irreducible_of_val_one K' (by rw [intMap_spec, hU.2.2.1, val_irreducible K hϖ])
  rw [h1, Ideal.map_span, Set.image_singleton,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 h2]


open scoped nonZeroDivisors in
theorem exists_trace_unit_of_span (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ)
    (hB : ∃ u : Fin d → K'.O, ∀ y : K'.O, ∃ a : Fin d → K.O,
      algebraMap K'.O K'.E y = ∑ i, φ (algebraMap K.O K.E (a i)) * algebraMap K'.O K'.E (u i)) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.O := (intMap hU).toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K.O K'.O K'.E := IsScalarTower.of_algebraMap_eq fun a => (intMap_spec hU a).symm
  have hmap : ∀ a : K.O, algebraMap K.O K'.O a = intMap hU a := fun _ => rfl

  obtain ⟨u, hu⟩ := hB
  haveI hfin : Module.Finite K.O K'.O := by
    classical
    refine ⟨⟨Finset.univ.image u, eq_top_iff.2 fun y _ => ?_⟩⟩
    obtain ⟨a, ha⟩ := hu y
    have hy : y = ∑ i, a i • u i := by
      apply IsFractionRing.injective K'.O K'.E
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hmap, intMap_spec]
    rw [hy]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  haveI : FaithfulSMul K.O K'.O :=
    (faithfulSMul_iff_algebraMap_injective K.O K'.O).2 (intMap_injective hU)
  haveI : Module.Free K.O K'.O := Module.free_of_finite_type_torsion_free'

  haveI : IsLocalization (Algebra.algebraMapSubmonoid K'.O K.O⁰) K'.E := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
    have hϖ0 : algebraMap K.O K.E ϖ ≠ 0 := by simpa using hϖ.ne_zero
    have hφϖ : φ (algebraMap K.O K.E ϖ) ≠ 0 := by simpa using hϖ0
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨r, hr, rfl⟩ := hy
      refine IsUnit.mk0 _ ?_
      change algebraMap K'.O K'.E (intMap hU r) ≠ 0
      rw [intMap_spec]
      simpa using nonZeroDivisors.ne_zero hr
    · intro z
      by_cases hz : z = 0
      · exact ⟨⟨0, 1⟩, by simp [hz]⟩
      obtain ⟨s, hs⟩ := mem_range_of_val_nonneg K'
        (z * φ (algebraMap K.O K.E ϖ) ^ (-(val K'.O z)).toNat) (by
          rw [val_mul_ne K' hz (pow_ne_zero _ hφϖ), val_pow_ne K' hφϖ, hU.2.2.1, val_irreducible K hϖ]
          omega)
      refine ⟨⟨s, ⟨algebraMap K.O K'.O (ϖ ^ (-(val K'.O z)).toNat),
        Algebra.mem_algebraMapSubmonoid_of_mem
          ⟨_, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero) _⟩⟩⟩, ?_⟩
      change z * algebraMap K'.O K'.E (intMap hU (ϖ ^ (-(val K'.O z)).toNat)) = algebraMap K'.O K'.E s
      rw [hs, intMap_spec, map_pow, map_pow]
    · intro x y h
      exact ⟨1, by rw [IsFractionRing.injective K'.O K'.E h]⟩

  have hpS : Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O) =
      IsLocalRing.maximalIdeal K'.O := map_maximalIdeal hU
  haveI hmax : (Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)).IsMaximal := by
    rw [hpS]; infer_instance
  letI : Field (K.O ⧸ IsLocalRing.maximalIdeal K.O) := Ideal.Quotient.field _
  letI : Field (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Ideal.Quotient.field _
  haveI : Finite (K'.O ⧸ IsLocalRing.maximalIdeal K'.O) := K'.fin
  haveI : Finite (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) :=
    Finite.of_equiv _ (Ideal.quotEquivOfEq hpS).symm.toEquiv
  haveI : Finite (K.O ⧸ IsLocalRing.maximalIdeal K.O) := K.fin
  haveI : FiniteDimensional (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  haveI : Algebra.IsSeparable (K.O ⧸ IsLocalRing.maximalIdeal K.O)
      (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (K.O ⧸ IsLocalRing.maximalIdeal K.O)
    (K'.O ⧸ Ideal.map (algebraMap K.O K'.O) (IsLocalRing.maximalIdeal K.O)) 1
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  have htr := Algebra.trace_quotient_mk (R := K.O) (S := K'.O) y
  rw [hz] at htr
  refine ⟨y, Algebra.trace K.O K'.O y, ?_, ?_⟩
  · by_contra h
    have h0 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal K.O) (Algebra.trace K.O K'.O y) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [h0] at htr
    exact one_ne_zero htr
  · exact Algebra.trace_localization K.O K.O⁰ (Rₘ := K.E) (Sₘ := K'.E) y

theorem exists_trace_unit (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E) (hU : IsUnrExt K K' d φ) :
    ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧
      @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  exists_trace_unit_of_span K K' d φ hU (exists_int_basis_of_unr K K' d φ hU)

end GlobalTheory.UnitLemma.Unr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtensionStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧ @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_trace_unit | exact GlobalTheory.UnitLemma.Unr.exists_trace_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_trace_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescent
noncomputable section

namespace GlobalTheory.UnitLemma.LieEnd

open GlobalTheory.UnitLemma Polynomial Filter Topology

theorem eta_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy), neg_add,
    zpow_add₀ (by norm_num)]

theorem eta_sq (K : UQ) (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]
  norm_num

theorem q_ne_zero (K : UQ) : K.q ≠ 0 := by
  intro hq
  have hc := K.card_res
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
  rw [hq] at hc
  simp at hc
  omega

theorem exists_small (K : UQ) : ∃ a : K.O, K.Small a := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨y, hy⟩ := K.c_int p
  have hinj := IsFractionRing.injective K.O K.E
  have hy' : K.c (algebraMap K.O K.E y) = algebraMap K.O K.E p := by rw [← hy, K.c_c]
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : algebraMap K.O K.E p = 0 := by simpa using hy
    exact hp.ne_zero ((map_eq_zero_iff _ hinj).1 h0)
  refine ⟨p * y, mul_ne_zero hp.ne_zero hy0, Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp.not_isUnit), ?_⟩
  rw [map_mul, map_mul, hy, hy', mul_comm]

variable {K : UQ}

theorem mulLeft_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    LinearMap.mulLeft K.E x = (LinearMap.mulLeft K.E x.1).prodMap (LinearMap.mulLeft K.E x.2) := LinearMap.ext fun y => Prod.ext (by simp) (by simp)

theorem prod_P (B₁ B₂ : InvAlg K) : (B₁.prod B₂).P = B₁.P * B₂.P := by
  show (LinearMap.mulLeft K.E ((B₁.g, B₂.g) : B₁.A × B₂.A)).charpoly = _
  rw [mulLeft_prod]
  exact LinearMap.charpoly_prodMap _ _

theorem trace_prod (B₁ B₂ : InvAlg K) (x : B₁.A × B₂.A) :
    Algebra.trace K.E (B₁.A × B₂.A) x = Algebra.trace K.E B₁.A x.1 + Algebra.trace K.E B₂.A x.2 := Algebra.trace_prod_apply x

theorem linLim (h1 : CountIdentity) (h2 : UnitaryLimit) (B : InvAlg K) (hB : B.LieReg) (a : K.O)
    (ha : K.Small a) (x : B.A) (hx : B.Plus x) : B.LinLim a x (B.N x : ℝ) := by
  have hw : ∀ k : ℕ, IsUnit (algebraMap K.O B.A a ^ k) := by
    intro k
    apply IsUnit.pow
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha.1)).map _
  have hσ : B.σ (algebraMap K.O B.A a) = algebraMap K.O B.A a := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ha.2.2]
  refine (h2 K B hB a ha x hx).congr fun k => ?_
  have e : x * algebraMap K.O B.A a ^ (2 * k) =
      x * (algebraMap K.O B.A a ^ k * B.σ (algebraMap K.O B.A a ^ k)) := by
    rw [map_pow, hσ, ← pow_add, two_mul]
  rw [e, h1 K B hB x _ hx (hw k), Rat.cast_natCast]

theorem nonempty_of_N_ne_zero (B : InvAlg K) (x : B.A) (h : B.N x ≠ 0) : (B.X x).Nonempty := by
  by_contra he
  apply h
  have : IsEmpty (B.X x) := Set.isEmpty_coe_sort.2 (Set.not_nonempty_iff_eq_empty.1 he)
  have : IsEmpty (Orb K.O B.T (B.X x)) := ⟨fun o => isEmptyElim (Quot.out o)⟩
  exact finsum_of_isEmpty _

theorem X_empty (B : InvAlg K) (y : B.A) (hy : y ≠ 0) (h : ∀ z, Algebra.trace K.E B.A (y * z) = 0) (x : B.A) :
    ¬ (B.X x).Nonempty := by
  rintro ⟨L, hL⟩
  obtain ⟨⟨hfg, -⟩, -, hdual⟩ := hL
  have hmem : ∀ s : B.A, y * s ∈ L := fun s => (hdual _).2 fun z _ => by
    have h0 : B.herm x (y * s) z = 0 := by
      unfold InvAlg.herm
      rw [show x * (y * s) * B.σ z = y * (x * s * B.σ z) by ring]
      exact h _
    rw [h0]
    exact zero_mem _
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K.E hy
  have htop : (⊤ : Submodule K.O K.E) ≤ L.map ((φ : B.A →ₗ[K.E] K.E).restrictScalars K.O) := by
    intro e _
    refine Submodule.mem_map.2 ⟨y * algebraMap K.E B.A e, hmem _, ?_⟩
    rw [LinearMap.restrictScalars_apply, mul_comm, ← Algebra.smul_def, map_smul, hφ, smul_eq_mul, mul_one]
  have : Module.Finite K.O K.E := ⟨by rw [← top_le_iff.1 htop]; exact hfg.map _⟩
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  have hp0 : algebraMap K.O K.E p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 hp.ne_zero
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (Algebra.IsIntegral.isIntegral (R := K.O) (algebraMap K.O K.E p)⁻¹)
  apply hp.not_isUnit
  have hpr : p * r = 1 :=
    IsFractionRing.injective K.O K.E (by rw [map_mul, hr, map_one, mul_inv_cancel₀ hp0])
  exact ⟨⟨p, r, hpr, by rw [mul_comm, hpr]⟩, rfl⟩

theorem exists_rad (B : InvAlg K) (h : B.gramDet 1 = 0) :
    ∃ y : B.A, y ≠ 0 ∧ ∀ z, Algebra.trace K.E B.A (y * z) = 0 := by
  classical
  set b := Module.finBasis K.E B.A
  have h' : (Matrix.of fun i j => B.herm 1 (b i) (b j)).det = 0 := h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h'
  have hj : ∀ j, Algebra.trace K.E B.A ((∑ i, v i • b i) * B.σ (b j)) = 0 := by
    intro j
    have hvj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, InvAlg.herm, one_mul, Pi.zero_apply] at hvj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simpa [smul_mul_assoc] using hvj
  refine ⟨∑ i, v i • b i, fun h0 => hv0 (funext fun i => Fintype.linearIndependent_iff.1 b.linearIndependent v h0 i), ?_⟩
  intro z
  have hz : z = ∑ j, K.c (b.repr (B.σ z) j) • B.σ (b j) := by
    conv_lhs => rw [← B.σ_σ z, ← b.sum_repr (B.σ z)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, B.σ_alg]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [mul_smul_comm, map_smul, hj, smul_zero]

theorem rep_plus (B : InvAlg K) (k : B.Cl) : B.Plus k.rep := ⟨Units.isUnit _, (Quot.out k).2⟩

theorem eta_norm (B : InvAlg K) (h : B.gramDet 1 ≠ 0) (x : B.A) (hx : IsUnit x) :
    K.eta (Algebra.norm K.E x) = K.eta (B.gramDet 1) * K.eta (B.gramDet x) := by
  have hn : Algebra.norm K.E x ≠ 0 := (hx.map (Algebra.norm K.E)).ne_zero
  rw [GlobalTheory.T.gramDet_eq_norm_mul_gramDet_one K B x, eta_mul K hn h, mul_left_comm, eta_sq, mul_one]

theorem cast_finsum {ι : Type} (f : ι → ℚ) : ((∑ᶠ i, f i : ℚ) : ℝ) = ∑ᶠ i, (f i : ℝ) := (Rat.castHom ℝ).toAddMonoidHom.map_finsum_of_injective Rat.cast_injective f

theorem unitLemmaLie_of (h1 : CountIdentity) (h2 : UnitaryLimit) (h3 : LinearDescent) : UnitLemmaLie := by
  intro K B₁ B₂ hg₁ hg₂ hsep
  show (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * InvAlg.kapSum B₁ B₂ = B₁.stSum * B₂.stSum
  obtain ⟨a, ha⟩ := exists_small K
  have hB : (B₁.prod B₂).LieReg := ⟨Prod.ext hg₁ hg₂, by rw [prod_P]; exact hsep⟩
  have hB₁ : B₁.LieReg := ⟨hg₁, hsep.of_mul_left⟩
  have hB₂ : B₂.LieReg := ⟨hg₂, hsep.of_mul_right⟩
  have hLD := h3 K B₁ B₂ hg₁ hg₂ hsep a ha (fun x => ((B₁.prod B₂).N x : ℝ)) (fun x => (B₁.N x : ℝ))
    (fun x => (B₂.N x : ℝ)) (fun x hx => linLim h1 h2 _ hB a ha x hx)
    (fun x hx => linLim h1 h2 _ hB₁ a ha x hx) (fun x hx => linLim h1 h2 _ hB₂ a ha x hx)
  simp only [← Rat.cast_mul] at hLD
  rw [← cast_finsum, ← cast_finsum, ← cast_finsum] at hLD
  have hq : (-(K.q : ℝ)) ^ val K.O (resultant B₁.P B₂.P) =
      (((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) : ℚ) : ℝ) := by
    rw [Rat.cast_zpow, Rat.cast_neg, Rat.cast_natCast]
  rw [hq, ← Rat.cast_mul, ← Rat.cast_mul] at hLD
  have hQ := Rat.cast_injective hLD
  have hq0 : (-(K.q : ℚ)) ≠ 0 := by simpa using q_ne_zero K
  by_cases hd : B₁.gramDet 1 = 0
  · obtain ⟨y, hy0, hy⟩ := exists_rad B₁ hd
    have hN₁ : ∀ x, B₁.N x = 0 := fun x =>
      by_contra fun hx => X_empty B₁ y hy0 hy x (nonempty_of_N_ne_zero B₁ x hx)
    have hN : ∀ x, (B₁.prod B₂).N x = 0 := by
      intro x
      by_contra hx
      refine X_empty (B₁.prod B₂) ((y, 0) : B₁.A × B₂.A) (fun h0 => hy0 (congrArg Prod.fst h0))
        (fun z => ?_) x (nonempty_of_N_ne_zero _ x hx)
      have key : ∀ w : B₁.A × B₂.A, Algebra.trace K.E (B₁.A × B₂.A) ((y, 0) * w) = 0 := fun w => by
        rw [trace_prod]
        simp [hy]
      exact key z
    simp [InvAlg.kapSum, InvAlg.stSum, hN, hN₁]
  · have he : K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1) = 1 := eta_sq K _
    have hS : ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (Algebra.norm K.E (InvAlg.Cl.rep k).1) * (B₁.prod B₂).N k.rep =
        K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂ := by
      unfold InvAlg.kapSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (Prod.isUnit_iff.1 (rep_plus _ k).1).1, mul_assoc]
    have hS₁ : ∑ᶠ k : B₁.Cl, K.eta (Algebra.norm K.E k.rep) * B₁.N k.rep =
        K.eta (B₁.gramDet 1) * B₁.stSum := by
      unfold InvAlg.stSum
      rw [mul_finsum]
      refine finsum_congr fun k => ?_
      rw [eta_norm B₁ hd _ (rep_plus _ k).1]
      by_cases hk : B₁.N k.rep = 0
      · rw [hk, mul_zero, mul_zero]
      · rw [GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice K B₁ k.rep (rep_plus _ k).2 (nonempty_of_N_ne_zero B₁ _ hk), mul_one]
    have hst : ∑ᶠ k : B₂.Cl, B₂.N k.rep = B₂.stSum := rfl
    rw [hS, hS₁, hst] at hQ
    have hk : InvAlg.kapSum B₁ B₂ =
        (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) := by
      calc InvAlg.kapSum B₁ B₂
          = K.eta (B₁.gramDet 1) * (K.eta (B₁.gramDet 1) * InvAlg.kapSum B₁ B₂) := by
            rw [← mul_assoc, he, one_mul]
        _ = K.eta (B₁.gramDet 1) * ((-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) *
            (K.eta (B₁.gramDet 1) * B₁.stSum * B₂.stSum)) := by rw [hQ]
        _ = (-(K.q : ℚ)) ^ val K.O (resultant B₁.P B₂.P) * (B₁.stSum * B₂.stSum) *
            (K.eta (B₁.gramDet 1) * K.eta (B₁.gramDet 1)) := by ring
        _ = _ := by rw [he, mul_one]
    rw [hk, ← mul_assoc, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, one_mul]

end GlobalTheory.UnitLemma.LieEnd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaSelfAdjointLieOfCountLimitDescentStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemmaSelfAdjointLie_of_count_limit_descent : CountIdentity → UnitaryLimit → LinearDescent → UnitLemmaLie := by
  first | exact @GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | exact GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of | (intros; apply GlobalTheory.UnitLemma.LieEnd.unitLemmaLie_of <;> assumption)
end
end
