module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdDiscrTorsionField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivativesSeparateLieBasisCoeffsCartesian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AbelianUnramIn
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize

namespace GlobalTheory.FieldSize.WeberUnram

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.WeberUnram.of_algHom {K M R : Type} [Field K] [NumberField K]
    [Field M] [Algebra K M] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (f : M →ₐ[K] R) :
    ∃ (_ : NumberField M) (_ : IsAbelianGalois K M),
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.NT.UnramIn R 𝔭 →
        _root_.GlobalTheory.NT.UnramIn M 𝔭 := by
  have hab : IsAbelianGalois K M := IsAbelianGalois.of_algHom f
  letI : Algebra M R := f.toRingHom.toAlgebra
  haveI : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : FiniteDimensional K M := FiniteDimensional.left K M R
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI nf : NumberField M := ⟨⟩
  exact ⟨nf, hab, fun 𝔭 h => _root_.GlobalTheory.RayMaximal.unramIn_of_tower (L := M) (M := R) h⟩

end GlobalTheory.FieldSize.WeberUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeDvdNatCastMem
namespace GlobalTheory.PrimeDvdNatCastMem

theorem exists_prime_dvd_natCast_mem {O : Type} [CommRing O] (P : Ideal O) [hP : Ideal.IsPrime P]
    (m : ℕ) : m ≠ (0 : ℕ) → (↑m : O) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m ∧ (↑p : O) ∈ P := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hm
    by_cases h1 : m = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hm)) hP.ne_top
    · obtain ⟨q, hq, k, hk⟩ := Nat.exists_prime_and_dvd h1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hm0 (by simpa using hk)
      have hmul : (q : O) * (k : O) ∈ P := by
        have := hm
        rw [hk, Nat.cast_mul] at this
        exact this
      rcases hP.mem_or_mem hmul with h | h
      · exact ⟨q, hq, ⟨k, hk⟩, h⟩
      · have hlt : k < m := by
          have h2 := hq.two_le
          have h3 : 0 < k := Nat.pos_of_ne_zero hk0
          rw [hk]
          nlinarith
        obtain ⟨p, hp, hpk, hpP⟩ := ih k hlt hk0 h
        exact ⟨p, hp, hk ▸ Dvd.dvd.mul_left hpk q, hpP⟩

end GlobalTheory.PrimeDvdNatCastMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminant
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.TorsionSize

theorem exists_prime_dvd_mem {O : Type} [CommRing O] (P : Ideal O) [hP : P.IsPrime] (m : ℕ) :
    m ≠ 0 → (m : O) ∈ P → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ (p : O) ∈ P := by
  first
  | exact @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem
  | exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem
  | (apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDvdNatCastMem.exists_prime_dvd_natCast_mem ..)

theorem unramIn_of_discr (H M : Type) [Field H] [NumberField H] [Field M] [NumberField M]
    [Algebra H M] [IsGalois H M] (n : ℕ)
    (h : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ n)
    (𝔭 : HeightOneSpectrum (𝓞 H)) (hn : (n : 𝓞 H) ∉ 𝔭.asIdeal) : UnramIn M 𝔭 := by
  rintro σ ⟨P, hP, hPo, hσ⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hnd : ¬ P ∣ differentIdeal (𝓞 H) (𝓞 M) := by
    intro hd
    have h1 : Ideal.absNorm P ∣ (discr M).natAbs := by
      rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow H (𝓞 H) M (𝓞 M)]
      exact (map_dvd Ideal.absNorm hd).mul_right _
    obtain ⟨p, hp, hpd, hpP⟩ := exists_prime_dvd_mem P (Ideal.absNorm P)
      (by rwa [Ne, Ideal.absNorm_eq_zero_iff]) (Ideal.absNorm_mem P)
    obtain ⟨k, hk⟩ := h p hp (hpd.trans h1)
    apply hn
    rw [hPo.over, Ideal.mem_comap, map_natCast, hk, Nat.cast_mul]
    exact P.mul_mem_right _ hpP
  have hI := (GlobalTheory.UnramDiscr.not_dvd_iff_inertia H M P hP0).1 hnd
  have : σ ∈ Ideal.inertia Gal(M/H) P := fun x => hσ x
  rw [hI] at this
  exact Subgroup.mem_bot.1 this

theorem log_rootDiscr_le (K H M : Type) [Field K] [NumberField K] [Field H] [NumberField H]
    [Field M] [NumberField M] [Algebra K H] [Algebra H M] [IsGalois K H] [IsGalois H M] (d : ℕ)
    (hd : 0 < d) (hK : Module.finrank ℚ K = 2) (hdK : (discr K).natAbs = d)
    (hu : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn H 𝔭)
    (h : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d ∨ p ∣ (discr H).natAbs) :
    Real.log |((discr M : ℤ) : ℝ)| / Module.finrank ℚ M ≤
      Real.log d / 2 + Real.log ((6 * d * Module.finrank H M : ℕ) : ℝ) := by
  have hH := (GlobalTheory.UnramDiscr.unramIn_iff_natAbs_discr K H).1 hu
  rw [hdK] at hH
  have h' : ∀ p : ℕ, p.Prime → p ∣ (discr M).natAbs → p ∣ 6 * d := by
    intro p hp hpd
    rcases h p hp hpd with h1 | h1
    · exact h1
    · rw [hH] at h1
      exact (hp.dvd_of_dvd_pow h1).mul_left 6
  have h1 := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal H M (6 * d) (by omega)
    (unramIn_of_discr H M (6 * d) h')
  have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal H M _
    (Nat.mul_pos (by omega) Module.finrank_pos) h1
  refine h2.trans (add_le_add_left (le_of_eq ?_) _)
  have h3 : |((discr H : ℤ) : ℝ)| = (d : ℝ) ^ Module.finrank K H := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, hH]; push_cast; rfl
  have h4 : (Module.finrank K H : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [h3, Real.log_pow, ← Module.finrank_mul_finrank ℚ K H, hK]
  push_cast
  field_simp

theorem exists_algHom_ray (hR : RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (hd : discr K < -4) (L : PeriodPair)
    (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) (H : IntermediateField ℚ ℂ)
    (hH : H = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯) [Algebra K H]
    (hKH : ∀ x : K, ((algebraMap K H x : H) : ℂ) = x) (n : ℕ) (ho : Odd n) (h3 : 3 ≤ n) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R),
      IsRay R (Ideal.span {(n : 𝓞 K)}) ∧ Nonempty (H →ₐ[K] R) := by
  have hn : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  obtain ⟨R, _, _, hRay⟩ := SmallField.exists_isRay_intermediateField hR K _ hn
  have hsub := InRay.weberSet_subset K hK hd L hL n ho h3 R hRay
  have hle : H ≤ R.restrictScalars ℚ := by
    rw [hH]
    refine sup_le (fun x hx => R.algebraMap_mem (⟨x, hx⟩ : K)) ?_
    rw [IntermediateField.adjoin_simple_le_iff, GlobalTheory.Published.latticeCurve_j_eq, mul_div_assoc]
    exact mul_mem (ofNat_mem _ 1728) (hsub (Set.mem_insert _ _))
  exact ⟨R, inferInstance, inferInstance, hRay,
    ⟨{ toRingHom := (IntermediateField.inclusion hle).toRingHom
       commutes' := fun x => Subtype.ext (hKH x) }⟩⟩

theorem invariantField (hR : RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2) (hd : discr K < -4) (L : PeriodPair)
    (hL : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) (H : IntermediateField ℚ ℂ)
    (hH : H = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯) [Algebra K H]
    (hKH : ∀ x : K, ((algebraMap K H x : H) : ℂ) = x) :
    ∃ (_ : NumberField H) (_ : IsGalois K H), (∀ 𝔭 : HeightOneSpectrum (𝓞 K), UnramIn H 𝔭) ∧
      Module.finrank K H ≤ 9 * (discr K).natAbs := by
  obtain ⟨R, _, _, hRay, ⟨f⟩⟩ := exists_algHom_ray hR K hK hd L hL H hH hKH 3 (by decide) le_rfl
  obtain ⟨S, _, _, hSay, ⟨g⟩⟩ :=
    exists_algHom_ray hR K hK hd L hL H hH hKH 5 (by decide) (by norm_num)
  obtain ⟨hN, hA, hf⟩ := WeberUnram.of_algHom f
  obtain ⟨-, -, hg⟩ := WeberUnram.of_algHom g
  refine ⟨hN, inferInstance, fun 𝔭 => ?_, ?_⟩
  · by_cases h : 𝔭.asIdeal ∣ Ideal.span {((3 : ℕ) : 𝓞 K)}
    · refine hg 𝔭 (hSay.1 𝔭 fun h' => 𝔭.isPrime.ne_top ?_)
      rw [Ideal.dvd_span_singleton] at h h'
      rw [Ideal.eq_top_iff_one]
      have := sub_mem (𝔭.asIdeal.mul_mem_left 2 h) h'
      convert this using 1
      norm_num
    · exact hf 𝔭 (hRay.1 𝔭 h)
  · have hn : Ideal.span {((3 : ℕ) : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have h1 := RayDegree.finrank_le K R _ hn hRay
    have he : IsEmpty (K →+* ℝ) := ⟨fun φ => by
      refine IsTotallyComplex.complexEmbedding_not_isReal (Complex.ofRealHom.comp φ) ?_
      rw [ComplexEmbedding.isReal_iff]
      ext x
      simp⟩
    rw [Fintype.card_eq_zero, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at h1
    have h2 : Module.finrank K H ≤ Module.finrank K R :=
      LinearMap.finrank_le_finrank_of_injective (f := f.toLinearMap) f.toRingHom.injective
    have h3 := GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K hK
    have h4 : classNumber K ≤ (discr K).natAbs := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs] at h3
      exact_mod_cast h3
    omega

theorem isGalois_torsion (F H M : IntermediateField ℚ ℂ) [NumberField F] [NumberField H]
    [NumberField M] (A : WeierstrassCurve F) (hFH : F ≤ H) (hHM : H ≤ M)
    (hM : M = H ⊔ IntermediateField.adjoin ℚ (torsionCoords (A.baseChange ℂ) 12)) :
    letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra
    IsGalois H M := by
  letI : Algebra H M := (IntermediateField.inclusion hHM).toAlgebra
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Algebra F M := (IntermediateField.inclusion (hFH.trans hHM)).toAlgebra
  haveI : IsScalarTower F H M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower H M ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower F H ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine TorsionRam.isGalois A (fun z hz => ⟨⟨z, ?_⟩, rfl⟩) fun T h1 h2 z => ?_
  · rw [hM]
    exact (le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hz)
  · let T' : IntermediateField ℚ ℂ := (T.map (algebraMap M ℂ)).toIntermediateField
      fun q => by simp
    have hT : M ≤ T' := by
      refine hM.le.trans (sup_le (fun x hx => ⟨_, h1 ⟨x, hx⟩, rfl⟩) ?_)
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      have hxM : x ∈ M := by
        rw [hM]
        exact (le_sup_right : _ ≤ H ⊔ _) (IntermediateField.subset_adjoin ℚ _ hx)
      exact ⟨⟨x, hxM⟩, h2 _ hx, rfl⟩
    obtain ⟨y, hy, hyz⟩ := hT z.2
    have : y = z := Subtype.ext hyz
    exact this ▸ hy

theorem card_GL_le : Nat.card (GL (Fin 2) (ZMod 12)) ≤ 20736 := by
  have h := Nat.card_le_card_of_injective
    (fun g : GL (Fin 2) (ZMod 12) => (g : Matrix (Fin 2) (Fin 2) (ZMod 12))) Units.val_injective
  refine h.trans (le_of_eq ?_)
  change Nat.card (Fin 2 → Fin 2 → ZMod 12) = _
  simp

theorem log_le_twenty {x : ℝ} (h0 : 0 < x) (hx : x ≤ 2 ^ 20) : Real.log x ≤ 20 := by
  have h1 : Real.log x ≤ Real.log (2 ^ 20) := Real.log_le_log h0 hx
  rw [Real.log_pow] at h1
  have := Real.log_two_lt_d9
  push_cast at h1
  linarith

theorem sz_discField : RayField → ∀ (P : Pre) (δ : FieldDat P),
    Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  intro hR P δ
  obtain ⟨K, _, _, hK, hdK, hd4, -, hO, -⟩ := exists_hostK P.R P.host
  obtain ⟨_, _, L, hL, hF, -, hg⟩ := δ.good
  unfold FieldDat.M'
  set d := P.host.d with hd
  set A := δ.curve
  have hd0 : 0 < d := by omega
  have hs : P.host.φ₀ P.host.sqrtMinusD ∈ K := by
    obtain ⟨a, ha⟩ := (hO _).1 ⟨(-1, 2), rfl⟩
    have : P.host.φ₀ P.host.sqrtMinusD = ((a : K) : ℂ) := by
      rw [ha]; push_cast; ring
    rw [this]; exact (a : K).2
  have hKe : ℚ⟮GlobalTheory.Published.sqrtNegNat d⟯ = K := by
    ext z
    rw [GlobalTheory.Published.mem_adjoin_sqrtNegNat_iff (K := K) hd0 hK (x := ⟨_, hs⟩)
      (Subtype.ext (by
        push_cast
        rw [← map_pow, P.host.sqrtMinusD_sq]; simp [hd]))]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨z, h⟩, rfl⟩⟩
  have hL' : ∀ z : ℂ, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := by
    intro z
    rw [hL z, hKe]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨⟨z, h1⟩, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom)
        Subtype.val_injective).1 h2⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : K).2, (isIntegral_algHom_iff (K.val.toRingHom.toIntAlgHom)
        Subtype.val_injective).2 a.2⟩
  have hH : hilbertField d δ.jField = K ⊔ ℚ⟮(GlobalTheory.latticeCurve L).j⟯ := by
    rw [hilbertField, hKe, ← hF]
  rw [DiscRoot.discField_eq_torsionField]
  have hKH : K ≤ hilbertField d δ.jField := hH ▸ le_sup_left
  letI : Algebra K (hilbertField d δ.jField) := (IntermediateField.inclusion hKH).toAlgebra
  obtain ⟨_, _, hu, hdeg⟩ := invariantField hR K hK hd4 L hL' _ hH fun _ => rfl
  obtain ⟨hfin, hM⟩ := TorsionDegree.finrank_torsionField_le d δ.jField A
  haveI : NumberField (torsionField d A) := ⟨⟩
  have hHM := hilbertField_le_torsionField d A
  letI : Algebra (hilbertField d δ.jField) (torsionField d A) :=
    (IntermediateField.inclusion hHM).toAlgebra
  haveI : IsGalois (hilbertField d δ.jField) (torsionField d A) :=
    isGalois_torsion δ.jField (hilbertField d δ.jField) (torsionField d A) A le_sup_right hHM rfl
  have hdn : (discr K).natAbs = d := by rw [hdK]; simp
  have hrd := log_rootDiscr_le K (hilbertField d δ.jField) (torsionField d A) d hd0 hK hdn hu
    (TorsionRam.dvd_discr_torsionField d δ.jField A hg)
  have hM' := hM.trans (Nat.mul_le_mul_left _ card_GL_le)
  have hrel : Module.finrank (hilbertField d δ.jField) (torsionField d A) ≤ 20736 := by
    rw [← (letI : Module.Free (hilbertField d δ.jField) (torsionField d A) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (hilbertField d δ.jField) (torsionField d A))] at hM'
    exact Nat.le_of_mul_le_mul_left hM' Module.finrank_pos
  rw [← Module.finrank_mul_finrank ℚ K (hilbertField d δ.jField), hK] at hM'
  rw [hdn] at hdeg
  have hdR : (0 : ℝ) < d := Nat.cast_pos.2 hd0
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have key : ∀ m : ℕ, 0 < m → m ≤ d * 2 ^ 20 → Real.log m ≤ Real.log d + 20 := by
    intro m h0 hm
    have h1 : Real.log m ≤ Real.log (d * 2 ^ 20) :=
      Real.log_le_log (Nat.cast_pos.2 h0) (by exact_mod_cast hm)
    rw [Real.log_mul hdR.ne' (by positivity)] at h1
    have := log_le_twenty (x := 2 ^ 20) (by positivity) le_rfl
    linarith
  have hM2 : Module.finrank ℚ (torsionField d A) ≤ d * 2 ^ 20 :=
    hM'.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hdeg)).trans
      (by clear * -; omega))
  refine ⟨hfin, key _ Module.finrank_pos hM2, hrd.trans ?_⟩
  have := key (6 * d * Module.finrank (hilbertField d δ.jField) (torsionField d A))
    (Nat.mul_pos (by omega) Module.finrank_pos)
    ((Nat.mul_le_mul_left _ hrel).trans (by clear * -; omega))
  linarith

end GlobalTheory.Mem.Fld.TorsionSize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldDatumSizeLogDiscriminantStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_datum_size_log_discriminant : RayField → ∀ (P : Pre) (δ : FieldDat P), Sz δ.M' (Real.log P.host.d + 20) (3 * Real.log P.host.d + 20) := by
  first | exact @GlobalTheory.Mem.Fld.TorsionSize.sz_discField | exact GlobalTheory.Mem.Fld.TorsionSize.sz_discField | (intros; apply GlobalTheory.Mem.Fld.TorsionSize.sz_discField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRoots
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.KummerSize

open GlobalTheory.FieldSize.Capit

variable {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ)

theorem step (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) (k : ℕ) (hk : 0 < k)
    (J : Ideal (𝓞 E)) (γ : 𝓞 E) (hγ : γ ≠ 0) (hJ : J ^ k = Ideal.span {γ}) (z : ℂ) (hz : z ^ k = φ (γ : E)) :
    Sz (F ⊔ ℚ⟮z⟯) (a + Real.log k) (b + Real.log k) := by
  have hyF : (intMap φ F h γ : F) ≠ 0 := by
    intro h0
    have h1 : φ (γ : E) = 0 := by rw [← coe_intMap φ F h, h0]; rfl
    exact hγ (RingOfIntegers.ext ((map_eq_zero φ).1 h1))
  exact GlobalTheory.FieldSize.sz_sup_adjoin_root F a b k (intMap φ F h γ : F)
    (IsLocalization.coeSubmodule F (J.map (intMap φ F h))) z hF hk hyF
    (by rw [← coeSubmodule_pow, ← Ideal.map_pow, hJ, Ideal.map_span, Set.image_singleton,
      IsLocalization.coeSubmodule_span_singleton]) hz

theorem sz_adjoin_roots (F : IntermediateField ℚ ℂ) (a b : ℝ) (hF : Sz F a b) (h : ∀ x, φ x ∈ F) {ι : Type}
    (k : ι → ℕ) (hk : ∀ i, 0 < k i) (J : ι → Ideal (𝓞 E)) (γ : ι → 𝓞 E) (hγ : ∀ i, γ i ≠ 0)
    (hJ : ∀ i, J i ^ k i = Ideal.span {γ i}) (z : ι → ℂ) (hz : ∀ i, z i ^ k i = φ (γ i : E)) (s : Finset ι) :
    Sz (F ⊔ IntermediateField.adjoin ℚ (z '' s)) (a + ∑ i ∈ s, Real.log (k i)) (b + ∑ i ∈ s, Real.log (k i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hF
  | insert i s hi ih =>
    have h' : ∀ x, φ x ∈ F ⊔ IntermediateField.adjoin ℚ (z '' s) := fun x => (le_sup_left : F ≤ F ⊔ _) (h x)
    have hS := step φ _ _ _ ih h' (k i) (hk i) (J i) (γ i) (hγ i) (hJ i) (z i) (hz i)
    have he : F ⊔ IntermediateField.adjoin ℚ (z '' ↑(insert i s)) =
        F ⊔ IntermediateField.adjoin ℚ (z '' s) ⊔ ℚ⟮z i⟯ := by
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, IntermediateField.adjoin_union, sup_comm
        (IntermediateField.adjoin ℚ {z i}), sup_assoc]
    rw [he, Finset.sum_insert hi]
    refine sz_mono' hS (by linarith) (by linarith)

end GlobalTheory.FieldSize.KummerSize

namespace GlobalTheory.FieldSize.KummerSize

variable {E : Type} [Field E] [NumberField E]

open GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis in
theorem exists_decomp (b : ClassBasis E) (J : Fin b.k → (Ideal (𝓞 E))⁰)
    (hJc : ∀ i, ClassGroup.mk0 (J i) = ClassGroup.mk E (b.c i)) (γ : Fin b.k → 𝓞 E) (hγ0 : ∀ i, γ i ≠ 0)
    (hγ : ∀ i, (J i : Ideal (𝓞 E)) ^ b.h i = Ideal.span {γ i}) {h : ℕ} (hh : 0 < h) {y : E}
    (hy : y ∈ powIdealElts E h) :
    ∃ (u : (𝓞 E)ˣ) (t : Eˣ) (a m : Fin b.k → ℤ), (∀ i, (h : ℤ) * a i = b.h i * m i) ∧
      y = (u : E) * (t : E) ^ h * ∏ i, (γ i : E) ^ m i := by
  obtain ⟨hy0, 𝔞, h𝔞⟩ := hy
  have h𝔞0 : 𝔞 ≠ 0 := by
    rintro rfl
    rw [zero_pow hh.ne'] at h𝔞
    exact hy0 (FractionalIdeal.spanSingleton_eq_zero_iff.1 h𝔞)
  set U := Units.mk0 𝔞 h𝔞0 with hU
  set Y := Units.mk0 y hy0 with hY
  have hUY : U ^ h = toPrincipalIdeal (𝓞 E) E Y := by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, hU, Units.val_mk0, hY, Units.val_mk0, h𝔞]
  have hγE : ∀ i, (γ i : E) ≠ 0 := fun i h0 => hγ0 i (RingOfIntegers.ext h0)
  let G : Fin b.k → Eˣ := fun i => Units.mk0 (γ i : E) (hγE i)
  let P : Fin b.k → (FractionalIdeal (𝓞 E)⁰ E)ˣ := fun i => FractionalIdeal.mk0 E (J i)
  have hP : ∀ i, ClassGroup.mk E (P i) = ClassGroup.mk E (b.c i) := fun i => by
    rw [ClassGroup.mk_mk0, hJc]
  have hPG : ∀ i, P i ^ b.h i = toPrincipalIdeal (𝓞 E) E (G i) := fun i => by
    refine Units.ext ?_
    rw [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val, FractionalIdeal.coe_mk0, ← FractionalIdeal.coeIdeal_pow,
      hγ i, FractionalIdeal.coeIdeal_span_singleton]
    rfl
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E U)
  have hx1 : ClassGroup.mk E U ^ h = 1 := by
    rw [← map_pow, hUY, ClassGroup.mk_eq_one_iff, coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨_, rfl⟩⟩
  have hm : ∀ i, ∃ m : ℤ, (h : ℤ) * a i = b.h i * m := by
    have h1 := b.indep (fun i => (h : ℤ) * a i) (by
      simp only [zpow_mul', zpow_natCast]
      rw [Finset.prod_pow, ← ha, hx1])
    intro i
    exact orderOf_dvd_iff_zpow_eq_one.2 (h1 i)
  choose m hm using hm
  have h2 : ClassGroup.mk E (U * (∏ i, P i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, hP, mul_inv_cancel]
  obtain ⟨t, ht⟩ := exists_gen h2
  have hU' : U = toPrincipalIdeal (𝓞 E) E t * ∏ i, P i ^ a i := by
    rw [← ht, inv_mul_cancel_right]
  have h3 : toPrincipalIdeal (𝓞 E) E (t ^ h * ∏ i, G i ^ m i) = toPrincipalIdeal (𝓞 E) E Y := by
    rw [← hUY, hU', mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, ← hPG, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← hm i, mul_comm]
  rw [toPrincipalIdeal_eq_iff, coe_toPrincipalIdeal, FractionalIdeal.spanSingleton_eq_spanSingleton] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨u, t, a, m, hm, ?_⟩
  show (Y : E) = _
  rw [← hu, Units.smul_def, Algebra.smul_def]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_prod, Units.val_zpow_eq_zpow_val, G, Units.val_mk0]
  ring

end GlobalTheory.FieldSize.KummerSize

namespace GlobalTheory.FieldSize

open GlobalTheory.FieldSize.KummerSize GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

theorem sz_kummerField : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), 0 < h →
    Sz (kummerField φ h) (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h +
      Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E +
      ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) := by
  intro E _ _ φ h hh
  classical

  let b : ClassBasis E := Classical.arbitrary _
  choose J hJ using fun i => ClassGroup.mk0_surjective (ClassGroup.mk E (b.c i))
  have hprin : ∀ i, ((J i : Ideal (𝓞 E)) ^ b.h i).IsPrincipal := fun i => by
    have hmem : (J i : Ideal (𝓞 E)) ^ b.h i ∈ (Ideal (𝓞 E))⁰ := pow_mem (J i).2 _
    rw [← ClassGroup.mk0_eq_one_iff hmem]
    have : (⟨_, hmem⟩ : (Ideal (𝓞 E))⁰) = J i ^ b.h i := rfl
    rw [this, map_pow, hJ]
    exact pow_orderOf_eq_one _
  choose γ hγ using fun i => (hprin i).principal
  have hγ' : ∀ i, (J i : Ideal (𝓞 E)) ^ b.h i = Ideal.span {γ i} := fun i => by
    rw [hγ i, Ideal.submodule_span_eq]
  have hγ0 : ∀ i, γ i ≠ 0 := fun i h0 => by
    have h1 := hγ' i
    rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at h1
    exact nonZeroDivisors.coe_ne_zero (J i ^ b.h i) h1

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := NumberField.Units.torsion E)
  let uγ : Option (Fin (NumberField.Units.rank E)) → (𝓞 E)ˣ :=
    fun o => o.elim (g : (𝓞 E)ˣ) (NumberField.Units.fundSystem E)
  have huJ : ∀ o, (⊤ : Ideal (𝓞 E)) ^ h = Ideal.span {((uγ o : (𝓞 E)ˣ) : 𝓞 E)} := fun o => by
    rw [Ideal.top_pow, eq_comm, Ideal.span_singleton_eq_top]
    exact (uγ o).isUnit
  have hu0 : ∀ o, ((uγ o : (𝓞 E)ˣ) : 𝓞 E) ≠ 0 := fun o => (uγ o).ne_zero

  choose ρ hρ using fun o => IsAlgClosed.exists_pow_nat_eq (φ (((uγ o : (𝓞 E)ˣ) : 𝓞 E) : E)) hh
  choose β hβ using fun i => IsAlgClosed.exists_pow_nat_eq (φ ((γ i : 𝓞 E) : E)) (b.h_pos i)

  have hF1 : Sz (imField φ ⊔ cycField h) (Real.log (Module.finrank ℚ E) + Real.log h)
      (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log h) :=
    sz_sup _ _ _ _ _ _ (sz_fieldRange_embedding E φ) (sz_adjoin_rootOfUnity h hh)
  have hφ1 : ∀ x, φ x ∈ imField φ ⊔ cycField h := fun x => (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hF2 := sz_adjoin_roots φ _ _ _ hF1 hφ1 (fun _ => h) (fun _ => hh) (fun _ => ⊤)
    (fun o => ((uγ o : (𝓞 E)ˣ) : 𝓞 E)) hu0 huJ ρ hρ Finset.univ
  set F2 := imField φ ⊔ cycField h ⊔ IntermediateField.adjoin ℚ (ρ '' ↑(Finset.univ : Finset (Option (Fin (NumberField.Units.rank E))))) with hF2def
  have hφ2 : ∀ x, φ x ∈ F2 := fun x => (le_sup_left : _ ≤ F2) (hφ1 x)
  have hF3 := sz_adjoin_roots φ _ _ _ hF2 hφ2 b.h b.h_pos (fun i => (J i : Ideal (𝓞 E))) γ hγ0 hγ' β hβ Finset.univ
  set F3 := F2 ⊔ IntermediateField.adjoin ℚ (β '' ↑(Finset.univ : Finset (Fin b.k))) with hF3def
  have hsum1 : ∑ _o ∈ (Finset.univ : Finset (Option (Fin (NumberField.Units.rank E)))), Real.log (h : ℕ) =
      (NumberField.Units.rank E + 1) * Real.log h := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_option]
  have hsum2 : ∑ i ∈ (Finset.univ : Finset (Fin b.k)), Real.log (b.h i) ≤ Real.log (classNumber E) := by
    have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
    rw [← Real.log_prod (fun i _ => by exact_mod_cast (b.h_pos i).ne')]
    refine Real.log_le_log (Finset.prod_pos fun i _ => by exact_mod_cast b.h_pos i) ?_
    exact_mod_cast h1
  have hF3' := (sz_mono_and_of_le.1 F3 _ _ _ _ hF3 (by rw [hsum1] at *; linarith) (by rw [hsum1] at *; linarith) :
    Sz F3 (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h +
      Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E +
      ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))))
  refine sz_mono_and_of_le.2 _ _ _ _ ?_ hF3'

  have h23 : F2 ≤ F3 := le_sup_left
  have h13 : imField φ ⊔ cycField h ≤ F3 := le_sup_left.trans h23
  have hρF : ∀ o, ρ o ∈ F3 := fun o => h23 ((le_sup_right : _ ≤ F2)
    (IntermediateField.subset_adjoin ℚ _ ⟨o, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩))
  have hβF : ∀ i, β i ∈ F3 := fun i => (le_sup_right : _ ≤ F3)
    (IntermediateField.subset_adjoin ℚ _ ⟨i, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
  refine (kummerField_le_iff φ).2 ⟨fun x => h13 (hφ1 x), h13 ((le_sup_right : cycField h ≤ _)
    (IntermediateField.mem_adjoin_simple_self ℚ _)), fun y hy z hz => ?_⟩
  have hy0 : y ≠ 0 := hy.1
  obtain ⟨u, t, a, m, hm, rfl⟩ := exists_decomp b J hJ γ hγ0 hγ' hh hy
  obtain ⟨⟨ζ, e⟩, hζe, -⟩ := NumberField.Units.exist_unique_eq_mul_prod E u
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.1 (hg ζ)
  let Φ : (𝓞 E)ˣ →* ℂˣ := Units.map ((φ.comp (algebraMap (𝓞 E) E)) : 𝓞 E →* ℂ)
  have hΦ : ∀ v : (𝓞 E)ˣ, ((Φ v : ℂˣ) : ℂ) = φ ((v : 𝓞 E) : E) := fun v => rfl
  set w : ℂ := ρ none ^ c * (∏ j, ρ (some j) ^ e j) * φ (t : E) * ∏ i, β i ^ a i with hw
  have hwF : w ∈ F3 := mul_mem (mul_mem (mul_mem (zpow_mem (hρF none) _)
    (prod_mem fun j _ => zpow_mem (hρF (some j)) _)) (h13 (hφ1 _))) (prod_mem fun i _ => zpow_mem (hβF i) _)
  have hA : ∀ o (k : ℤ), (ρ o ^ k) ^ h = ((Φ (uγ o) ^ k : ℂˣ) : ℂ) := fun o k => by
    rw [Units.val_zpow_eq_zpow_val, hΦ, ← hρ o, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hB : ∀ i, (β i ^ a i) ^ h = φ ((γ i : 𝓞 E) : E) ^ m i := fun i => by
    rw [← hβ i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm (a i), hm i]
  have hu : φ ((u : 𝓞 E) : E) = ((Φ (uγ none) ^ c : ℂˣ) : ℂ) * ∏ j, ((Φ (uγ (some j)) ^ e j : ℂˣ) : ℂ) := by
    rw [← hΦ, hζe, ← hc, map_mul, Units.val_mul, map_prod, Units.coe_prod]
    congr 1
    · rw [Subgroup.coe_zpow, map_zpow]; rfl
    · exact Finset.prod_congr rfl fun j _ => by rw [map_zpow]; rfl
  have hwh : w ^ h = φ ((u : E) * (t : E) ^ h * ∏ i, ((γ i : 𝓞 E) : E) ^ m i) := by
    rw [hw, mul_pow, mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, hA]
    simp only [hA, hB]
    rw [map_mul, map_mul, map_pow, map_prod, hu]
    simp only [map_zpow₀]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne', eq_comm, map_eq_zero] at hwh
    exact hy0 hwh
  have hzw : z / w ∈ cycField h := mem_cycField hh.ne' (by rw [div_pow, hz, ← hwh, div_self (pow_ne_zero _ hw0)])
  have := mul_mem (h13 ((le_sup_right : cycField h ≤ _) hzw)) hwF
  rwa [div_mul_cancel₀ _ hw0] at this

end GlobalTheory.FieldSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRootsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), 0 < h → Sz (kummerField φ h) (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) := by
  first | exact @GlobalTheory.FieldSize.sz_kummerField | exact GlobalTheory.FieldSize.sz_kummerField | (intros; apply GlobalTheory.FieldSize.sz_kummerField <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomial
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

theorem om_sizes_le_poR (f r L lE lh lN lhs lG lr ld rk ldeg : ℝ) (hf : 8 ≤ f) (hr : 62 ≤ r) (hL : 4 ≤ L)
    (hlf : Real.log f ≤ L) (hE0 : 0 ≤ lE) (hE : lE ≤ 2 * L)
    (hh : lh ≤ f * lE + 2 * f * Real.log (1 + f * lE)) (hN : lN ≤ 20 * L + 2) (hs0 : 0 ≤ lhs)
    (hs : lhs ≤ lh + 2 * f * lN) (hG : lG ≤ f * r ^ 2 * (18 * L + 2)) (hr' : lr ≤ lG + 24)
    (hd : ld ≤ 4 * L) (hk : rk ≤ 2 * f) (hdeg : ldeg ≤ 1 + L) :
    (ld + 20) + (ldeg + lhs) + lr + (ldeg + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L ∧
    (3 * ld + 20) + (lE + lN + lhs) + lr + (lE + ((rk + 2) * lhs + lh)) ≤ 19 * f * r ^ 2 * L + 198 * f ^ 2 * L := by
  have hf0 : 0 < f := by linarith
  have hL0 : 0 < L := by linarith
  have hfE0 : 0 ≤ f * lE := mul_nonneg hf0.le hE0
  have hfE : f * lE ≤ f * (2 * L) := mul_le_mul_of_nonneg_left hE hf0.le
  have hfL : 32 ≤ f * L := by nlinarith
  have h1 : Real.log (1 + f * lE) ≤ Real.log (f * (3 * L)) := Real.log_le_log (by linarith) (by nlinarith)
  have h2 : Real.log (f * (3 * L)) = Real.log f + Real.log (3 * L) := Real.log_mul hf0.ne' (by positivity)
  have h3 : Real.log (3 * L) ≤ 3 * L - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (1 + f * lE) ≤ 4 * L := by linarith
  have h5 : 2 * f * Real.log (1 + f * lE) ≤ 2 * f * (4 * L) := mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : lh ≤ 10 * (f * L) := by nlinarith
  have h7 : 2 * f * lN ≤ 2 * f * (20 * L + 2) := mul_le_mul_of_nonneg_left hN (by positivity)
  have h8 : 4 * f ≤ f * L := by nlinarith
  have h9 : lhs ≤ 51 * (f * L) := by nlinarith
  have h10 : (rk + 2) * lhs ≤ (2 * f + 2) * (51 * (f * L)) :=
    mul_le_mul_of_nonneg_right (by linarith) hs0 |>.trans (mul_le_mul_of_nonneg_left h9 (by linarith))
  have h11 : f * r ^ 2 * 2 ≤ f * r ^ 2 * L := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h12 : 8 * (f * L) ≤ f * (f * L) := mul_le_mul_of_nonneg_right hf (by positivity)
  have h13 : f * (f * L) = f ^ 2 * L := by ring
  constructor <;> nlinarith

theorem sz_Om_poR : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  intro hR P δ L hL
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  obtain ⟨K, _, _, hK2, hKd, -, hKE, -, hdeg⟩ := exists_hostK P.R P.host
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
  have hrd : lE ≤ 2 * L := hlE' ▸ hL.rd

  have hd : Real.log (P.host.d : ℝ) ≤ 4 * L := by
    obtain ⟨_, -, h⟩ := sz_mono_and_of_le.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2, hKd] at h'
    push_cast at h'
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg _)] at h'
    linarith

  have hM' := GlobalTheory.T.field_datum_size_log_discriminant hR P δ
  obtain ⟨hdeg_le, hray⟩ := GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound P.host.E P.host.φ₀ (modulus P) δ.ray δ.isRay (modulus_ne_zero P)
  have hcyc : Sz (cycField (rootOrder P)) (Real.log (rootOrder P)) (Real.log (rootOrder P)) :=
    sz_adjoin_rootOfUnity _ (Nat.pos_of_ne_zero (rootOrder_ne_zero P))
  have hV : Sz δ.V _ _ := GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots P.host.E P.host.φ₀ δ.hstar δ.hstar_pos
  have hall := sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ (sz_sup _ _ _ _ _ _ hM' hray) hcyc) hV
  change Sz (δ.M' ⊔ δ.ray ⊔ cycField (rootOrder P) ⊔ δ.V) _ _

  obtain ⟨hG, -, hf8, -⟩ := roots_sizes P L hL
  have hf0 : (0 : ℝ) < P.R.f := by have : 8 ≤ P.R.f := hf8; exact_mod_cast (by omega : 0 < P.R.f)
  have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
  rw [← hlE'] at hcl
  have hh0 : 0 < classNumber P.host.E := classNumber_pos _

  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := P.host.pde_prime.pos
  have hp' := P.host.pde'_prime.pos
  have hN : Real.log (modulus P : ℝ) ≤ 20 * L + 2 := by
    have e : Real.log (modulus P : ℝ) = Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log P.host.pde +
        Real.log P.host.pde' := by
      simp only [modulus]; push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
    have := hL.g 0
    have := hL.g 1
    have := hL.p
    rw [e]; linarith [this.1, this.2]

  have hs0 : 0 ≤ Real.log (δ.hstar : ℝ) := Real.log_natCast_nonneg _
  have hs : Real.log (δ.hstar : ℝ) ≤ Real.log (classNumber P.host.E) + 2 * P.R.f * Real.log (modulus P : ℝ) := by
    have h1 : (δ.hstar : ℝ) ≤ (classNumber P.host.E : ℝ) * (modulus P : ℝ) ^ Module.finrank ℚ P.host.E := by
      exact_mod_cast hdeg_le
    have h2 := Real.log_le_log (by exact_mod_cast δ.hstar_pos) h1
    rw [Real.log_mul (by positivity) (pow_ne_zero _ (by exact_mod_cast modulus_ne_zero P)), Real.log_pow, hdeg] at h2
    push_cast at h2
    linarith

  have hr : Real.log (rootOrder P : ℝ) ≤ Real.log P.restRowsFiniteGroupCard + 24 := by
    have hc := P.restRowsFiniteGroupCard_pos
    have h1 : (rootOrder P : ℝ) ≤ (P.restRowsFiniteGroupCard : ℝ) * ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by positivity) (Nat.lcm_dvd_mul _ _)
    have h2 := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero (rootOrder_ne_zero P)) h1
    rw [Real.log_mul (by positivity) (by positivity)] at h2
    have e : Real.log ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = 4 * Real.log 3 + 4 * Real.log 5 := by
      rw [show ((3 ^ 4 * 5 ^ 4 : ℕ) : ℝ) = (3 : ℝ) ^ 4 * (5 : ℝ) ^ 4 by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]; push_cast; ring
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    linarith

  have hk : (NumberField.Units.rank P.host.E : ℝ) ≤ 2 * P.R.f := by
    have : NumberField.Units.rank P.host.E ≤ Module.finrank ℚ P.host.E := by
      rw [NumberField.Units.rank, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
        NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]; omega
    rw [hdeg] at this
    exact_mod_cast this
  have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
    rw [hdeg]; push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have := hL.deg
    linarith
  have hnum := om_sizes_le_poR P.R.f P.R.r L lE (Real.log (classNumber P.host.E)) (Real.log (modulus P : ℝ))
    (Real.log (δ.hstar : ℝ)) (Real.log P.restRowsFiniteGroupCard) (Real.log (rootOrder P : ℝ)) (Real.log (P.host.d : ℝ))
    (NumberField.Units.rank P.host.E) (Real.log (Module.finrank ℚ P.host.E)) (by exact_mod_cast hf8)
    (by exact_mod_cast hL.rank) hL.len hL.deg hlE0 hrd hcl hN hs0 hs hG hr hd hk d1
  refine sz_mono_and_of_le.1 _ _ _ _ _ hall ?_ ?_
  · unfold poR; exact hnum.1
  · unfold poR; exact hnum.2

end GlobalTheory.FieldSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomialStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial : RayField → ∀ (P : Pre) (δ : FieldDat P) (L : ℝ), HostSz P.host L → Sz δ.Om (poR P.R L) (poR P.R L) := by
  first | exact @GlobalTheory.FieldSize.sz_Om_poR | exact GlobalTheory.FieldSize.sz_Om_poR | (intros; apply GlobalTheory.FieldSize.sz_Om_poR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContainsRayFieldSub
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberRay

theorem containsRayField_sub (P : Pre) (δ : FieldDat P) (K : IntermediateField ℚ ℂ) [NumberField K]
    (hKE : K ≤ P.host.φ₀.toRatAlgHom.fieldRange) (hKR : K ≤ δ.ray) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hKR).toRingHom (modulus P) := by
  obtain ⟨hm, hNF, hray⟩ := δ.isRay
  letI := algOf P.host.φ₀ δ.ray hm
  obtain ⟨hab, hun, -, hart⟩ := hray
  haveI : IsGalois P.host.E δ.ray := hab.toIsGalois
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.E δ.ray) (modulus P) :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (modulus P) hun (fun I hI hc => (hart I hI hc).1)
  let e : P.host.E ≃ₐ[ℚ] P.host.φ₀.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom
  let φKE : K →+* P.host.E :=
    ((e.symm : P.host.φ₀.toRatAlgHom.fieldRange ≃+* P.host.E) : P.host.φ₀.toRatAlgHom.fieldRange →+* P.host.E).comp
      (IntermediateField.inclusion hKE).toRingHom
  have hcomp : (algebraMap P.host.E δ.ray).comp φKE = (IntermediateField.inclusion hKR).toRingHom := by
    refine RingHom.ext fun x => Subtype.ext ?_
    have := congrArg Subtype.val (e.apply_symm_apply (IntermediateField.inclusion hKE x))
    exact this
  rw [← hcomp]
  exact GlobalTheory.RayDescent.containsRayField_comp K P.host.E δ.ray φKE _ _ hC

theorem weberSet_subset_ray : ∀ (P : Pre) (δ : FieldDat P) (L : PeriodPair), (∀ z, z ∈ L.lattice ↔ ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + P.host.φ₀ P.host.sqrtMinusD) / 2)) → ∀ n : ℕ, Odd n → 3 ≤ n → n ∣ modulus P → weberSet L n ⊆ δ.ray := by
  intro P δ L hL n _ hn hdvd
  obtain ⟨K, hKN, hKT, h2, -, hd, hKE, hlat, -⟩ := GlobalTheory.FieldSize.exists_hostK P.R P.host
  have hP : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
  have hKR : K ≤ δ.ray := fun z hz => by
    obtain ⟨x, rfl⟩ := hKE hz
    exact δ.isRay.emb_mem x
  have hCK := containsRayField_sub P δ K hKE hKR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd L hP n hn
  haveI := GlobalTheory.FieldSize.WeberIn.numberField_adjoin K δ.ray (weberSet L n)
  have hm0 : ((modulus P : ℕ) : 𝓞 δ.ray) ≠ 0 := by
    exact_mod_cast modulus_ne_zero P
  haveI : NumberField (⊥ : IntermediateField δ.ray ℂ) := NumberField.of_module_finite δ.ray _
  have hle : IntermediateField.adjoin δ.ray (weberSet L n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split δ.ray ℂ ⊥ (IntermediateField.adjoin δ.ray (weberSet L n)) ?_
    refine ((WeberIn.finite_mem hm0).union (WeberIn.finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hCK 𝔓 hc.1
    have h1' : (n : 𝓞 K) ∣ α - 1 := (Nat.cast_dvd_cast hdvd).trans h1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K δ.ray hKR (weberSet L n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1')
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin δ.ray _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberRay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AtMember

open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem odd_of_mem_levelPrimes (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) : Odd p := by
  have h := (P.level_cond p hp).2
  have h2 : (2 : ℕ) ∣ P.host.QS * P.host.q * P.host.d := ((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans P.host.tower_dvd).mul_right _).mul_right _)
  rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd p h2, h]

set_option maxHeartbeats 4000000 in
theorem fieldTies_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre),
    X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  intro hR X f δ hx
  have := GlobalTheory.Mem.FieldsEx.host_cplx X.B.toPre
  have hFO : FO X.toD7 = X.B.KsC := SetLike.ext fun z => (mem_FO_assembled_iff X z).trans (X.B.mem_KsC).symm
  have hxe : X.B.KsC = Fld.listField δ f := hx
  obtain ⟨hray, -, hchar, -⟩ := Base.KsExact.lower hx
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hpl : p ∈ X.B.host.levelPrimes := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_level.1, X.B.host.pde_level.2]
    have hpp : p.Prime := (X.B.toPre.level_cond p hpl).1
    have hdvd : X.B.host.g 0 * X.B.host.g 1 * p ∣ Fld.modulus X.B.toPre := by
      rcases hp with rfl | rfl
      · exact dvd_mul_right _ _
      · exact ⟨X.B.host.pde, by unfold Fld.modulus; ring⟩
    have hpd : p ∣ Fld.modulus X.B.toPre := (dvd_mul_left p _).trans hdvd
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rw [hFO]
      exact hray (GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn X.B.host.E X.B.host.φ₀ (Fld.modulus X.B.toPre) p δ.ray (Fld.modulus_ne_zero _) hpd δ.isRay)
    · have hn0 : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
        Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hpp.pos
      refine GlobalTheory.FieldSize.curveOver_of_weberSet X.toD7 _ hn0 ?_ fun L hL => ?_
      · rw [hFO]
        exact X.B.imField_le_KsC ⟨_, rfl⟩
      · have hodd : Odd (X.B.host.g 0 * X.B.host.g 1 * p) :=
          ((odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 0)).mul
            (odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 1))).mul (odd_of_mem_levelPrimes X.B.toPre hpl)
        have h3 : 3 ≤ X.B.host.g 0 * X.B.host.g 1 * p := by
          have a := (X.B.host.g_prime 0).two_le
          have b := (X.B.host.g_prime 1).two_le
          have c := hpp.two_le
          have := Nat.mul_le_mul (Nat.mul_le_mul a b) c
          omega
        rw [hFO]
        exact (GlobalTheory.FieldSize.WeberRay.weberSet_subset_ray X.B.toPre δ L hL _ hodd h3 hdvd).trans fun z hz => hray hz
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), fun x => ?_, fun x => ?_, fun L hL => ?_⟩
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del X.B.KsC f.isDel.fin
      ((le_sup_right.trans (le_sup_left.trans le_sup_left)).trans hchar) x
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del' X.B.KsC f.isDel'.fin ((le_sup_right.trans le_sup_left).trans hchar) x
  · have hle : FO X.toD7 ≤ δ.Om := by
      rw [hFO, hxe]
      exact GlobalTheory.Mem.FieldsEx.listField_le_Om δ f
    exact GlobalTheory.FieldSize.sz_mono_and_of_le.2 _ _ _ _ hle (GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial hR X.B.toPre δ L hL)

end GlobalTheory.AtMember

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallFieldStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fieldTies_of_rayField_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre), X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  first | exact @GlobalTheory.AtMember.fieldTies_of_ksExact | exact GlobalTheory.AtMember.fieldTies_of_ksExact | (intros; apply GlobalTheory.AtMember.fieldTies_of_ksExact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Plug

theorem tied_cfOf : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  intro hR 𝒮 hcs K p
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p.x.what₂.r.z.geo.fw.laws
  · exact hcs K p.B p.f p.T p.w p.Z p.x.Wt p.O.p0 p.x.what₂ p.x.rx
  · exact GlobalTheory.T.fieldTies_of_rayField_of_ksExact hR (p.w.st p.Z) p.f p.w.δ p.w.exact
  · show HalfAt (ofObj p.O).errX (Fr.at (p.w.st p.Z) p.f)
    rw [p.x.errX]
    exact GlobalTheory.T.conjGenerators_mem_framePrimes_trueColumns p.B p.f p.T p.w p.Z p.x.col.toColT

end GlobalTheory.Plug
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoreFrameCompatibleConstructedPointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreFrameCompatible_constructed_point : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots), CoreSlot 𝒮 → ∀ (K : Ctx) (p : WPt 𝒮 K), Tied p.O.ex.errX (cfOf p).J (cfOf p).C := by
  first | exact @GlobalTheory.Plug.tied_cfOf | exact GlobalTheory.Plug.tied_cfOf | (intros; apply GlobalTheory.Plug.tied_cfOf <;> assumption)
end
