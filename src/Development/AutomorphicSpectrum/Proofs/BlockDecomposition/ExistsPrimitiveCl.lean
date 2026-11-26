module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSaturated
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import GroundTheory.AutomorphicForms.GL2.GodementSection
public import GroundTheory.GlobalFields.TateThesis.TateMain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlaces

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.RootsC

variable {l : ℕ} [hl : Fact l.Prime]

theorem seq_add_pow (m d : ℕ) : rootSeq l (m + d) ^ l ^ d = rootSeq l m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← Nat.add_assoc, pow_succ', pow_mul, GroundTheory.PAdicHodge.rootSeq_succ_pow, ih]

theorem seq_primitive (n : ℕ) : IsPrimitiveRoot (rootSeq l n) (l ^ n) := by
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    simpa using (GroundTheory.PAdicHodge.rootSeq_pow (p := l) 0)
  | succ k =>
    have h1 : ¬ rootSeq l (k + 1) ^ l ^ k = 1 := by
      rw [Nat.add_comm, seq_add_pow]
      exact GroundTheory.PAdicHodge.rootSeq_one_ne_one
    have h2 := orderOf_eq_prime_pow h1 (GroundTheory.PAdicHodge.rootSeq_pow (p := l) (k + 1))
    rw [← h2]
    exact IsPrimitiveRoot.orderOf _

theorem exists_primitive_cl (n : ℕ) : ∃ η : PadicAlgCl l, IsPrimitiveRoot η (l ^ n) := by
  have hq : (l ^ n : ℕ) ≠ 0 := pow_ne_zero n hl.out.ne_zero
  haveI : NeZero ((l ^ n : ℕ) : PadicAlgCl l) := ⟨by exact_mod_cast hq⟩
  have hdeg : (Polynomial.cyclotomic (l ^ n) (PadicAlgCl l)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    have ht : 0 < Nat.totient (l ^ n) := Nat.totient_pos.2 (Nat.pos_of_ne_zero hq)
    exact_mod_cast ht.ne'
  obtain ⟨η, hη⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨η, Polynomial.isRoot_cyclotomic_iff.1 hη⟩

theorem exists_lift (n : ℕ) :
    ∃ ρ : PadicAlgCl l, IsPrimitiveRoot ρ (l ^ n) ∧ clToC l ρ = rootSeq l n := by
  obtain ⟨η, hη⟩ := exists_primitive_cl (l := l) n
  have hinj : Function.Injective (clToC l) := (clToC l).injective
  have hη' : IsPrimitiveRoot (clToC l η) (l ^ n) :=
    (IsPrimitiveRoot.map_iff_of_injective hinj).2 hη
  obtain ⟨i, -, hi⟩ := hη'.eq_pow_of_pow_eq_one (GroundTheory.PAdicHodge.rootSeq_pow (p := l) n)
  refine ⟨η ^ i, ?_, by rw [map_pow, hi]⟩
  rw [← IsPrimitiveRoot.map_iff_of_injective hinj, map_pow, hi]
  exact seq_primitive n

theorem prim_of_primitive {q : ℕ} (hq : q ≠ 0) {F : Type} [Field F] [CharZero F] {ρ : F}
    (h : IsPrimitiveRoot ρ q) :
    IsUnit ((q : ℕ) : F) ∧ Polynomial.aeval ρ (Polynomial.cyclotomic q ℤ) = 0 := by
  refine ⟨isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hq), ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact h.isRoot_cyclotomic (Nat.pos_of_ne_zero hq)

theorem rootsEx : CrystallineSemistableComparison.E.RootsEx := by
  intro l _
  choose ρ hρ using fun n => exists_lift (l := l) n
  exact ⟨⟨fun n => Subtype.mk (ρ n)
      (prim_of_primitive (pow_ne_zero n (Fact.out : l.Prime).ne_zero) (hρ n).1),
    fun n => (hρ n).2⟩⟩

end GlobalTheory.CompanionTheory.RootsC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXi
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXi
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

namespace GradedFiltration

theorem Fil0_succ_le {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.Fil0 (r + 1) ≤ A.Fil0 r :=
  Ideal.span_mono fun _ ⟨k, hk, e⟩ => ⟨k, by omega, e⟩

theorem dividedXi_mem_filtration {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ) : A.dxi0 r ∈ A.Fil0 r :=
  Ideal.subset_span ⟨r, le_rfl, rfl⟩

theorem mem_filtration_of_prime_pow_mul {l : ℕ} [Fact l.Prime] (A : PAlg l) (r n : ℕ) (z : A.Acr0)
    (h : (l : A.Acr0) ^ n * z ∈ A.Fil0 r) : z ∈ A.Fil0 r := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply GlobalTheory.T.crystalline_filtration_saturated A r
    rwa [pow_succ', mul_assoc, mul_comm, mul_assoc, mul_comm z, ← mul_assoc, mul_comm _ (l : A.Acr0), mul_assoc] at h

theorem mkAcr_surjective {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ) :
    Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

end GradedFiltration


open GradedFiltration in
theorem graded_mod_pow : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ),
    (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧
    ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  intro l _ A n r
  have hF : ∀ s, A.Fil n s = (A.Fil0 s).map (A.mkAcr n) := (GlobalTheory.T.crystalline_filtration_multiplicative A).2.2.2.2.1 n
  have hsurj := mkAcr_surjective A n
  have hto : ∀ w, A.toAcr n w = A.mkAcr n (algebraMap A.W A.Acr0 w) := fun _ => rfl
  have hdx : A.dxi n r = A.mkAcr n (A.dxi0 r) := rfl
  refine ⟨fun z hz => ?_, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    obtain ⟨w, hw⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z0 hz0
    refine ⟨w, ?_⟩
    set_option synthInstance.maxHeartbeats 200000 in
      rw [hF, hto, hdx, ← map_mul (A.mkAcr n), ← map_sub (A.mkAcr n)]
    exact Ideal.mem_map_of_mem _ hw
  · rw [hF, Ideal.mem_map_iff_of_surjective _ hsurj, hto, hdx, ← map_mul] at h
    obtain ⟨z', hz', e⟩ := h
    have hd : algebraMap A.W A.Acr0 w * A.dxi0 r - z' ∈ Ideal.span {(l : A.Acr0) ^ n} := by
      apply Ideal.Quotient.eq.1
      exact e.symm
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 hd
    have hzr : z ∈ A.Fil0 r := by
      apply mem_filtration_of_prime_pow_mul A r n
      rw [← hz]
      exact sub_mem (Ideal.mul_mem_left _ _ (dividedXi_mem_filtration A r)) (Fil0_succ_le A r hz')
    obtain ⟨w', hw'⟩ := (GlobalTheory.T.crystalline_graded_pieces_description A r).1 z hzr
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      rw [← (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1]
      have : algebraMap A.W A.Acr0 (w - (l : A.W) ^ n * w') * A.dxi0 r =
          z' + (l : A.Acr0) ^ n * (z - algebraMap A.W A.Acr0 w' * A.dxi0 r) := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hz
      rw [this]
      exact add_mem hz' (Ideal.mul_mem_left _ _ hw')
    have : A.th w = (l : A.U) ^ n * A.th w' := by
      have h0 : A.th (w - (l : A.W) ^ n * w') = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxi
      rw [map_sub, map_mul, map_pow, map_natCast, sub_eq_zero] at h0
      exact h0
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h
    obtain ⟨w', rfl⟩ : ∃ w', A.th w' = u := Ideal.Quotient.mk_surjective u
    have hxi : w - (l : A.W) ^ n * w' ∈ Ideal.span {A.xi} := by
      apply Ideal.Quotient.eq_zero_iff_mem.1
      change A.th (w - (l : A.W) ^ n * w') = 0
      rw [map_sub, map_mul, map_pow, map_natCast, hu, sub_self]
    have h1 := (GlobalTheory.T.crystalline_graded_pieces_description A r).2.1 _ |>.2 hxi
    have h2 : A.toAcr n (w - (l : A.W) ^ n * w') * A.dxi n r ∈ A.Fil n (r + 1) := by
      rw [hF, hto, hdx, ← map_mul]
      exact Ideal.mem_map_of_mem _ h1
    have h3 : A.toAcr n (w - (l : A.W) ^ n * w') = A.toAcr n w := by
      rw [map_sub, map_mul, map_pow, map_natCast, pow_l_acr, zero_mul, sub_zero]
    rwa [h3] at h2

end GlobalTheory.CompanionTheory.PerfFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFiltrationGeneratedByDividedXiStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_filtration_generated_by_dividedXi : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ), (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧ ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow | exact GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow | (intros; apply GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.HT CrystallineSemistableComparison.Pb GlobalTheory.LogCris

namespace GlobalTheory.CompanionTheory.HodgePull

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem thick_ext {T T' : Thick (smFun X q)} (hB : T.B = T'.B) (hr : HEq T.ring T'.ring) (hi : HEq T.i T'.i)
    (hJ : HEq T.J T'.J) (hδ : HEq T.δ T'.δ) (hy : HEq T.y T'.y) : T = T' := by
  have hs : T.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T
  have hs' : T'.s = 1 := s_eq_one (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T'
  cases T with
  | @mk B ring i J δ adm compat α y inα w x v s hx hs0 hv =>
  cases T' with
  | @mk B' ring' i' J' δ' adm' compat' α' y' inα' w' x' v' s' hx' hs0' hv' =>
  dsimp only at hB hr hi hJ hδ hy hs hs'
  subst hB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hi
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hy
  obtain rfl : x = x' := funext fun j => Empty.elim j
  obtain rfl : v = v' := funext fun j => Empty.elim j
  obtain rfl : s = s' := hs.trans hs'.symm
  rfl

theorem hom_heq {T₁ T₂ T₁' T₂' : Thick (smFun X q)} (h : T₁ = T₂) (h' : T₁' = T₂') (f : T₁ ⟶ T₁') (g : T₂ ⟶ T₂')
    (hφ : HEq f.φ g.φ) : HEq f g := by
  subst h h'
  exact heq_of_eq (Thick.Hom.ext (eq_of_heq hφ) (funext fun j => Empty.elim j))

theorem obj_id (T : Thick (smFun X q)) : (smMor (𝟙 X) (Category.id_comp q)).obj T = T :=
  thick_ext rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl (heq_of_eq (Subtype.ext (Prod.ext rfl (Category.comp_id _))))

theorem functor_id : (smMor (𝟙 X) (Category.id_comp q)).functor = 𝟭 _ :=
  Functor.hext obj_id fun T T' f => hom_heq (obj_id T) (obj_id T') _ _ HEq.rfl

abbrev idMor (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ) : CH.Mor (grT (smFun X q) a) (grT (smFun X q) a) (RingHom.id K) :=
  (smS (𝟙 X) (Category.id_comp q)).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ))
    (b' := thFil _ ((a : ℤ) + 1)) (fun _ _ hx => hx) fun _ _ hx => hx

theorem τ_id (a : ℕ) (T : Thick (smFun X q)) (y : (grT (smFun X q) a).obj T) :
    (idMor q a).τ T y = y := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem pullC_id (a n : ℕ) (z : CH.Cn (grT (smFun X q) a) n) : (idMor q a).pullC n z = z := by
  funext s
  have h : s ⋙ (idMor q a).G = s := by
    change s ⋙ (smMor (𝟙 X) (Category.id_comp q)).functor = s
    rw [functor_id]
    exact Functor.comp_id s
  exact (τ_id a _ _).trans (eq_of_heq (congr_arg_heq z h))

theorem pullH_id : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (a n : ℕ) (x : Hdg q a n),
    pullH (𝟙 X) (Category.id_comp q) a n x = x := by
  intro K _ X q a n x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (pullC_id a n z))

end GlobalTheory.CompanionTheory.HodgePull

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLeNormInfCModuleSectionMul
set_option maxSynthPendingDepth 1

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
  GroundTheory.Automorphic.GodementSection IdeleGroup

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.EisRk1

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def infC (a : 𝔸[K]) : mixedSpace K := GroundTheory.Global.homeomorphMixedSpace K a.1

theorem infC_mul (a b : 𝔸[K]) : infC (a * b) = infC a * infC b :=
  homeomorphMixedSpace_mul _ _

theorem infC_add (a b : 𝔸[K]) : infC (a + b) = infC a + infC b := by
  simp only [infC, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace K) a.1 b.1

theorem infC_algebraMap (x : K) : infC (algebraMap K 𝔸[K] x) = mixedEmbedding K x := by
  simp only [infC, adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]

theorem continuous_infC : Continuous (infC (K := K)) :=
  (homeomorphMixedSpace K).continuous.comp continuous_fst

theorem exists_ideal_of_isCompact {S : Set 𝔸ᶠ[K]} (hS : IsCompact S) :
    ∃ (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (κ₀ : ℝ), 0 < κ₀ ∧
      (∀ ξ : K, algebraMap K 𝔸ᶠ[K] ξ ∈ S → ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K)) ∧
      ∀ ξ ∈ (J : FractionalIdeal (𝓞 K)⁰ K), ξ ≠ 0 →
        κ₀ ≤ mixedEmbedding.norm (mixedEmbedding K ξ) := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hNd : ((Algebra.norm ℚ dK : ℚ) : ℝ) ≠ 0 := by
    rw [Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).2 hdK
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)),
    |((Algebra.norm ℚ dK : ℚ) : ℝ)|⁻¹, inv_pos.2 (abs_pos.2 hNd), ?_, ?_⟩
  · intro ξ hmem
    have h1 := hd _ hmem
    rw [← map_mul] at h1
    have h2 : dK * ξ ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
      exact h1
    rw [Units.val_one] at h2
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
    refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
    rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]
  · intro ξ hξ hξ0
    obtain ⟨r', hr'⟩ := (FractionalIdeal.mem_spanSingleton _).1 hξ
    have hr'0 : r' ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hr'
      exact hξ0 hr'.symm
    have hmul : Algebra.norm ℚ dK * Algebra.norm ℚ ξ = Algebra.norm ℚ (r' : K) := by
      rw [← map_mul, ← hr', Algebra.smul_def, mul_left_comm, mul_inv_cancel₀ hdK, mul_one]
    have hξN : ((Algebra.norm ℚ ξ : ℚ) : ℝ) =
        ((Algebra.norm ℚ (r' : K) : ℚ) : ℝ) * ((Algebra.norm ℚ dK : ℚ) : ℝ)⁻¹ := by
      rw [← hmul, Rat.cast_mul]
      field_simp
    rw [mixedEmbedding.norm_eq_norm, Rat.cast_abs, hξN, abs_mul, abs_inv]
    exact le_mul_of_one_le_left (by positivity) (one_le_abs_norm_of_ne_zero hr'0)

theorem norm_le_norm_infC_moduleSection_mul (w : InfinitePlace K) {t : {x : ℝ // 0 < x}}
    (ht : 1 ≤ (t : ℝ)) (x : mixedSpace K) :
    ‖x‖ ≤ ‖infC ((moduleSection w t : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K]) * x‖ := by
  set e := infC ((moduleSection w t : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K])
  set e' := infC ((moduleSection w t⁻¹ : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K])
  have hee : e' * e = 1 := by
    rw [← infC_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    simp only [infC, homeomorphMixedSpace_apply]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace K)
  have he' : ∀ v, normAtPlace v e' ≤ 1 := by
    intro v
    simp only [e', infC]
    rw [normAtPlace_homeomorphMixedSpace]
    refine norm_moduleSection_apply_le_one w ?_ v
    change (t : ℝ)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ ht
  calc ‖x‖ = ‖e' * (e * x)‖ := by rw [← mul_assoc, hee, one_mul]
    _ ≤ ‖e * x‖ := norm_mul_le_of_normAtPlace_le_one he' _

theorem norm_infC_moduleSection (w : InfinitePlace K) (t : {x : ℝ // 0 < x}) :
    mixedEmbedding.norm (infC ((moduleSection w t : NumberField.IdeleGroup (𝓞 K) K) : 𝔸[K])) = t := by
  have h := mixedEmbedding_norm_toInfinite (moduleSection w t)
  rw [infiniteModule_moduleSection] at h
  exact h

end

end GlobalTheory.CompanionTheory.EisRk1
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructures
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructures
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem exists_natCast_mul_eq_l_pow {n k : ℕ} (hn : n ≠ 0) (hk : n.factorization l ≤ k) :
    ∃ w : A.Acr0, (n : A.Acr0) * w = (l : A.Acr0) ^ k := by
  obtain ⟨w, hw⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) hn hk
  refine ⟨algebraMap A.W A.Acr0 (A.sW w), ?_⟩
  have h := congrArg (fun t => algebraMap A.W A.Acr0 (A.sW t)) hw
  simpa using h

theorem exists_divided_power_of_dividedXi {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) :
    ∃ y ∈ A.Fil0 1, (k.factorial : A.Acr0) * y = A.dxi0 j ^ k := by
  obtain ⟨-, -, hf, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  refine ⟨(Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j),
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k * j, Nat.mul_pos (Nat.pos_of_ne_zero hk)
      (Nat.pos_of_ne_zero hj), rfl⟩), ?_⟩
  have hnz := A.acris_torsion_free (j.factorial ^ k) (pow_ne_zero k j.factorial_ne_zero)
  refine (mul_cancel_left_mem_nonZeroDivisors hnz).1 ?_
  have h1 : ((j.factorial ^ k : ℕ) : A.Acr0) *
      ((k.factorial : A.Acr0) * ((Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j))) =
      ((k * j).factorial : A.Acr0) * A.dxi0 (k * j) := by
    rw [← Nat.uniformBell_mul_eq k hj]
    push_cast
    ring
  rw [h1, hf, pow_mul', ← hf j]
  push_cast
  ring

theorem exists_l_pow {k : ℕ} (hk : k ≠ 0) :
    ∃ y ∈ Ideal.span {(l : A.Acr0)}, (k.factorial : A.Acr0) * y = (l : A.Acr0) ^ k := by
  have hv : k.factorial.factorization l ≤ k - 1 := by
    rw [Nat.factorization_def _ Fact.out]
    have h := sub_one_mul_multiplicity_factorial_lt_of_ne_zero (p := l) hk
    have h2 : 1 ≤ l - 1 := Nat.le_sub_of_add_le (Fact.out : l.Prime).two_le
    have h3 : multiplicity l k.factorial ≤ (l - 1) * multiplicity l k.factorial :=
      Nat.le_mul_of_pos_left _ h2
    omega
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero hv
  refine ⟨(l : A.Acr0) * w, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [mul_left_comm, hw]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  ring

theorem filtration_one_eq_span_dividedXi : A.Fil0 1 = Ideal.span {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k} := rfl

theorem pFil0_eq : A.PFil0 = Ideal.span ({(l : A.Acr0)} ∪ {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k}) := by
  rw [Ideal.span_union]
  rfl

theorem filtration_one_has_divided_powers : R.PdI (A.Fil0 1) := by
  rw [filtration_one_eq_span_dividedXi]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rintro _ ⟨j, hj, rfl⟩ k hk
  exact exists_divided_power_of_dividedXi A (by omega) hk

theorem pdI_pFil0 : R.PdI A.PFil0 := by
  rw [pFil0_eq]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rw [← pFil0_eq]
  rintro x (rfl | ⟨j, hj, rfl⟩) k hk
  · obtain ⟨y, hy, e⟩ := exists_l_pow A hk
    exact ⟨y, (le_sup_left : _ ≤ A.PFil0) hy, e⟩
  · obtain ⟨y, hy, e⟩ := exists_divided_power_of_dividedXi A (by omega : j ≠ 0) hk
    exact ⟨y, (le_sup_right : _ ≤ A.PFil0) hy, e⟩

theorem pow_mem_filtration_of_mem_one {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) : x ^ k ∈ A.Fil0 k := by
  obtain ⟨h0, -, -, hm, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  induction k with
  | zero => rw [h0]; exact Submodule.mem_top
  | succ k ih => rw [pow_succ]; exact hm k 1 (Ideal.mul_mem_mul ih hx)

theorem mem_filtration_of_prime_pow_mul_mem (r N : ℕ) (z : A.Acr0) (h : (l : A.Acr0) ^ N * z ∈ A.Fil0 r) :
    z ∈ A.Fil0 r := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (GlobalTheory.T.crystalline_filtration_saturated A r _ ?_)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem mem_filtration_of_factorial_mul_eq_pow {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) (y : A.Acr0)
    (e : (k.factorial : A.Acr0) * y = x ^ k) : y ∈ A.Fil0 k := by
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero le_rfl
  refine mem_filtration_of_prime_pow_mul_mem A k (k.factorial.factorization l) y ?_
  rw [← hw, mul_right_comm, e, mul_comm]
  exact Ideal.mul_mem_left _ _ (pow_mem_filtration_of_mem_one A hx k)

theorem pdI_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧
    ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k :=
  fun A => ⟨filtration_one_has_divided_powers A, pdI_pFil0 A, fun _ hx k y e => mem_filtration_of_factorial_mul_eq_pow A hx k y e⟩

end GlobalTheory.CompanionTheory.PerfFil
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructuresStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_divided_power_structures : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧ ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.pdI_main | exact GlobalTheory.CompanionTheory.PerfFil.pdI_main | (intros; apply GlobalTheory.CompanionTheory.PerfFil.pdI_main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRk1Bound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem vecMul_vecMul_inv (x : Fin 2 → 𝔸[K]) (h : GL (Fin 2) 𝔸[K]) :
    (x ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) ᵥ*
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = x := by
  rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]

theorem continuous_infRingHom : Continuous (infRingHom (K := K)) := by
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp continuous_fst

theorem continuous_finRingHom : Continuous (finRingHom (K := K)) := by
  exact continuous_snd

theorem continuous_inv_entry (i j : Fin 2) :
    Continuous fun h : GL (Fin 2) 𝔸[K] ↦
      ((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j := by
  exact Units.continuous_coe_inv.matrix_elem i j

private theorem mul_mem_idealFiniteAdeles_of_mem_integral {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x a : 𝔸ᶠ[K]}
    (hx : x ∈ idealFiniteAdeles I) (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a * x ∈ idealFiniteAdeles I := by
  change ∀ v, Valued.v ((a * x) v) ≤ _
  intro v
  have h1 : Valued.v (x v) ≤ WithZero.exp (-FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)) :=
    hx v
  have h2 : Valued.v (a v) ≤ 1 := (mem_adicCompletionIntegers _ _ _).mp (ha v)
  have h3 : (a * x) v = a v * x v := rfl
  rw [h3, Valuation.map_mul]
  calc Valued.v (a v) * Valued.v (x v) ≤ 1 * Valued.v (x v) := mul_le_mul' h2 le_rfl
    _ ≤ _ := by rw [one_mul]; exact h1

private theorem mem_idealFiniteAdeles_one_of_mem_integral {a : 𝔸ᶠ[K]} (ha : a ∈ integralFiniteAdeles (𝓞 K) K) :
    a ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := by
  change ∀ v, Valued.v (a v) ≤ _
  intro v
  rw [Units.val_one, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]
  exact (mem_adicCompletionIntegers _ _ _).mp (ha v)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : Fin 2 → 𝔸ᶠ[K])
    {C : Set (GL (Fin 2) 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      (∀ i, finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set S : Set 𝔸ᶠ[K] := ((⋃ i : Fin 2, ⋃ j : Fin 2,
      (fun h : GL (Fin 2) 𝔸[K] =>
        finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) i j)) '' C) ∪
      Set.range b) ∪ {1} with hS
  have hSc : IsCompact S :=
    ((isCompact_iUnion fun i => isCompact_iUnion fun j =>
      hC.image (continuous_finRingHom.comp (continuous_inv_entry i j))).union
      (isCompact_range continuous_of_discreteTopology)).union isCompact_singleton
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hSc
  have hL0 : ((I : FractionalIdeal (𝓞 K)⁰ K) ⊔ 1) ≠ 0 := by
    intro h0
    have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≤ 0 := h0 ▸ le_sup_right
    exact one_ne_zero (le_antisymm h1 (FractionalIdeal.zero_le _))
  set L : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 _ hL0 with hLdef
  have hIL : (idealFiniteAdeles I : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0]; exact le_sup_left)
  have h1L : (idealFiniteAdeles (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set 𝔸ᶠ[K]) ⊆ idealFiniteAdeles L :=
    idealFiniteAdeles_subset (by rw [hLdef, Units.val_mk0, Units.val_one]; exact le_sup_right)
  set e : K := algebraMap (𝓞 K) K d with he_def
  have he : e ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  have hE0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (e⁻¹ * e⁻¹) * (L : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    mul_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr
      (mul_ne_zero (inv_ne_zero he) (inv_ne_zero he))) (Units.ne_zero L)
  refine ⟨Units.mk0 _ hE0, fun h hh ξ hξ i => ?_⟩
  set y := finPart ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K])) with hy
  have hrec : (fun i => algebraMap K 𝔸ᶠ[K] (ξ i)) =
      y ᵥ* ((((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])).map finRingHom) := by
    rw [hy, ← finPart_vecMul, vecMul_vecMul_inv, finPart_algebraMap]
  have hξi : algebraMap K 𝔸ᶠ[K] (ξ i) = ∑ j, y j *
      finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) := by
    rw [congrFun hrec i]
    rfl
  set E : 𝔸ᶠ[K] := algebraMap K 𝔸ᶠ[K] e with hEdef
  have hE1 : E ∈ integralFiniteAdeles (𝓞 K) K := by
    have := hd 1 (Or.inr rfl)
    rwa [mul_one] at this
  have hEs : ∀ j, E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i) ∈
      integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨i, ⟨h, hh, rfl⟩⟩⟩)))
  have hEb : ∀ j, E * b j ∈ integralFiniteAdeles (𝓞 K) K := fun j =>
    hd _ (Or.inl (Or.inr ⟨j, rfl⟩))
  have hmemL : algebraMap K 𝔸ᶠ[K] (e * e * ξ i) ∈ idealFiniteAdeles L := by
    rw [map_mul, map_mul, hξi, Finset.mul_sum]
    refine sum_mem fun j _ => ?_
    have hsplit : E * E * (y j * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) :
        Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) =
        (E * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i))) *
          (y j - b j) +
        (E * b j) * (E * finRingHom (((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K]) j i)) := by
      ring
    rw [hsplit]
    refine add_mem (hIL (mul_mem_idealFiniteAdeles_of_mem_integral (hξ j) (mul_mem hE1 (hEs j)))) ?_
    exact h1L (mem_idealFiniteAdeles_one_of_mem_integral (mul_mem (hEb j) (hEs j)))
  have hmem : e * e * ξ i ∈ (L : FractionalIdeal (𝓞 K)⁰ K) :=
    (algebraMap_mem_idealFiniteAdeles_iff L _).mp hmemL
  rw [Units.val_mk0]
  have hξeq : ξ i = (e⁻¹ * e⁻¹) * (e * e * ξ i) := by field_simp
  rw [hξeq]
  exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hmem

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) : ℝ :=
  if x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + ‖mixedEmbedding K x‖) ^ k)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) :
    0 ≤ latticeWeight J k x := by
  unfold latticeWeight
  split_ifs <;> positivity

end

end GlobalTheory.CompanionTheory.EisRk1Bound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsSide
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRankOne

theorem weakFEPair_Λ₀_of_smul (P Q : WeakFEPair ℂ) (c : ℂ) (hf : Q.f = c • P.f)
    (hg : Q.g = c • P.g) (hk : Q.k = P.k) (hε : Q.ε = P.ε) (hf₀ : Q.f₀ = c • P.f₀)
    (hg₀ : Q.g₀ = c • P.g₀) : Q.Λ₀ = c • P.Λ₀ := by
  have hmod : Q.f_modif = c • P.f_modif := by
    funext x
    simp only [WeakFEPair.f_modif, Pi.add_apply, Pi.smul_apply, Set.indicator_apply, hf, hf₀, hg₀, hk, hε,
      smul_eq_mul]
    split_ifs <;> ring
  funext s
  simp only [WeakFEPair.Λ₀, hmod, Pi.smul_apply]
  exact mellin_const_smul P.f_modif s c

end GlobalTheory.CompanionTheory.EisRankOne
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassUniqueOfLiftAndLog
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtChern

theorem restrict_id_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (x : H (𝟭 C ⋙ F) 2) (x' : H F 2)
    (h : x = (Mor.restrict F (𝟭 C)).pull 2 x') : x = x' := by
  subst h
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  rfl

theorem chern_class_unique_of_lift_and_log : CrystallineSemistableComparison.E.LiftEx → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.FirstChernUniqueEtale := by
  intro hL hG l _ H O _ X q κ D hE y y' hy hy'
  obtain ⟨Λ⟩ := (hL l H O X q κ (El (PX q κ)) (𝟭 _) D).2 hE
  funext n
  obtain ⟨z, hz, hc, e⟩ := hy (El (PX q κ)) (𝟭 _) Λ n
  obtain ⟨z', hz', hc', e'⟩ := hy' (El (PX q κ)) (𝟭 _) Λ n
  have hzz : z = z' := by
    funext s
    exact (hG l _ n).2.1 _ _ _ (hc s) (hc' s)
  subst hzz
  have e1 := restrict_id_pull _ _ _ e
  have e2 := restrict_id_pull _ _ _ e'
  exact e1.symm.trans e2

end GlobalTheory.CompanionTheory.EtChern
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBC
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineBase

theorem u_eq {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (ha : a = a') (hb : b = b') (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    D.u a b h = D.u a' b' h' := by
  subst ha hb
  rfl

noncomputable def pull {X' X : Scheme.{0}} (g : X' ⟶ X) (D : LineData X) : LineData X' where
  Y := pullback D.f g
  f := pullback.snd D.f g
  sm := by
    exact MorphismProperty.pullback_snd (P := @Smooth) D.f g D.sm
  surj := by
    exact MorphismProperty.pullback_snd (P := @Surjective) D.f g D.surj
  u := fun {V} a b h => D.u (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g) (by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, h])
  nat := fun {V' V} k a b h => by
    rw [← D.nat k (a ≫ pullback.fst D.f g) (b ≫ pullback.fst D.f g)]
    exact u_eq D (Category.assoc _ _ _) (Category.assoc _ _ _) _ _
  coc := fun {V} a b c h h' => D.coc _ _ _ _ _

theorem lineBC : CrystallineSemistableComparison.E.LineBC := by
  intro X' X g D
  refine ⟨pull g D, pullback.fst D.f g, pullback.condition, ?_, ?_⟩
  · intro V a x h
    exact ⟨pullback.lift a x h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  · intro V a b h h'
    rfl

end GlobalTheory.CompanionTheory.LineBase
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftEx
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LineLift

theorem liftEx : CrystallineSemistableComparison.E.LiftEx := by
  intro l _ H O _ X q κ C _ G D
  have key : ∀ p : ∀ T : C, Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y,
      (∀ T, p T ≫ D.f = (G.obj T).2.1) → ∃ Λ : Lift G D, Λ.p = p := by
    intro p hp
    have hh : ∀ {T T' : C} (φ : T ⟶ T'),
        (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) ≫ D.f = p T' ≫ D.f := by
      intro T T' φ
      rw [Category.assoc, hp, hp]
      exact congrArg Subtype.val (G.map φ).2
    have ex : ∀ {T T' : C} (φ : T ⟶ T'), ∃ w : ((G.obj T').1.obj.A)ˣ,
        (G.obj T').1.obj.sharp w = (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)) := by
      intro T T' φ
      exact H.sharp _ (G.obj T').1.property (Units.map
        (Scheme.ΓSpecIso (CommRingCat.of (G.obj T').1.obj.U)).hom.hom.toMonoidHom
        (D.u (Spec.map (CommRingCat.ofHom (PAlg.mapU (G.map φ).1.hom)) ≫ p T) (p T') (hh φ)))
    exact ⟨{ p := p, hp := hp, w := fun φ => (ex φ).choose, hw := fun φ _ => (ex φ).choose_spec }, rfl⟩
  refine ⟨key, fun hE => ?_⟩
  have sec : ∀ T : C, ∃ p : Spec (CommRingCat.of (G.obj T).1.obj.U) ⟶ D.Y, p ≫ D.f = (G.obj T).2.1 := by
    intro T
    haveI := D.surj
    obtain ⟨s, hs⟩ := H.splitU _ (G.obj T).1.property (pullback D.f (G.obj T).2.1)
      (pullback.snd D.f (G.obj T).2.1) inferInstance inferInstance
    refine ⟨s ≫ pullback.fst D.f (G.obj T).2.1, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  choose p hp using sec
  obtain ⟨Λ, -⟩ := key p hp
  exact ⟨Λ⟩

end GlobalTheory.CompanionTheory.LineLift
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcMorCup
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtCupF

variable {l : ℕ} [Fact l.Prime]

noncomputable def lcRing (hS : LcSpec) (H : RIn l) (A : PAlg l) (hA : A.IsTest) (n : ℕ) :
    LocallyConstant (SU A) (ZMod (l ^ n)) →+* A.Acr n where
  toFun := lcA A n
  map_one' := (hS l H A hA n).2.1
  map_mul' := (hS l H A hA n).2.2.1
  map_zero' := map_zero _
  map_add' := map_add _

theorem lcMor_cup (hM : MorCup) (hS : LcSpec) (hN : LcNat) (H : RIn l) (r : Roots l) {C : Type 1} [Category.{0} C]
    (T : C ⥤ Test l) (n p q m : ℕ) (h : p + q = m) (x : CH.H (probe H r T n).L p) (y : CH.H (probe H r T n).L q) :
    (lcMor hN H r T n).pull m ((mulP (lcF (probe H r T n).S (l ^ n))).cup h x y) =
      (mulP ((T ⋙ testι l) ⋙ AcrA l n)).cup h ((lcMor hN H r T n).pull p x) ((lcMor hN H r T n).pull q y) :=
  (hM ℤ (Acris l) (Int.castRingHom (Acris l)) C (lcF (probe H r T n).S (l ^ n)) ((T ⋙ testι l) ⋙ AcrA l n)
    (lcMor hN H r T n) (fun c => lcRing hS H (T.obj c).obj (T.obj c).property n) (fun c x => rfl)).2 p q m h x y

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem eG_cup (hE : EtCup) (hM : MorCup) (hS : LcSpec) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l)
    (M : Model l K) {C : Type 1} [Category.{0} C] (G : C ⥤ El M.P) (n : ℕ) (i i' i'' : ℤ) (hi : i + i' = i'')
    (j j' j'' : ℕ) (hj : j + j' = j'') (x : Ht (l ^ n) (sch.obj (gb M)) j i) (y : Ht (l ^ n) (sch.obj (gb M)) j' i') :
    eG hN H r M G n i'' j'' ((cup (l ^ n) x y).cast (by omega) hi) =
      (mulP ((((G ⋙ CategoryOfElements.π _) ⋙ testι l)) ⋙ AcrA l n)).cup hj (eG hN H r M G n i j x) (eG hN H r M G n i' j' y) := by
  have h1 := hE E.gen E.tw (l ^ n) C (probe H r (G ⋙ CategoryOfElements.π _) n) (gb M)
    (pts H r M G n) i i' i'' hi j j' j'' hj x y
  have h2 := lcMor_cup hM hS hN H r (G ⋙ CategoryOfElements.π _) n j j' j'' hj
    ((pts H r M G n).et i j x) ((pts H r M G n).et i' j' y)
  exact (congrArg ((lcMor hN H r (G ⋙ CategoryOfElements.π _) n).pull j'') h1).trans h2

theorem fCup : CrystallineSemistableComparison.E.EtCup → CrystallineSemistableComparison.E.MorCup → CrystallineSemistableComparison.E.LcSpec → CrystallineSemistableComparison.E.FCup := by
  intro hE hM hS E hN l _ H r K M n i i' i'' hi j j' j'' hj x y
  exact eG_cup hE hM hS E hN H r M (𝟭 _) n i i' i'' hi j j' j'' hj x y

end GlobalTheory.CompanionTheory.EtCupF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VnRed
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.FUntwPf

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def vn (E : Spc) (k : ℕ) (a : Ht (l ^ k) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ k) E ((0 : ℕ) : ℤ) (-1)) : Ht (l ^ k) E ((2 : ℕ) : ℤ) 0 :=
  (cup (l ^ k) a b).cast rfl rfl

theorem vn_red (h : A11) (E : Spc) (k : ℕ) (a : Ht (l ^ (k + 1)) E ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ (k + 1)) E ((0 : ℕ) : ℤ) (-1)) :
    red (l ^ (k + 1)) (l ^ k) E ((2 : ℕ) : ℤ) 0 (vn E (k + 1) a b) =
      vn E k (red (l ^ (k + 1)) (l ^ k) E _ _ a) (red (l ^ (k + 1)) (l ^ k) E _ _ b) := by
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact (h (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l k.le_succ) E).1 a b

theorem step (hF : FCup) (hO : CupOne) (E : EtIn) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K) (n : ℕ)
    (a : Ht (l ^ n) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1) (b : Ht (l ^ n) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1))
    (hb : eM hN H r M n (-1) 0 b = oneH (AcrEl M.P n)) :
    eM hN H r M n 0 2 (vn (sch.obj (gb M)) n a b) = eM hN H r M n 1 2 a := by
  have h := hF E hN l H r K M n 1 (-1) 0 rfl 2 0 2 rfl a b
  have h2 := congrArg ((mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a)) hb
  have h' : (mulP (AcrEl M.P n)).cup (add_zero 2) (eM hN H r M n 1 2 a) (oneH (AcrEl M.P n)) = eM hN H r M n 1 2 a :=
    hO _ _ _ _ _
  exact h.trans (h2.trans h')

theorem core (E : EtIn) (hF : FCup) (hO : CupOne) (hN : LcNat) (H : RIn l) (r : Roots l) (M : Model l K)
    (x : Hl l (sch.obj (gb M)) (2 : ℕ) 1) (w : Hl l (sch.obj (gb M)) (0 : ℕ) (-1))
    (hw : ∀ n, eM hN H r M n (-1) 0 (w.1 n) = oneH (AcrEl M.P n)) :
    ∃ v : Hl l (sch.obj (gb M)) (2 : ℕ) 0, ∀ n, eM hN H r M n 0 2 (v.1 n) = eM hN H r M n 1 2 (x.1 n) := by
  have hv : ∀ k, red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 0
      (vn (sch.obj (gb M)) (k + 1) (x.1 (k + 1)) (w.1 (k + 1))) = vn (sch.obj (gb M)) k (x.1 k) (w.1 k) := by
    intro k
    have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((2 : ℕ) : ℤ) 1 (x.1 (k + 1)) = x.1 k := x.2 k
    have h2 : red (l ^ (k + 1)) (l ^ k) (sch.obj (gb M)) ((0 : ℕ) : ℤ) (-1) (w.1 (k + 1)) = w.1 k := w.2 k
    exact (vn_red E.a11 _ k _ _).trans (congrArg₂ (vn (sch.obj (gb M)) k) h1 h2)
  exact ⟨⟨fun k => vn (sch.obj (gb M)) k (x.1 k) (w.1 k), hv⟩, fun n => step hF hO E hN H r M n (x.1 n) (w.1 n) (hw n)⟩

theorem main : CrystallineSemistableComparison.E.FCup → CrystallineSemistableComparison.E.FRoot → CrystallineSemistableComparison.E.CupOne → CrystallineSemistableComparison.E.FUntw :=
  fun hF hR hO E hN l _ H r K M x => (hR E hN l H r K M (-1)).elim fun w hw => core E hF hO hN H r M x w hw

end GlobalTheory.CompanionTheory.FUntwPf
end
end
