module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVring

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zpow_w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1)
    (i j : Fin n) (hij : i ≠ j) : a ^ w n i ≠ a ^ w n j := by
  have h1 : a ≠ 1 := by
    rintro rfl
    simp at ha
  have h2 : a ≠ a⁻¹ := by
    intro h
    apply ha
    rw [sq]
    nth_rewrite 2 [h]
    simp
  rcases hn with rfl | rfl
  · fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals first | exact h1 | exact Ne.symm h1 | exact h2 | exact Ne.symm h2
  · fin_cases i <;> fin_cases j <;> simp [w] at hij ⊢
    all_goals first | exact h1 | exact Ne.symm h1 | exact h2 | exact Ne.symm h2

theorem UpperTheory.V.Fr.flag :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : S.A →+* C) (v : F.V), UpperTheory.V.W.HasFlag ((S.u.map f).r.comp (F.loc0 v)).toHomUnits ((S.u.map f).ψ v) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ f v
  obtain ⟨g, hg⟩ := hF.f3 v
  obtain ⟨hB, hm⟩ := co_B hF hn S
  refine flag_loc _ _ g (fun i j hij => ?_) ?_ (fun s => (S.u.map f).ord v s)
  · have hu : IsUnit (S.ψB v i g - S.ψB v j g) := by
      by_contra hu
      have h1 : S.ψB v i g - S.ψB v j g ∈ S.mB := by
        rw [← hm]
        exact hu
      have h2 : (S.ρ.ψ v i g : S.R) - S.ρ.ψ v j g ∈ maximalIdeal S.R := h1
      have h3 := (res_eq_zero_iff O S.R _).2 h2
      have h4 : ∀ i, res O S.R (S.ρ.ψ v i g) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
        fun i => S.lift.2.1.2 v i g
      rw [map_sub, h4, h4, sub_eq_zero] at h3
      exact zpow_w_ne hn _ hg i j hij (Units.ext h3)
    have h5 := (hu.map S.inc).map f
    rw [map_sub, map_sub] at h5
    exact h5
  · have h := congrArg (Polynomial.map ((residue C).comp f)) (o1 hF hn S v g)
    rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ArtinRees
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem artin_rees {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (P Q : Submodule R M) (hQ : Q.FG) (N : ℕ) : ∃ K : ℕ, ∀ x ∈ P, x ∈ I ^ K • Q → x ∈ I ^ N • P := by
  haveI : Module.Finite R Q := Module.Finite.iff_fg.mpr hQ
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (P.comap Q.subtype)
  refine ⟨k + N, fun x hxP hxQ => ?_⟩
  have hmap : I ^ (k + N) • Q = (I ^ (k + N) • (⊤ : Submodule R Q)).map Q.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hxQ
  obtain ⟨y, hy, rfl⟩ := hxQ
  have hy' : y ∈ I ^ (k + N) • ⊤ ⊓ P.comap Q.subtype := ⟨hy, hxP⟩
  rw [hk _ (Nat.le_add_right k N), Nat.add_sub_cancel_left] at hy'
  have h2 : I ^ N • (I ^ k • ⊤ ⊓ P.comap Q.subtype) ≤ I ^ N • P.comap Q.subtype :=
    Submodule.smul_mono le_rfl inf_le_right
  have h3 := Submodule.mem_map_of_mem (f := Q.subtype) (h2 hy')
  rw [Submodule.map_smul''] at h3
  exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) h3

private theorem val_prod {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {F : UpperTheory.V.Fr.Frame l (ResidueField O)}
    {n : ℕ} (S : Space O F n) (L : List (F.G0 × Fin n × Fin n)) :
    (((L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod : S.A) : S.R) = (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, Subalgebra.coe_mul, ih, List.map_cons, List.prod_cons]
    rfl

theorem UpperTheory.V.Fr.cone_u :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ [IsCO O S.B], Cone O S.B S.u ∧ Integral O S.B S.u := by
  intro l _ O _ _ _ _ F C₀ n hF hn S _
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨hgrI, hgrM, hgr0, hgrFG, hfin, hnoethA, hmem⟩ := gr_A hF hn S
  obtain ⟨hcx, haB, hψB, hAR⟩ := cont_u hF hn S
  have hres : ∀ x : S.B, res O S.B x = res O S.R (x : S.R) := fun x => (res_map S.B.val x).symm
  have hmax : maximalIdeal S.B = S.mB := by
    ext x
    rw [← res_eq_zero_iff O S.B x, hres, res_eq_zero_iff]
    rfl
  have hdiag : ∀ g i, res O S.R (S.ρ.r g i i) = ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun g i => S.lift.2.1.1 g i
  have hpsi : ∀ v i g, res O S.R ((S.ρ.ψ v i g : S.Rˣ) : S.R) =
      ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) :=
    fun v i g => S.lift.2.1.2 v i g
  have hoff : ∀ g (i j : Fin n), i ≠ j → res O S.R (S.ρ.r g i j) = 0 :=
    fun g i j h => S.lift.2.2 g i j h
  have hA : ∀ g i, algebraMap S.B S.A (S.aB g i) = S.u.r g i i := fun _ _ => rfl
  have hPsi : ∃ χ, IsPsi O F n χ ∧ ∀ v i g, algebraMap S.B S.A (χ v i g) = ((S.u.ψ v i g : S.Aˣ) : S.A) := by
    refine ⟨S.ψB, fun v i => ⟨?_, fun g => ?_⟩, fun v i g => rfl⟩
    · rw [hmax]; exact hψB v i
    · rw [hres]; exact hpsi v i g
  refine ⟨⟨fun g i => ⟨S.aB g i, rfl, by rw [hres]; exact hdiag g i⟩, ?_, ?_, ?_, hPsi⟩, ⟨?_, hPsi, ?_⟩⟩
  · intro L hL ⟨s, hs, hne⟩
    have hm : (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod ∈ S.B := S.mon_mem ⟨L, hL, rfl⟩
    refine ⟨⟨_, hm⟩, ?_, Subtype.ext (val_prod S L).symm⟩
    rw [← res_eq_zero_iff O S.B, hres]
    show res O S.R (L.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod = 0
    rw [map_list_prod, List.map_map]
    apply List.prod_eq_zero
    exact List.mem_map.2 ⟨s, hs, hoff _ _ _ hne⟩
  · intro i j
    haveI := isNoetherian_of_fg_of_noetherian _ (hgrFG (w n i - w n j))
    have hle : Submodule.span S.B (Set.range fun g => S.u.r g i j) ≤ S.gr (w n i - w n j) :=
      Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hmem g i j)
    haveI := isNoetherian_of_le hle
    exact Module.Finite.iff_fg.1 inferInstance
  · intro i j N
    rw [hmax]
    obtain ⟨K, hK⟩ := artin_rees S.mB (Submodule.span S.B (Set.range fun g => S.u.r g i j))
      (S.gr (w n i - w n j)) (hgrFG _) N
    obtain ⟨M, hM⟩ := hAR (w n i - w n j) K
    have hc := S.lift.1.1 i j M
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro g
    filter_upwards [hc g] with g' hg'
    rw [Ideal.Quotient.eq] at hg'
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    apply hK
    · exact Submodule.sub_mem _ (Submodule.subset_span ⟨g', rfl⟩) (Submodule.subset_span ⟨g, rfl⟩)
    · apply hM _ (Submodule.sub_mem _ (hmem g' i j) (hmem g i j))
      exact hg'
  · refine ⟨S.trB, ⟨?_, fun g => ?_⟩, fun g => ?_⟩
    · rw [hmax]
      intro N
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have h2 := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (haB i N) g
      filter_upwards [h2] with g' hg'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Space.trB, map_sum, hg']
    · show res O S.B (∑ i, S.aB g i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hres]; exact hdiag g i
    · show algebraMap S.B S.A (∑ i, S.aB g i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Matrix.trace]
      rfl
  · obtain ⟨-, -, -, -, hst⟩ := UpperTheory.V.Fr.star hF
    have hz : ∀ i : Fin n, (S.u.r F.g0 - S.u.r (F.star F.g0)) i i = S.u.r F.g0 i i - S.u.r F.g0 i.rev i.rev :=
      fun i => by rw [Matrix.sub_apply, hst]
    rcases hn with rfl | rfl
    · refine ⟨S.aB F.g0 0 - S.aB F.g0 1, ?_, fun i => ?_⟩
      · rw [map_sub, hres, hres]
        erw [hdiag, hdiag]
        simp [w]
      · rw [hz, map_sub, hA, hA]
        fin_cases i <;> simp [w] <;> ring
    · refine ⟨S.aB F.g0 0 - S.aB F.g0 2, ?_, fun i => ?_⟩
      · rw [map_sub, hres, hres]
        erw [hdiag, hdiag]
        simp [w]
      · rw [hz, map_sub, hA, hA]
        fin_cases i <;> simp [w] <;> ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MinHom
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem aux {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    (h1 : DirectSum.IsInternal 𝒜) (h2 : SetLike.GradedMonoid 𝒜) (η : Ideal A) (hη : η ∈ minimalPrimes A) :
    η = Ideal.span {x | x ∈ η ∧ ∃ j, x ∈ 𝒜 j} := by
  classical
  letI : DirectSum.Decomposition 𝒜 := h1.chooseDecomposition
  letI : GradedRing 𝒜 := { }
  have hp : η.IsPrime := hη.1.1
  have hc : (η.homogeneousCore 𝒜).toIdeal.IsPrime := Ideal.IsPrime.homogeneousCore hp
  have hle : (η.homogeneousCore 𝒜).toIdeal ≤ η := Ideal.toIdeal_homogeneousCore_le 𝒜 η
  have hge : η ≤ (η.homogeneousCore 𝒜).toIdeal := hη.2 ⟨hc, bot_le⟩ hle
  apply le_antisymm
  · refine hge.trans ?_
    show Ideal.homogeneousCore' 𝒜 η ≤ _
    unfold Ideal.homogeneousCore'
    apply Ideal.span_mono
    rintro _ ⟨⟨x, hx⟩, hx', rfl⟩
    exact ⟨hx', hx⟩
  · exact Ideal.span_le.2 fun x hx => hx.1

theorem UpperTheory.V.Fr.min_hom :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η ∈ minimalPrimes S.A, S.IsHom η := by
  intro l _ O _ _ _ _ F C₀ n hF hn S η hη
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.Fr.gr_A hF hn S
  exact aux S.gr h1 h2 η hη
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibreClosed
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem fibre_closed {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (m : Ideal B) [m.IsMaximal] (W : Set (PrimeSpectrum A)) (hW : IsLocallyClosed W) (p : PrimeSpectrum A)
    (hp : p ∈ W) (hm : m ≤ p.asIdeal.comap (algebraMap B A)) :
    ∃ x ∈ W, m ≤ x.asIdeal.comap (algebraMap B A) ∧ x.asIdeal.IsMaximal := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hW
  obtain ⟨hpU, hpZ⟩ := hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hfU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU hU
  have hqmax : (p.asIdeal.comap (algebraMap B A)).IsMaximal := by
    have e := Ideal.IsMaximal.eq_of_le ‹m.IsMaximal› (Ideal.IsPrime.comap (algebraMap B A)).ne_top hm
    rw [← e]
    infer_instance
  letI := Ideal.Quotient.field (p.asIdeal.comap (algebraMap B A))
  haveI : IsJacobsonRing (A ⧸ p.asIdeal) :=
    isJacobsonRing_of_finiteType (A := B ⧸ p.asIdeal.comap (algebraMap B A))
  have hbot : (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 ‹_› ⊥ Ideal.isPrime_bot
  have hf0 : Ideal.Quotient.mk p.asIdeal f ∉ (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpf
  have hf1 : ¬ ∀ J ∈ {J : Ideal (A ⧸ p.asIdeal) | ⊥ ≤ J ∧ J.IsMaximal}, Ideal.Quotient.mk p.asIdeal f ∈ J :=
    fun h => hf0 (Ideal.mem_sInf.2 h)
  push_neg at hf1
  obtain ⟨J, ⟨-, hJ⟩, hfJ⟩ := hf1
  haveI := hJ
  haveI := hJ.isPrime
  have hle : p.asIdeal ≤ J.comap (Ideal.Quotient.mk p.asIdeal) := fun a ha => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact J.zero_mem
  refine ⟨⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩, ⟨hfU ?_, ?_⟩, ?_,
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  · exact hfJ
  · have hpx : p ≤ ⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩ := hle
    exact hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 hpZ) ((PrimeSpectrum.le_iff_mem_closure _ _).1 hpx)
  · exact hm.trans (Ideal.comap_mono hle)

theorem UpperTheory.V.Fr.jac :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ C : Set (PrimeSpectrum S.A), IsClosed C → ∀ U : Set (PrimeSpectrum S.A), IsOpen U → (C ∩ U ∩ S.BB).Nonempty → ∃ x ∈ C ∩ U ∩ S.BB, x.asIdeal.IsMaximal := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C hC U hU hne
  obtain ⟨-, -, -, -, hft, -, -⟩ := gr_A hF hn S
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  haveI : S.mB.IsMaximal := hmax ▸ IsLocalRing.maximalIdeal.isMaximal S.B
  obtain ⟨p, ⟨hpC, hpU⟩, hpm, hpT⟩ := hne
  have hO : IsOpen {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal} :=
    (PrimeSpectrum.isClosed_zeroLocus (S.u.triP : Set S.A)).isOpen_compl
  have hW : IsLocallyClosed (C ∩ U ∩ {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal}) :=
    (hC.isLocallyClosed.inter hU.isLocallyClosed).inter hO.isLocallyClosed
  obtain ⟨x, ⟨⟨hxC, hxU⟩, hxT⟩, hxm, hxmax⟩ := fibre_closed S.mB _ hW p ⟨⟨hpC, hpU⟩, hpT⟩ hpm
  exact ⟨x, ⟨⟨hxC, hxU⟩, hxm, hxT⟩, hxmax⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ResEqOf
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.AdditiveValuation.UnramExtY
namespace KStar.Binom

open IsLocalRing Polynomial

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

theorem adjoinRoot_unramified (hϖ : Irreducible ϖ) {f : O[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (residue O))) :
    ∃ (_ : IsDomain (AdjoinRoot f)) (_ : IsDiscreteValuationRing (AdjoinRoot f)),
      Irreducible (algebraMap O (AdjoinRoot f) ϖ) ∧
        Nat.card (ResidueField (AdjoinRoot f)) = Nat.card (ResidueField O) ^ f.natDegree := by
  classical
  have : Fact (Irreducible (f.map (residue O))) := ⟨hirr⟩
  have hfirr : Irreducible f := Monic.irreducible_of_irreducible_map (residue O) f hf hirr
  have hdom : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hfirr.prime
  have hfin : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hfree : Module.Free O (AdjoinRoot f) := hf.free_adjoinRoot
  have : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite O _
  let J : Ideal (AdjoinRoot f) := Ideal.map (AdjoinRoot.of f) (maximalIdeal O)
  let e : (AdjoinRoot f ⧸ J) ≃+* AdjoinRoot (f.map (residue O)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal O) f
  have hJ : J.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have huniq : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal → M = J := by
    intro M hM
    letI : M.IsMaximal := hM
    have h1 := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap O (AdjoinRoot f)) (by
        intro x
        exact IsIntegral.of_finite O x) M
    have h2 : J ≤ M := by
      rw [Ideal.map_le_iff_le_comap, ← AdjoinRoot.algebraMap_eq, eq_maximalIdeal h1]
    exact (hJ.eq_of_le hM.ne_top h2).symm
  have : IsLocalRing (AdjoinRoot f) := IsLocalRing.of_unique_max_ideal ⟨J, hJ, huniq⟩
  have hmJ : maximalIdeal (AdjoinRoot f) = J := (eq_maximalIdeal hJ).symm
  have hm : maximalIdeal (AdjoinRoot f) = Ideal.span {algebraMap O (AdjoinRoot f) ϖ} := by
    rw [hmJ]
    simp only [J, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      AdjoinRoot.algebraMap_eq]
  have hne : algebraMap O (AdjoinRoot f) ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (FaithfulSMul.algebraMap_injective O (AdjoinRoot f) (by simpa using h))
  have hnf : ¬ IsField (AdjoinRoot f) := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hne
  have hdvr : IsDiscreteValuationRing (AdjoinRoot f) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 1 5).mpr
      (show (maximalIdeal (AdjoinRoot f)).IsPrincipal from ⟨_, hm⟩)
  refine ⟨hdom, hdvr, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hm, ?_⟩
  have e2 : ResidueField (AdjoinRoot f) ≃+* AdjoinRoot (f.map (residue O)) :=
    (Ideal.quotEquivOfEq hmJ).trans e
  have : Module.Finite (ResidueField O) (AdjoinRoot (f.map (residue O))) :=
    (hf.map _).finite_adjoinRoot
  rw [Nat.card_congr e2.toEquiv, Module.natCard_eq_pow_finrank (K := ResidueField O),
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hf.natDegree_map]

end KStar.Binom
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem prim_ex (k K : Type) [Field k] [Field K] [Finite K] [Algebra k K] :
    ∃ g : Polynomial k, g.Monic ∧ Irreducible g ∧ Nonempty (AdjoinRoot g ≃ₐ[k] K) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k K
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  exact ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint,
    ⟨(IntermediateField.adjoinRootEquivAdjoin k hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)⟩⟩

private theorem unr_ex {l : ℕ} (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (K : Type) [Field K] [Finite K] [Algebra O K] (hK : ∀ a ∈ maximalIdeal O, algebraMap O K a = 0) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : IsCoef l O')
      (_ : Algebra O O') (_ : Module.Finite O O'), (maximalIdeal O).map (algebraMap O O') = maximalIdeal O' ∧
      Nonempty (K →ₐ[O] ResidueField O') := by
  letI : Algebra (ResidueField O) K := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O K) hK).toAlgebra
  haveI : IsScalarTower O (ResidueField O) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨g, hg, hgi, ⟨e⟩⟩ := prim_ex (ResidueField O) K
  obtain ⟨f, hf1, -, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := residue O) (p := g) (Polynomial.mem_lifts_of_surjective residue_surjective _) hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hd, hv, hi, hc⟩ := KStar.Binom.adjoinRoot_unramified hϖ hf (hf1 ▸ hgi)
  haveI : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hm : (maximalIdeal O).map (algebraMap O (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f) := by
    rw [hϖ.maximalIdeal_eq, hi.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  haveI hl : IsLocalHom (algebraMap O (AdjoinRoot f)) := ((local_hom_tfae _).out 1 3).2 hm.le
  have hcl : UpperTheory.V.CA.IsCL O (AdjoinRoot f) := UpperTheory.V.CA.cl_fin O O (AdjoinRoot f) (UpperTheory.V.CA.IsCL.of_isCO O O)
  have hfin : Finite (ResidueField (AdjoinRoot f)) := Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ Nat.card_pos.ne')
  have hch : CharP (ResidueField (AdjoinRoot f)) l :=
    charP_of_injective_ringHom (ResidueField.map (algebraMap O (AdjoinRoot f))).injective l
  refine ⟨AdjoinRoot f, inferInstance, hd, hv, ⟨hcl.complete, hfin, hch⟩, inferInstance, inferInstance, hm, ?_⟩
  have h0 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) g = 0 := by
    rw [← hf1]
    have h1 : Polynomial.aeval (residue (AdjoinRoot f) (AdjoinRoot.root f)) f = 0 := by
      have := Polynomial.aeval_algebraMap_apply (ResidueField (AdjoinRoot f)) (AdjoinRoot.root f) f
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] at this
      exact this
    exact (Polynomial.aeval_map_algebraMap (ResidueField O) _ f).trans h1
  exact ⟨((AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ h0).comp e.symm.toAlgHom).restrictScalars O⟩

private theorem res_eq_of {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {x : R} {a : O} (h : x - algebraMap O R a ∈ maximalIdeal R) : res O R x = algebraMap O _ a := by
  have := (res_eq_zero_iff O R _).2 h
  rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

private theorem cpl_univ (O D R : Type) [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    (φ : D →ₐ[O] ResidueField O) [CommRing R] [IsLocalRing R] [Algebra D R] [Algebra O R] [IsScalarTower O D R]
    [(RingHom.ker φ.toRingHom).IsMaximal] (hc : UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R) :
    ∃ (_ : IsCO O R), (∀ a, res O R (algebraMap D R a) = φ a) ∧
      ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
        (∀ a, res O C (f a) = φ a) → ∃! g : R →ₐ[O] C, ∀ a, g (algebraMap D R a) = f a := by
  have hy : ∀ d : D, algebraMap D R d ∈ maximalIdeal R ↔ φ d = 0 := fun d => by
    have := hc.comap_pow 1
    rw [pow_one, pow_one] at this
    rw [← Ideal.mem_comap, this]
    rfl
  have hs : ∀ d : D, ∃ a : O, φ d = algebraMap O _ a ∧ algebraMap D R d - algebraMap O R a ∈ maximalIdeal R :=
    fun d => by
      obtain ⟨a, ha⟩ := residue_surjective (φ d)
      refine ⟨a, ha.symm, ?_⟩
      rw [IsScalarTower.algebraMap_apply O D R, ← map_sub, hy, map_sub, AlgHom.commutes, sub_eq_zero]
      exact ha.symm
  haveI := hc.noeth
  have hco : IsCO O R :=
    { complete := hc.complete
      isLocalHom := ⟨fun a ha => by
        by_contra hn
        have h1 : algebraMap D R (algebraMap O D a) ∈ maximalIdeal R := by
          rw [hy, AlgHom.commutes]
          exact (residue_eq_zero_iff a).2 hn
        rw [← IsScalarTower.algebraMap_apply] at h1
        exact h1 ha⟩
      res_surj := fun r => by
        obtain ⟨d, hd⟩ := hc.dense 1 r
        obtain ⟨a, -, ha⟩ := hs d
        rw [pow_one] at hd
        exact ⟨a, by simpa using add_mem hd ha⟩ }
  refine ⟨hco, fun d => ?_, fun C _ _ _ f hf => ?_⟩
  · obtain ⟨a, h1, h2⟩ := hs d
    rw [h1, res_eq_of h2]
  · obtain ⟨G, ⟨h1, h2⟩, hu⟩ := (UpperTheory.V.CA.cpl_uniq _ hc).1 C (maximalIdeal C) f.toRingHom fun d hd => by
      rw [Ideal.mem_comap, ← res_eq_zero_iff O]
      exact (hf d).trans hd
    have h3 : ∀ d, G (algebraMap D R d) = f d := fun d => DFunLike.congr_fun h1 d
    refine ⟨{ G with commutes' := fun a => ?_ }, h3, fun g hg => ?_⟩
    · rw [IsScalarTower.algebraMap_apply O D R]
      exact (h3 _).trans (f.commutes a)
    · have := hu g.toRingHom ⟨RingHom.ext hg, fun z hz => by
        rw [Ideal.mem_comap, ← res_eq_zero_iff O]
        exact (UpperTheory.V.Alg.res_map g z).trans ((res_eq_zero_iff O R z).2 hz)⟩
      exact AlgHom.ext fun z => DFunLike.congr_fun this z

private theorem cpl_ex (O D : Type) [CommRing O] [IsLocalRing O] [CommRing D] [Algebra O D] [IsNoetherianRing D]
    (φ : D →ₐ[O] ResidueField O) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : D →ₐ[O] R), (∀ a, res O R (j a) = φ a) ∧
      ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (f : D →ₐ[O] C),
        (∀ a, res O C (f a) = φ a) → ∃! g : R →ₐ[O] C, ∀ a, g (j a) = f a := by
  haveI hm : (RingHom.ker φ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun z => by
    obtain ⟨a, rfl⟩ := residue_surjective z
    exact ⟨algebraMap O D a, φ.commutes a⟩
  have key : ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : Algebra D R),
      UpperTheory.V.CA.IsCplAt (RingHom.ker φ.toRingHom) R := by
    obtain ⟨hloc, hc⟩ := UpperTheory.V.CA.cpl_is D (RingHom.ker φ.toRingHom)
    exact ⟨_, _, hloc, _, hc⟩
  obtain ⟨R, _, _, _, hc⟩ := key
  letI : Algebra O R := ((algebraMap D R).comp (algebraMap O D)).toAlgebra
  haveI : IsScalarTower O D R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hco, h1, h2⟩ := cpl_univ O D R φ hc
  exact ⟨R, _, _, hco, IsScalarTower.toAlgHom O D R, h1, h2⟩

private theorem res_fin (O B A : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing B] [Algebra O B]
    [IsCO O B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] (x : Ideal A) [x.IsMaximal]
    (hx : maximalIdeal B ≤ x.comap (algebraMap B A)) : Finite (A ⧸ x) := by
  letI := Ideal.Quotient.field x
  haveI : Finite (ResidueField B) := Finite.of_surjective _ (resMap_bijective O B).2
  letI : Algebra (ResidueField B) (A ⧸ x) := (Ideal.Quotient.lift (maximalIdeal B) (algebraMap B (A ⧸ x))
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (hx ha)).toAlgebra
  haveI : IsScalarTower B (ResidueField B) (A ⧸ x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType (ResidueField B) (A ⧸ x) := Algebra.FiniteType.of_restrictScalars_finiteType B _ _
  haveI : Module.Finite (ResidueField B) (A ⧸ x) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Module.finite_of_finite (ResidueField B)

theorem UpperTheory.V.Fr.loc_ex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ x : Ideal S.A, x.IsMaximal → S.mB ≤ S.π x → Nonempty (S.Loc x) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x hx hB
  have hA : IsNoetherianRing S.A := (gr_A hF hn S).2.2.2.2.2.1
  have hT : Algebra.FiniteType S.B S.A := (gr_A hF hn S).2.2.2.2.1
  obtain ⟨hco, hm⟩ := UpperTheory.V.Fr.co_B hF hn S
  rw [← hm] at hB
  haveI : Finite (S.A ⧸ x) := res_fin O S.B S.A x hB
  letI := Ideal.Quotient.field x
  obtain ⟨O', _, _, _, _, _, _, hu, ⟨e⟩⟩ := unr_ex (l := l) O (S.A ⧸ x) fun a ha => by
    have h1 : algebraMap O S.B a ∈ maximalIdeal S.B := fun h => ha (IsLocalHom.map_nonunit a h)
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hB h1)
  have hD : IsNoetherianRing (TensorProduct O O' S.A) := by
    have h1 : IsNoetherianRing (TensorProduct O S.A O') :=
      Algebra.FiniteType.isNoetherianRing S.A _
    exact isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm O S.A O').toRingEquiv
  let φ : TensorProduct O O' S.A →ₐ[O'] ResidueField O' :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (e.comp (Ideal.Quotient.mkₐ O x)) fun _ _ => Commute.all _ _
  obtain ⟨R, _, _, _, j, h1, h2⟩ := cpl_ex O' _ φ
  letI : Algebra O R := ((algebraMap O' R).comp (algebraMap O O')).toAlgebra
  haveI : IsScalarTower O O' R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hφ : ∀ a : S.A, φ (1 ⊗ₜ a) = e (Ideal.Quotient.mk x a) := fun a => by simp [φ]
  refine ⟨{
    O' := O'
    unr := hu
    R := R
    ι := (j.restrictScalars O).comp Algebra.TensorProduct.includeRight
    lies := ?_
    univ := fun C _ _ _ _ _ f hf => ?_ }⟩
  · ext a
    rw [Ideal.mem_comap, ← res_eq_zero_iff O', ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff e e.toRingHom.injective, ← hφ, ← h1]
    rfl
  · let f' : TensorProduct O O' S.A →ₐ[O'] C :=
      Algebra.TensorProduct.lift (Algebra.ofId _ _) f fun _ _ => Commute.all _ _
    have hf' : ∀ a : S.A, f' (1 ⊗ₜ a) = f a := fun a => by simp [f']
    have e1 : (res O' C).comp f' = φ := Algebra.TensorProduct.ext (by ext) (by
      ext a
      show res O' C (f' (1 ⊗ₜ a)) = φ (1 ⊗ₜ a)
      rw [hf', hf, ← h1]; rfl)
    obtain ⟨g, hg, hu⟩ := h2 C f' fun a => DFunLike.congr_fun e1 a
    refine ⟨g, fun a => (hg _).trans (hf' a), fun g' hg' => hu g' fun a => ?_⟩
    have e2 : g'.comp j = f' := Algebra.TensorProduct.ext (by ext) (by
      ext a
      show g' (j (1 ⊗ₜ a)) = f' (1 ⊗ₜ a)
      rw [hf']; exact hg' a)
    exact DFunLike.congr_fun e2 a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothCharacterExtendsToOpenSubgroup
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.smoothCharacter_extends_to_open_subgroup :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (Q : Type) [CommRing Q] [Algebra (ResidueField O) Q] (ξ : S.A →+* Q), S.FPt ξ → (S.u.map ξ).IsBar (algebraMap (ResidueField O) Q) ∧ (∀ i j, IsLocallyConstant fun g => (S.u.map ξ).r g i j) ∧ ∀ ξ' : S.A →+* Q, S.FPt ξ' → (∀ g i j, ξ' (S.u.r g i j) = ξ (S.u.r g i j)) → ξ' = ξ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ ξ hξ
  have hkey : ∀ ζ : S.A →+* Q, S.FPt ζ → ∀ (b : S.B) (c : O), b - algebraMap O S.B c ∈ S.mB →
      ζ (S.inc b) = algebraMap (ResidueField O) Q (residue O c) := by
    intro ζ hζ b c hbc
    have h1 : S.inc (b - algebraMap O S.B c) ∈ S.x0 := Ideal.mem_map_of_mem _ hbc
    have h2 := hζ.x0 h1
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, map_sub, sub_eq_zero] at h2
    rw [h2, hζ.alg]
  have hres : ∀ (b : S.B) (y : ResidueField O), res O S.R b.val = y →
      ∀ ζ : S.A →+* Q, S.FPt ζ → ζ (S.inc b) = algebraMap (ResidueField O) Q y := by
    intro b y hb ζ hζ
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective y
    apply hkey ζ hζ b c
    show (b - algebraMap O S.B c).val ∈ maximalIdeal S.R
    rw [← res_eq_zero_iff O S.R]
    simp [hb]
  refine ⟨⟨fun g i => ?_, fun v i g => ?_⟩, fun i j => ?_, fun ξ' hξ' hag => ?_⟩
  · have h := S.lift.2.1.1 g i
    exact hres (S.aB g i) _ (by simpa [NRep.map, Space.aB] using h) ξ hξ
  · have h := S.lift.2.1.2 v i g
    exact hres (S.ψB v i g) _ (by simpa [NRep.map, Space.ψB] using h) ξ hξ
  · have hc := ((cont_u hF hn S).1.1 i j) 1
    let f := Ideal.Quotient.lift (S.x0 ^ 1) ξ (fun a ha => hξ.x0 (by rwa [pow_one] at ha))
    convert hc.comp f using 1
    funext g
    rfl
  · apply RingHom.ext
    rintro ⟨x, hx⟩
    refine Algebra.adjoin_induction (p := fun x hx => ξ' ⟨x, hx⟩ = ξ ⟨x, hx⟩) ?_ ?_ ?_ ?_ hx
    · rintro x (hxB | ⟨g, i, j, rfl⟩)
      · obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) x
        have hc' : (⟨x, hxB⟩ : S.B) - algebraMap O S.B c ∈ S.mB := hc
        show ξ' (S.inc ⟨x, hxB⟩) = ξ (S.inc ⟨x, hxB⟩)
        rw [hkey ξ' hξ' _ c hc', hkey ξ hξ _ c hc']
      · exact hag g i j
    · intro r
      show ξ' (algebraMap O S.A r) = ξ (algebraMap O S.A r)
      rw [hξ'.alg, hξ.alg]
    · intro x y hx hy h1 h2
      show ξ' ((⟨x, hx⟩ : S.A) + ⟨y, hy⟩) = ξ ((⟨x, hx⟩ : S.A) + ⟨y, hy⟩)
      rw [map_add (f := _), map_add (f := _), h1, h2]
    · intro x y hx hy h1 h2
      show ξ' ((⟨x, hx⟩ : S.A) * ⟨y, hy⟩) = ξ ((⟨x, hx⟩ : S.A) * ⟨y, hy⟩)
      rw [map_mul, map_mul, h1, h2]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SmoothHomWeightSumNeg
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem w_lt {n : ℕ} {i j : Fin n} (h : j < i) : w n i - w n j < 0 := by
  have h' : (j : ℕ) < (i : ℕ) := h
  unfold w
  split_ifs <;> omega

private theorem sum_neg {α : Type} (f : α → ℤ) (L : List α) (h : ∀ s ∈ L, f s ≤ 0) (h' : ∃ s ∈ L, f s < 0) :
    (L.map f).sum < 0 := by
  have key : ∀ L : List α, (∀ s ∈ L, f s ≤ 0) → (L.map f).sum ≤ 0 := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      have h1 := h a (by simp)
      have h2 := ih (fun s hs => h s (by simp [hs]))
      omega
  induction L with
  | nil => simp at h'
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have hL : ∀ s ∈ L, f s ≤ 0 := fun s hs => h s (by simp [hs])
    have hsum := key L hL
    obtain ⟨s, hs, hs'⟩ := h'
    rcases List.mem_cons.1 hs with rfl | hs
    · omega
    · have := ih hL ⟨s, hs, hs'⟩
      omega

private theorem lc_hom {k G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group k] (χ : G →* k)
    (h : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g * x) '' (χ.ker : Set G), ?_, isOpenMap_mul_left g _ h, ⟨1, χ.ker.one_mem, mul_one g⟩⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : χ x = 1 := MonoidHom.mem_ker.1 hx
  show χ (g * x) = y
  rw [map_mul, hx1, mul_one]
  exact hg

set_option maxHeartbeats 400000 in
theorem UpperTheory.smoothHom_weight_sum_neg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (S : Space O F n) (Q : Type) [CommRing Q] [Nontrivial Q] [Algebra (ResidueField O) Q] (ρ : NRep F n Q), ρ.IsBar (algebraMap (ResidueField O) Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → ∃ ξ : S.A →+* Q, S.FPt ξ ∧ S.u.map ξ = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S Q _ _ _ ρ hbar htri hlc
  letI : IsCO O (ResidueField O) := (co_res O).1
  letI : Algebra O Q := ((algebraMap (ResidueField O) Q).comp (algebraMap O (ResidueField O))).toAlgebra
  haveI : IsScalarTower O (ResidueField O) Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CompactSpace F.G0 := by
    have hc : IsCompact (F.del.ker : Set F.Γ) := (Subgroup.isClosed_of_isOpen _ hF.del_open).isCompact
    exact isCompact_iff_compactSpace.1 hc
  have hres : ∀ c : ResidueField O, res O (ResidueField O) c = c := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    exact (res O (ResidueField O)).commutes a
  have hinj : Function.Injective (algebraMap (ResidueField O) Q) := (algebraMap (ResidueField O) Q).injective
  have hz : ∀ g i j, i < j → ρ.r g i j = 0 := by
    intro g i j h
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, h, rfl⟩
    rw [htri] at hm
    exact Ideal.mem_bot.1 hm
  have hΨ : IsLocallyConstant (F.Ψ : F.Γ → (ResidueField O)ˣ) := lc_hom F.Ψ hF.Ψ_open
  have hcone : Cone O (ResidueField O) ρ := by
    refine ⟨fun g i => ⟨_, (hbar.1 g i).symm, hres _⟩, fun L hsum hex => ?_,
      fun i j => Submodule.fg_span (hlc i j).range_finite, fun i j N => (hlc i j).comp _, ?_⟩
    · refine ⟨0, Ideal.zero_mem _, ?_⟩
      rw [map_zero, eq_comm]
      apply List.prod_eq_zero
      rw [List.mem_map]
      by_contra hcon
      push_neg at hcon
      have hle : ∀ t ∈ L, w n t.2.1 - w n t.2.2 ≤ 0 := by
        intro t ht
        rcases lt_trichotomy t.2.1 t.2.2 with h | h | h
        · exact absurd (hz _ _ _ h) (hcon t ht)
        · rw [h, sub_self]
        · exact (w_lt h).le
      obtain ⟨s, hs, hne⟩ := hex
      have hlt : w n s.2.1 - w n s.2.2 < 0 := by
        rcases lt_trichotomy s.2.1 s.2.2 with h | h | h
        · exact absurd (hz _ _ _ h) (hcon s hs)
        · exact absurd h hne
        · exact w_lt h
      have h2 : (L.map fun t : F.G0 × Fin n × Fin n => w n t.2.1 - w n t.2.2).sum < 0 :=
        sum_neg (fun t : F.G0 × Fin n × Fin n => w n t.2.1 - w n t.2.2) L hle ⟨s, hs, hlt⟩
      exact absurd hsum (ne_of_lt h2)
    · refine ⟨fun v i g => ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O),
        fun v i => ⟨fun N => ?_, fun g => hres _⟩, fun v i g => (hbar.2 v i g).symm⟩
      have hcont : Continuous (F.loc v) :=
        continuous_subtype_val.comp (hF.loc_cont v)
      exact (hΨ.comp_continuous hcont).comp
        (fun u => Ideal.Quotient.mk (maximalIdeal (ResidueField O) ^ N)
          ((u ^ w n i : (ResidueField O)ˣ) : ResidueField O))
  obtain ⟨ξ, β, hmap, hβ⟩ := alg hF hn S (ResidueField O) Q hinj ρ hcone
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  refine ⟨(ξ : S.A →+* Q), ⟨?_, fun c => ξ.commutes c⟩, hmap⟩
  rw [Space.x0, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hb' : b ∈ maximalIdeal S.B := by rw [hmax]; exact hb
  have h0 : β b = 0 := by
    rw [← hres (β b), res_map β b]
    exact (res_eq_zero_iff O S.B b).2 hb'
  show ξ (S.inc b) = 0
  rw [hβ b, h0, map_zero]
end
