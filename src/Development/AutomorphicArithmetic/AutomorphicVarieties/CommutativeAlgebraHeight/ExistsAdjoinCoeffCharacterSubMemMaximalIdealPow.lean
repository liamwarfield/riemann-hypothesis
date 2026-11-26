module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GroupDetExistsSemisimpleRepresentation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.SignLemma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) (N : ℕ) (x : B.B), ∃ y ∈ Algebra.adjoin O ({a | ∃ (i : ℕ) (g : F.G₀), 1 ≤ i ∧ i ≤ n ∧ a = B.u.D.lam i (MonoidAlgebra.single g 1)} ∪ {a | ∃ v i g, a = ((B.u.ψ v i g : B.Bˣ) : B.B)}), x - y ∈ maximalIdeal B.B ^ N := by
  intro l _ F O _ _ _ _ _ _ _ n r B N x
  refine u_gen O B.B _ ?_ N x
  intro R' _ _ _ f f' h
  obtain ⟨p, hp⟩ := pair_map r B.u f
  refine (B.univ R' p).unique hp ⟨?_, fun v i => ?_⟩
  · rw [← hp.1]
    refine d_gext _ _ fun g i h1 h2 => ?_
    have e : ∀ φ : B.B →+* R', (B.u.D.map φ).lam i (MonoidAlgebra.single g 1) =
        φ (B.u.D.lam i (MonoidAlgebra.single g 1)) := fun φ => by
      have := ((d_gmap B.u.D).2.2.1 φ (MonoidAlgebra.single g 1)).2 i
      rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
    rw [e, e]
    exact (h _ (Or.inl ⟨i, g, h1, h2, rfl⟩)).symm
  · rw [← hp.2 v i]
    ext g
    exact (h _ (Or.inr ⟨v, i, g, rfl⟩)).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimform
open IsLocalRing

private theorem height_map_mk_comap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    (hφ : Function.Surjective φ) (I : Ideal S) (hI : I = RingHom.ker φ) (J : Ideal T) :
    ((J.comap φ).map (Ideal.Quotient.mk I)).height = J.height := by
  subst hI
  have h : (J.comap φ).map (Ideal.Quotient.mk (RingHom.ker φ)) =
      J.comap (RingHom.quotientKerEquivOfSurjective hφ) := by
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk (RingHom.ker φ)) Ideal.Quotient.mk_surjective
      (J.comap (RingHom.quotientKerEquivOfSurjective hφ))]
    congr 1
  rw [h, RingEquiv.height_comap]

attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem height_ker_add {B C : Type} [CommRing B] [IsDomain B] [CommRing C] [IsDomain C] [Algebra B C]
    [FaithfulSMul B C] (t N : ℕ) (ht : Algebra.trdeg B C = t) (g : MvPolynomial (Fin N) B →ₐ[B] C)
    (hg : Function.Surjective g) :
    ((RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).height : WithBot ℕ∞) + t = N := by
  let K := FractionRing B
  let L := FractionRing C
  have hBL : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B C L]
    exact (IsFractionRing.injective C L).comp (FaithfulSMul.algebraMap_injective B C)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBL
  letI : Algebra K L := FractionRing.liftAlgebra B L
  have : IsScalarTower B K L := FractionRing.isScalarTower_liftAlgebra B L
  let g' : MvPolynomial (Fin N) K →ₐ[K] L :=
    MvPolynomial.aeval fun i => algebraMap C L (g (MvPolynomial.X i))
  have hgg : ∀ x, g' (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K) x) = algebraMap C L (g x) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, MvPolynomial.algHom_C, MvPolynomial.algHom_C,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | mul_X a i ha =>
      simp only [map_mul, ha]
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      simp [g']
  have hL : IsLocalization ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) K) :=
    MvPolynomial.isLocalization _ _
  have hp : (RingHom.ker g').IsPrime := RingHom.ker_isPrime g'
  have hc : (RingHom.ker g').comap (algebraMap (MvPolynomial (Fin N) B) (MvPolynomial (Fin N) K)) =
      RingHom.ker (g : MvPolynomial (Fin N) B →+* C) := by
    ext x
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, hgg]
    exact map_eq_zero_iff _ (IsFractionRing.injective C L)
  have h1 := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field K N (RingHom.ker g')
  have h2 : ringKrullDim (MvPolynomial (Fin N) K ⧸ RingHom.ker g') = ringKrullDim g'.range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange g').toRingEquiv
  have hft : Algebra.FiniteType K g'.range :=
    Algebra.FiniteType.of_surjective g'.rangeRestrict g'.rangeRestrict_surjective
  have h3 : Algebra.trdeg K g'.range = t := by
    have hmem : ∀ c : C, algebraMap C L c ∈ g'.range := fun c => by
      obtain ⟨x, rfl⟩ := hg c
      exact ⟨_, hgg x⟩
    let j : C →ₐ[B] g'.range.restrictScalars B :=
      (IsScalarTower.toAlgHom B C L).codRestrict (g'.range.restrictScalars B) hmem
    have hj : Function.Injective j := fun a b hab =>
      IsFractionRing.injective C L (congrArg Subtype.val hab)
    have a1 : Algebra.trdeg B C ≤ Algebra.trdeg B g'.range := trdeg_le_of_injective j hj
    have a2 : Algebra.trdeg B g'.range ≤ Algebra.trdeg B L :=
      trdeg_le_of_injective (g'.range.val.restrictScalars B) Subtype.val_injective
    have : Algebra.IsAlgebraic C L := IsLocalization.isAlgebraic L (nonZeroDivisors C)
    have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic K (nonZeroDivisors B)
    have a3 : Algebra.trdeg B L = Algebra.trdeg B C := by
      rw [← trdeg_add_eq B C (A := L), trdeg_eq_zero (R := C) (A := L), add_zero]
    have a4 : Algebra.trdeg B g'.range = Algebra.trdeg K g'.range := by
      have : FaithfulSMul K g'.range :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K g'.range).injective
      rw [← trdeg_add_eq B K (A := g'.range), trdeg_eq_zero (R := B) (A := K), zero_add]
    rw [← a4, ← ht]
    exact le_antisymm (a2.trans a3.le) a1
  rw [h2, ReciprocityTheory.CA.ringKrullDim_eq_of_trdeg_eq_field t h3,
    ← IsLocalization.height_under ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin N))) (RingHom.ker g'), Ideal.under_def, hc] at h1
  exact h1

theorem UpperTheory.V.CA.g_dimform :
    ∀ (B C : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing C] [IsDomain C] [Algebra B C] [FaithfulSMul B C]
      [Algebra.FiniteType B C] (t : ℕ), ReciprocityTheory.CA.IsCMQuot B → Algebra.trdeg B C = t →
        ∀ (𝔪 : Ideal C) [𝔪.IsMaximal], 𝔪.comap (algebraMap B C) = maximalIdeal B →
          (𝔪.height : WithBot ℕ∞) = ringKrullDim B + t := by
  intro B C _ _ _ _ _ _ _ hft t hB ht 𝔪 _ h𝔪
  obtain ⟨P, _, _, f, hP, hf⟩ := hB
  have := hP.1
  obtain ⟨N, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft
  let F : MvPolynomial (Fin N) P →+* MvPolynomial (Fin N) B := MvPolynomial.map f
  have hF : Function.Surjective F := MvPolynomial.map_surjective f hf
  let G : MvPolynomial (Fin N) P →+* C := (g : MvPolynomial (Fin N) B →+* C).comp F
  have hG : Function.Surjective G := hg.comp hF
  have hGC : ∀ a : P, G (MvPolynomial.C a) = algebraMap B C (f a) := fun a => by
    simp [G, F]
  have : (𝔪.comap G).IsMaximal := Ideal.comap_isMaximal_of_surjective G hG
  have hc : (𝔪.comap G).comap MvPolynomial.C = maximalIdeal P := by
    have : (𝔪.comap G).comap MvPolynomial.C = (maximalIdeal B).comap f := by
      ext a
      rw [← h𝔪]
      simp only [Ideal.mem_comap, hGC]
    rw [this]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf)
  obtain ⟨hCM, e1⟩ := ReciprocityTheory.CA.isCM_localization_mvPolynomial hP N (𝔪.comap G) hc
  have : (RingHom.ker G).IsPrime := RingHom.ker_isPrime G
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have e2 := ReciprocityTheory.CA.height_eq_add_of_isCM_localization (𝔪.comap G) (RingHom.ker G) hCM
    (Ideal.ker_le_comap G)
  rw [height_map_mk_comap G hG _ rfl] at e2
  have : (RingHom.ker G).LiesOver (RingHom.ker f) := ⟨by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker, MvPolynomial.algebraMap_eq, hGC]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective B C)).symm⟩
  have e3 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (RingHom.ker f) (RingHom.ker G)
  have hk : RingHom.ker G = (RingHom.ker (g : MvPolynomial (Fin N) B →+* C)).comap F := rfl
  have e4 := height_map_mk_comap F hF ((RingHom.ker f).map (algebraMap P (MvPolynomial (Fin N) P)))
    (by rw [MvPolynomial.algebraMap_eq]; exact (MvPolynomial.ker_map f).symm)
    (RingHom.ker (g : MvPolynomial (Fin N) B →+* C))
  rw [← hk] at e4
  rw [e4] at e3
  have e5 := height_ker_add t N ht g hg
  have e6 := hP.height_add_ringKrullDim_quotient (RingHom.ker f)
  rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hf)] at e6
  have f1 : (RingHom.ker G).height ≠ ⊤ := Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  have key : (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + 𝔪.height =
      (((RingHom.ker G).height : ℕ∞) : WithBot ℕ∞) + (ringKrullDim B + t) := by
    rw [← WithBot.coe_add, ← e2, e1, ← e6, ← e5, e3, WithBot.coe_add]
    abel
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp f1
  rw [← hn] at key
  exact (ENat.WithBot.natCast_add_cancel).mp key
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem UpperTheory.V.CA.localDimension_eq_height {C : Type} [CommRing C] (x : Ideal C) [x.IsPrime] (p : Ideal C)
    (hp : p ≤ x) [(x.map (Ideal.Quotient.mk p)).IsPrime] :
    dimAt x p = ((x.map (Ideal.Quotient.mk p)).height : WithBot ℕ∞) := by
  have hsub : Algebra.algebraMapSubmonoid (C ⧸ p) x.primeCompl = (x.map (Ideal.Quotient.mk p)).primeCompl := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      intro h
      apply hb
      exact (Ideal.mem_quotient_iff_mem hp).mp h
    · intro hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨a, fun ha => hy (Ideal.mem_map_of_mem _ ha), rfl⟩
  haveI : IsLocalization.AtPrime (Localization.AtPrime x ⧸ p.map (algebraMap C (Localization.AtPrime x)))
      (x.map (Ideal.Quotient.mk p)) := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    infer_instance
  unfold dimAt
  exact IsLocalization.AtPrime.ringKrullDim_eq_height _ _

theorem UpperTheory.V.CA.c3b :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] {B C : Type} [CommRing B] [Algebra O B] [IsLocalRing B] [CommRing C] [Algebra B C] [Algebra.FiniteType B C] (x : Ideal C) [x.IsMaximal], IsCL O B → x.comap (algebraMap B C) = maximalIdeal B → ∀ (p : Ideal C) [p.IsPrime], p ≤ x → ∃ t : ℕ, Algebra.trdeg (B ⧸ p.comap (algebraMap B C)) (C ⧸ p) = t ∧ dimAt x p = ringKrullDim (B ⧸ p.comap (algebraMap B C)) + t := by
  intro O _ _ _ _ B C _ _ _ _ _ _ x _ hCL hx p _ hp
  set q := p.comap (algebraMap B C) with hq
  have hqm : q ≤ maximalIdeal B := by
    rw [← hx]
    exact Ideal.comap_mono hp
  haveI : IsLocalRing (B ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : FaithfulSMul (B ⧸ q) (C ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  have hcm : IsCMQuot (B ⧸ q) :=
    cl_cmquot O (B ⧸ q) (cl_quot O B (B ⧸ q) (Ideal.Quotient.mkₐ O q) Ideal.Quotient.mk_surjective hCL)
  have hlt : Algebra.trdeg (B ⧸ q) (C ⧸ p) < Cardinal.aleph0 := by
    open Algebra in exact trdeg_lt_aleph0_of_finiteType
  set t := (Algebra.trdeg (B ⧸ q) (C ⧸ p)).toNat
  have ht : Algebra.trdeg (B ⧸ q) (C ⧸ p) = t := (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm
  have mapmax : ∀ {R : Type} [CommRing R] (I J : Ideal R), J.IsMaximal → I ≤ J →
      (J.map (Ideal.Quotient.mk I)).IsMaximal := by
    intro R _ I J hJ hIJ
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hJ with h | h
    · exfalso
      have h1 : Ideal.Quotient.mk I 1 ∈ J.map (Ideal.Quotient.mk I) := by
        rw [h]
        exact Submodule.mem_top
      rw [Ideal.mem_quotient_iff_mem hIJ] at h1
      exact hJ.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
    · exact h
  haveI hmax : (x.map (Ideal.Quotient.mk p)).IsMaximal := mapmax p x ‹x.IsMaximal› hp
  have hmB : (maximalIdeal B).map (Ideal.Quotient.mk q) = maximalIdeal (B ⧸ q) :=
    IsLocalRing.eq_maximalIdeal (mapmax q _ (IsLocalRing.maximalIdeal.isMaximal B) hqm)
  have hcomap : (x.map (Ideal.Quotient.mk p)).comap (algebraMap (B ⧸ q) (C ⧸ p)) = maximalIdeal (B ⧸ q) := by
    ext b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.mem_comap, ← hmB, Ideal.mem_quotient_iff_mem hqm]
    change Ideal.Quotient.mk p (algebraMap B C b) ∈ _ ↔ _
    rw [Ideal.mem_quotient_iff_mem hp, ← Ideal.mem_comap, hx]
  refine ⟨t, ht, ?_⟩
  rw [UpperTheory.V.CA.localDimension_eq_height x p hp]
  exact g_dimform (B ⧸ q) (C ⧸ p) t hcm ht (x.map (Ideal.Quotient.mk p)) hcomap
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DQuotDet
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_quotDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Group G] (D : GDet n A G) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G], D.IsCont (maximalIdeal A) → ∀ Z : Set (MonoidAlgebra A G), (∀ z ∈ Z, D.Kills z) → ∃ DE : Det n A (D.CHQuot Z), DE.IsCH ∧ DE.pull (D.toQuot Z) = D.toDet := by
  intro n A G _ _ _ _ D _ _ _ _ hc Z hZ
  set f := D.toQuot Z
  have hsurj : Function.Surjective f := RingCon.mkₐ_surjective _
  have hmem : ∀ x, x ∈ D.chBar Z → f x = 0 := by
    intro x hx
    have hr : (D.chBar Z).ringCon x 0 := (TwoSidedIdeal.rel_iff _ _ _).2 (by rwa [sub_zero])
    rw [← map_zero f]
    exact (RingCon.eq _).2 hr
  have hker : ∀ x, f x = 0 → x ∈ D.chBar Z := by
    intro x hx
    rw [← map_zero f] at hx
    have hr := (RingCon.eq _).1 hx
    simpa using (TwoSidedIdeal.rel_iff _ _ _).1 hr
  have hle : TwoSidedIdeal.span (D.CH ∪ Z) ≤ D.chBar Z := by
    unfold GDet.chBar closureIdeal
    refine le_iInf fun N => le_iInf fun H => fun y hy => ?_
    exact TwoSidedIdeal.mem_span_iff.1 hy _ fun z hz =>
      TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) (Or.inl (Or.inl hz))
  have hsub : D.CH ∪ Z ⊆ D.chBar Z := fun x hx =>
    hle (TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hx)
  have hCHk : ∀ z ∈ D.CH, D.Kills z := by
    intro z hz
    have hz' : z ∈ D.toDet.CH := by
      rw [d_toDet_CH]
      exact TwoSidedIdeal.subset_span (R := MonoidAlgebra A G) hz
    exact (d_toDet D z).2.2.2.1 ((d_ker _ z).1.1 (d_ch_ker _ hz'))
  have hK : ∀ x, f x = 0 → x ∈ D.toDet.ker := fun x hx =>
    (d_ker _ x).1.2 ((d_toDet D x).2.2.2.2
      (d_closed D (maximalIdeal A) hc (D.CH ∪ Z)
        (by
          rintro z (hz | hz)
          exacts [hCHk z hz, hZ z hz]) x (hker x hx)))
  obtain ⟨DE, hDE, -⟩ := d_factor D.toDet f hsurj hK
  refine ⟨DE, ?_, hDE⟩
  show DE.CH = ⊥
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := ((d_pull DE f).2.2.2 hsurj).2 y hy
    rw [hDE, d_toDet_CH] at hx
    rw [hmem x ((TwoSidedIdeal.mem_span_iff.1 hx) _ fun z hz => hsub (Or.inl hz))]
    exact TwoSidedIdeal.zero_mem _
  · intro hy
    rw [TwoSidedIdeal.mem_bot] at hy
    rw [hy]
    exact TwoSidedIdeal.zero_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.StableField
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MatIrrIff
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.matIrrIff :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (H : Subgroup G) (ρ : G →* Matrix (Fin n) (Fin n) K),
    U3.MatIrr H ρ ↔ Submodule.span K (Set.range fun h : H => ρ h) = ⊤ := by
  intro K G _ _ _ n H ρ
  have h := UpperTheory.V.AlgebraTools.Det.irrIffSpan (K := K) (ρ.comp H.subtype)
  refine Iff.trans ?_ h
  constructor
  · intro h1 N hN; exact h1 N fun g hg v hv => hN ⟨g, hg⟩ v hv
  · intro h1 N hN; exact h1 N fun g v hv => hN g g.2 v hv
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpen
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.irrOpen :
    ∀ {A G ι : Type} [CommRing A] [Group G] [Fintype ι] [DecidableEq ι] (t : G → A),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] (φ : A →+* K) (ρ : G →* Matrix ι ι K) (p : PrimeSpectrum A), p.asIdeal = RingHom.ker φ →
        (∀ g, (ρ g).trace = φ (t g)) → (p ∈ U ↔ Submodule.span K (Set.range ρ) = ⊤) := by
  intro A G ι _ _ _ _ t
  refine ⟨⋃ g : ι × ι → G,
      ((PrimeSpectrum.basicOpen (Matrix.of fun a b => t (g a * g b)).det : TopologicalSpace.Opens (PrimeSpectrum A)) :
        Set (PrimeSpectrum A)),
    isOpen_iUnion (fun g => (PrimeSpectrum.basicOpen _).isOpen), ?_⟩
  intro K _ φ ρ p hp htr
  rw [UpperTheory.V.AlgebraTools.Det.gramIff, Set.mem_iUnion]
  apply exists_congr
  intro g
  have hM : φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) =
      Matrix.of fun a b => (ρ (g a * g b)).trace := by
    ext a b
    show φ (t (g a * g b)) = (ρ (g a * g b)).trace
    rw [htr]
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hp, RingHom.mem_ker, RingHom.map_det, hM]
end

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.stable_field :
    ∀ {n : ℕ} {A G κ κ' : Type} [CommRing A] [Group G] [Field κ] [IsAlgClosed κ] [Field κ'] [IsAlgClosed κ'] (D : GDet n A G) (f : A →+* κ) (f' : A →+* κ'), RingHom.ker f = RingHom.ker f' → (∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ) → ∃ ρ : G →* Matrix (Fin n) (Fin n) κ', UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f' = GDet.ofRep ρ := by
  intro n A G κ κ' _ _ _ _ _ _ D f f' hker ⟨ρ, hρ, hD⟩
  obtain ⟨ρ', hD'⟩ : ∃ ρ' : G →* Matrix (Fin n) (Fin n) κ', D.map f' = GDet.ofRep ρ' := by
    obtain ⟨r, -, hr⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed (D.map f').toDet
    let ρ' := r.toMonoidHom.comp (MonoidAlgebra.of κ' G)
    have hrep : GDet.repAlg ρ' κ' = r := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, ρ', MonoidAlgebra.lift_single]
      · ext
    refine ⟨ρ', Eq.symm ?_⟩
    suffices h : (GDet.ofRep ρ').toDet = (D.map f').toDet by
      rw [← GDet.ofDet_toDet (GDet.ofRep ρ'), h, GDet.ofDet_toDet]
    rw [← hr, ← hrep]
    refine Det.ext' fun S _ _ x => ?_
    change (GDet.repAlg ρ' S (ofT κ' G S x)).det = (Det.repS (GDet.repAlg ρ' κ') S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g a => ext i j; simp [GDet.repAlg]
  refine ⟨ρ', ?_, hD'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact (UpperTheory.V.AlgebraTools.Det.matIrrIff ⊤ ρ').2 (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htrace (K : Type) [Field K] (φ : A →+* K) (τ : G →* Matrix (Fin n) (Fin n) K)
      (hτ : D.map φ = GDet.ofRep τ) (g : G) :
      (τ g).trace = φ (D.tr (MonoidAlgebra.single g 1)) := by
    have hmap : (D.map φ).chi (MonoidAlgebra.single g 1) =
        (D.chi (MonoidAlgebra.single g 1)).map φ := by
      let _ : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let ψ : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with commutes' := fun _ => Polynomial.map_C φ }
      have hψ (x : A[X]) : ψ x = x.map φ := rfl
      have h := D.nat A[X] K[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
      simpa only [GDet.chi, GDet.map, map_sub, MonoidAlgebra.mapRingHom_single,
        AlgHom.coe_toRingHom, hψ, Polynomial.map_X, map_one] using h
    have hchi : (GDet.ofRep τ).chi (MonoidAlgebra.single g 1) = (τ g).charpoly := by
      simp only [GDet.chi, MonoidAlgebra.mapRingHom_single, map_one]
      change (GDet.repAlg τ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)).det = _
      rw [map_sub, Matrix.charpoly]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [GDet.repAlg, hij]
    rw [hτ, hchi] at hmap
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap]
    simp [GDet.tr, GDet.lam]
  let H : Subgroup G := ⊤
  obtain ⟨U, -, hU⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
    (fun g : H => D.tr (MonoidAlgebra.single (g : G) 1))
  let p : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have hp : p ∈ U := (hU κ f (ρ.comp H.subtype) p rfl (fun g => htrace κ f ρ hD g)).2
    ((UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ).1 hρ)
  exact (UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ').2
    ((hU κ' f' (ρ'.comp H.subtype) p hker (fun g => htrace κ' f' ρ' hD' g)).1 hp)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UQuot
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

namespace UpperTheory.V.CA

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

noncomputable def coord (D : GDet n A G) (t : ℕ × G) : A := D.lam t.1 (MonoidAlgebra.single t.2 1)

theorem coord_ext {D D' : GDet n A G} (h : ∀ t, coord D t = coord D' t) : D = D' := by
  have hlam (E : GDet n A G) (i : ℕ) (y : MonoidAlgebra A G) :
      E.toDet.lam i y = E.lam i y := by
    suffices hchi : E.toDet.chi y = E.chi y by simp only [Det.lam, GDet.lam, hchi]
    change E.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      E.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  have hdet : D.toDet = D'.toDet := by
    refine d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [eq_top_iff]
      rintro x -
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i _ _
      rw [hlam, hlam]
      exact h (i, g)
  rw [← GDet.ofDet_toDet D, hdet, GDet.ofDet_toDet]

theorem coord_map (D : GDet n A G) {B : Type} [CommRing B] (f : A →+* B) (t : ℕ × G) :
    coord (D.map f) t = f (coord D t) := by
  have hchi : (D.map f).chi (MonoidAlgebra.single t.2 1) =
      (D.chi (MonoidAlgebra.single t.2 1)).map f := by
    let : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
    let φ : A[X] →ₐ[A] B[X] :=
      { Polynomial.mapRingHom f with
        commutes' := fun a => by
          change Polynomial.map f (C a) = C (f a)
          exact Polynomial.map_C f }
    refine Eq.trans ?_ (D.nat A[X] B[X] φ
      (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single t.2 1)))
    change D.D B[X] _ = D.D B[X] _
    congr 1
    have hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f := rfl
    rw [hφ]
    simp
  simp only [coord, GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

theorem coord_comap (D : GDet n A G) {H : Type} [Group H] (φ : H →* G) (t : ℕ × H) :
    coord (D.comap φ) t = coord D (t.1, φ t.2) := by
  unfold coord GDet.lam GDet.chi
  congr 2
  change (D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _)).coeff = (D.D A[X] _).coeff
  congr 1
  rw [map_sub]
  simp

theorem exists_comap_quot (D : GDet n A G) (H : Subgroup G) [H.Normal]
    (hD : ∀ h ∈ H, D.Kills (MonoidAlgebra.single h 1 - 1)) :
    ∃ D0 : GDet n A (G ⧸ H), D0.comap (QuotientGroup.mk' H) = D := by
  have hk : ∀ h ∈ H, (MonoidAlgebra.single h 1 - 1 : MonoidAlgebra A G) ∈ D.toDet.ker := by
    intro h hh
    apply (d_ker D.toDet _).1.2
    intro S _ _ y
    change D.D S (ofT A G S (1 + y * (1 ⊗ₜ (MonoidAlgebra.single h 1 - 1)))) = 1
    rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
    exact hD h hh S _
  let f : MonoidAlgebra A G →ₐ[A] MonoidAlgebra A (G ⧸ H) := MonoidAlgebra.mapDomainAlgHom A A (QuotientGroup.mk' H)
  let σ : MonoidAlgebra A (G ⧸ H) →+ MonoidAlgebra A G :=
    { toFun := MonoidAlgebra.mapDomain Quotient.out
      map_zero' := MonoidAlgebra.mapDomain_zero _
      map_add' := MonoidAlgebra.mapDomain_add _ }
  have h1 : ∀ y, f (σ y) = y := fun y => by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [f, σ]
  have h2 : ∀ x, x - σ (f x) ∈ D.toDet.ker := fun x => by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact D.toDet.ker.add_mem ha hb
    | single g r =>
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
      have : MonoidAlgebra.single g r - σ (f (MonoidAlgebra.single g r)) =
          - (MonoidAlgebra.single g r * (MonoidAlgebra.single (h : G) 1 - 1)) := by
        simp [f, σ, hh, mul_sub, MonoidAlgebra.single_mul_single]
      rw [this]
      exact D.toDet.ker.neg_mem (D.toDet.ker.mul_mem_left _ _ (hk h h.2))
  obtain ⟨D', hD', -⟩ := d_factor D.toDet f (fun y => ⟨_, h1 y⟩) fun x hx => by
    simpa [hx] using h2 x
  refine ⟨GDet.ofDet D', GDet.ext fun S _ _ x => ?_⟩
  rw [← GDet.ofDet_toDet D, ← hD']
  change D'.D S (toT A _ S (MonoidAlgebra.mapDomainRingHom S (QuotientGroup.mk' H) x)) =
    D'.D S (Algebra.TensorProduct.map (AlgHom.id S S) f (toT A G S x))
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [f, toT_single]

theorem exists_comap_level [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (D : GDet n A G) (I : Ideal A) (hc : D.IsCont I) {N : ℕ} (hN : I ^ N = ⊥) :
    ∃ H : OpenNormalSubgroup G, ∀ (K : Subgroup G) [K.Normal], K ≤ H.toSubgroup →
      ∃ D0 : GDet n A (G ⧸ K), D0.comap (QuotientGroup.mk' K) = D := by
  have locallyInvariant {X : Type} {f : G → X} (hf : IsLocallyConstant f) :
      ∀ᶠ h in nhds (1 : G), ∀ g, f (g * h) = f g := by
    have hfiber : ∀ y ∈ Set.range f, ∀ᶠ h in nhds (1 : G), ∀ g, f g = y → f (g * h) = y := by
      intro y _
      obtain ⟨T, hT, hW⟩ := IsTopologicalGroup.exist_mul_closure_nhds (hf.isClopen_fiber y)
      filter_upwards [hT] with h hh g hg
      exact hW (Set.mul_mem_mul (show g ∈ {x | f x = y} from hg) hh)
    filter_upwards [(Filter.eventually_all_finite hf.range_finite).2 hfiber] with h hh g
    exact hh _ ⟨g, rfl⟩ g rfl
  have hlocal := (Filter.eventually_all_finite (Set.finite_Iic n)).2 fun i _ =>
    locallyInvariant (hc i N)
  obtain ⟨U, hU, hUo, hU1⟩ := mem_nhds_iff.1 hlocal
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo hU1
  have hcoeff (i : ℕ) (hi : i ≤ n) (h : G) (hh : h ∈ H) (g : G) :
      D.lam i (MonoidAlgebra.single (g * h) 1) = D.lam i (MonoidAlgebra.single g 1) := by
    have heq := hU (hH hh) i hi g
    exact sub_eq_zero.mp (by simpa [hN] using Ideal.Quotient.eq.1 heq)
  have hlam (i : ℕ) (y : MonoidAlgebra A G) : D.toDet.lam i y = D.lam i y := by
    suffices hchi : D.toDet.chi y = D.chi y by simp only [Det.lam, GDet.lam, hchi]
    change D.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
      MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rfl
  have hfinite {k : ℕ} (g g' : Fin k → G) (hg : ∀ a, (g a : G ⧸ H.toSubgroup) = g' a)
      (S : Type) [CommRing S] [Algebra A S] (s : Fin k → S) :
      D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) =
        D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
    have lift_single (w : FreeMonoid (Fin k)) (b : Fin k → G) :
        FreeMonoid.lift (fun a => (MonoidAlgebra.single (b a) 1 : MonoidAlgebra A G)) w =
          MonoidAlgebra.single (FreeMonoid.lift b w) 1 := by
      induction w using FreeMonoid.inductionOn' with
      | one => simp [MonoidAlgebra.one_def]
      | of_mul a w ih => simp [ih, MonoidAlgebra.single_mul_single]
    have lift_quot (w : FreeMonoid (Fin k)) :
        ((FreeMonoid.lift g w : G) : G ⧸ H.toSubgroup) = FreeMonoid.lift g' w := by
      induction w using FreeMonoid.inductionOn' with
      | one => simp
      | of_mul a w ih => simp [ih, hg]
    have heval (b : Fin k → G) :
        D.D S (1 + ∑ a, MonoidAlgebra.single (b a) (s a)) =
          MvPolynomial.aeval s (D.toDet.D (MvPolynomial (Fin k) A)
            (1 + Det.gen fun a => (MonoidAlgebra.single (b a) 1 : MonoidAlgebra A G))) := by
      rw [← D.toDet.nat]
      change _ = D.D S (ofT A G S _)
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Det.gen, map_sum, ofT_tmul]
    rw [heval, heval]
    congr 1
    ext α
    obtain ⟨P, hP, -, hP'⟩ := d_amitsur n k α
    rw [hP', hP']
    refine MvPolynomial.hom_congr_vars ?_ ?_ rfl
    · ext a
      simp
    · intro v hv _
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, lift_single, hlam]
      have hv' := QuotientGroup.eq.1 (lift_quot v.2)
      rw [← hcoeff v.1 (hP v hv).2.1 _ hv', mul_inv_cancel_left]
  have hsum {ι : Type} [Fintype ι] (g g' : ι → G) (hg : ∀ a, (g a : G ⧸ H.toSubgroup) = g' a)
      (S : Type) [CommRing S] [Algebra A S] (s : ι → S) :
      D.D S (1 + ∑ a, MonoidAlgebra.single (g a) (s a)) =
        D.D S (1 + ∑ a, MonoidAlgebra.single (g' a) (s a)) := by
    let e := (Fintype.equivFin ι).symm
    rw [← e.sum_comp, ← e.sum_comp (fun a => MonoidAlgebra.single (g' a) (s a))]
    exact hfinite (g ∘ e) (g' ∘ e) (fun a => hg _) S (s ∘ e)
  have hkills (h : G) (hh : h ∈ H) : D.Kills (MonoidAlgebra.single h 1 - 1) := by
    intro S _ _ u
    have hu : ∃ (ι : Type) (_ : Fintype ι) (g : ι → G) (s : ι → S),
        u = ∑ a, MonoidAlgebra.single (g a) (s a) := by
      induction u using MonoidAlgebra.induction_linear with
      | zero => exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, by simp⟩
      | single g r => exact ⟨Unit, inferInstance, fun _ => g, fun _ => r, by simp⟩
      | add a b ha hb =>
        obtain ⟨ι, _, g, s, rfl⟩ := ha
        obtain ⟨ι', _, g', s', rfl⟩ := hb
        exact ⟨ι ⊕ ι', inferInstance, Sum.elim g g', Sum.elim s s', by simp⟩
    obtain ⟨ι, _, g, s, rfl⟩ := hu
    have hcancel := hsum (ι := ι ⊕ ι) (Sum.elim (fun a => g a * h) g) (Sum.elim g g)
      (by rintro (a | a)
          · simpa using (show h ∈ H.toOpenSubgroup from hh)
          · rfl) S (Sum.elim s fun a => -s a)
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, MonoidAlgebra.single_neg,
      Finset.sum_neg_distrib, add_neg_cancel, add_zero, map_one] at hcancel
    rw [← hcancel]
    congr 2
    simp [Finset.sum_mul, MonoidAlgebra.single_mul_single, sub_eq_add_neg, mul_add]
  exact ⟨H, fun K _ hK => exists_comap_quot D K fun h hh => hkills h (hK hh)⟩

end UpperTheory.V.CA
end
