module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqFirstPageIsoAndDifferential
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSeqExactAtOfTwoMulAddStableRangeLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologicalStabilityTheorem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSyzygyFactorization
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.TruncFirstCycles

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  intro k G _ _ C d hdd hsurj hex
  have hz0 : ∀ x : C 2, (d 0).hom ((d 1).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 0)
    simpa [Rep.hom_comp] using h
  have hz1 : ∀ x : C 3, (d 1).hom ((d 2).hom x) = 0 := by
    intro x
    have h := congrArg (fun f => (Rep.Hom.hom f) x) (hdd 1)
    simpa [Rep.hom_comp] using h
  let K := (d 0).hom.ker
  let ι : Rep.of K.toRepresentation ⟶ C 1 :=
    Rep.ofHom (σ := (C 1).ρ) ⟨K.toSubmodule.subtype, fun g => by ext; rfl⟩
  let bl : C 2 →ₗ[k] K.toSubmodule :=
    (d 1).hom.toLinearMap.codRestrict K.toSubmodule (fun x => hz0 x)
  let b : C 2 ⟶ Rep.of K.toRepresentation :=
    Rep.ofHom (ρ := (C 2).ρ) ⟨bl, fun g => by
      ext x
      exact Rep.hom_comm_apply (d 1) g x⟩
  have hιd : ι ≫ d 0 = 0 := by
    apply Rep.hom_ext
    ext x
    exact x.2
  refine ⟨Rep.of K.toRepresentation, ι, hιd, b, ?_, ?_, ?_, ?_, ?_⟩
  · exact
      { exact := (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful _ <|
          (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ⟨⟨x, hx⟩, rfl⟩
        mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
        epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  · apply Rep.hom_ext
    ext x
    rfl
  · intro z
    obtain ⟨y, hy⟩ := (hex z.1).1 z.2
    exact ⟨y, Subtype.ext hy⟩
  · apply Rep.hom_ext
    ext x
    exact hz1 x
  · intro h2 y
    rw [← h2 y]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end GlobalTheory.HomStab.TruncFirstCycles

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_syzygy_factorization : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → Function.Exact (d 1).hom (d 0).hom → ∃ (Z : Rep k G) (ι : Z ⟶ C 1) (h : ι ≫ d 0 = 0) (b : C 2 ⟶ Z), (ShortComplex.mk ι (d 0) h).ShortExact ∧ b ≫ ι = d 1 ∧ Function.Surjective b.hom ∧ d 2 ≫ b = 0 ∧ (Function.Exact (d 2).hom (d 1).hom → Function.Exact (d 2).hom b.hom) := by
  first
  | exact @GlobalTheory.HomStab.TruncFirstCycles.main
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSequenceRepComplexExact
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SplitSetPermRepChainsIsoSplitSeqChains
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

private theorem split_set_boundary_comp_face_sum (R : Type) [CommRing R] (n p : ℕ) :
    (Finsupp.lmapDomain ℤ ℤ (fun x : SplitSet R n p => (x.1 : List ((Fin n → R) × (Fin n → R))))) ∘ₗ
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face R n p i)) =
    bd _ ∘ₗ Finsupp.lmapDomain ℤ ℤ
      (fun x : SplitSet R n (p + 1) => (x.1 : List ((Fin n → R) × (Fin n → R)))) := by
  apply Finsupp.lhom_ext
  intro l a
  have hlen : l.1.length = p + 1 := l.2.2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  unfold bd
  rw [Finsupp.linearCombination_single, hlen, Finset.smul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => a • ((-1 : ℤ) ^ i • Finsupp.single (l.1.eraseIdx i) (1 : ℤ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) a =
    a • ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) (1 : ℤ))
  simp [Finsupp.smul_single, mul_comm]

theorem splitSet_chains_incl : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  intro R _ n p
  have hD : ∀ c : SplitSet R n (p + 1) →₀ ℤ, (splitD R n p).hom c =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain (face R n p i) c : SplitSet R n p →₀ ℤ) := by
    intro c
    simp [splitD, permMap, Rep.sum_hom, Rep.hom_ofHom, Rep.zsmul_hom, Rep.smul_hom,
      Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, Set.image_univ]
    unfold chains
    congr 1
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
  · intro c
    rw [hD]
    have key := LinearMap.congr_fun (split_set_boundary_comp_face_sum R n p) c
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply] at key
    exact key

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSet_permRep_chains_iso_splitSeq_chains : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  first
  | exact @GlobalTheory.HomStab.splitSet_chains_incl
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab.SplitEx

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧
    (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧
    ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  intro R _ n
  have key := T.splitSet_permRep_chains_iso_splitSeq_chains R n
  have hzero : ∀ p (x : SplitSet R n (p + 1 + 1) →₀ ℤ),
      (splitD R n p).hom ((splitD R n (p + 1)).hom x) = 0 := by
    intro p x
    apply (key p).1
    have h1 := (key p).2.2 ((splitD R n (p + 1)).hom x)
    have h2 := (key (p + 1)).2.2 x
    rw [h2, T.seqChain_boundary_comp_boundary_apply] at h1
    exact h1.trans (Finsupp.mapDomain_zero
      (f := (Subtype.val : SplitSet R n p → List ((Fin n → R) × (Fin n → R)))) (M := ℤ)).symm
  refine ⟨fun p => ?_, fun h0 => ?_, fun p hp => ?_⟩
  · ext c a
    simp [hzero]
  · intro (y : SplitSet R n 0 →₀ ℤ)
    have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y
        ∈ chains (splitSeq R n) 0 := by
      rw [← (key 0).2.1]
      exact LinearMap.mem_range.mpr ⟨y, rfl⟩
    have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
      have hsup : ↑(Finsupp.mapDomain (Subtype.val : SplitSet R n 0 → List ((Fin n → R) × (Fin n → R))) y).support
          ⊆ {l | l ∈ splitSeq R n ∧ l.length = 0} := (Finsupp.mem_supported ℤ _).mp hy
      rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Finset.sum_eq_zero
      intro l hl
      have hlen : l.length = 0 := (hsup hl).2
      simp [hlen]
    obtain ⟨b, hb, hbeq⟩ := h0 _ hy hbd
    have hb' : b ∈ LinearMap.range
        (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n 1 → List ((Fin n → R) × (Fin n → R)))) := by
      rw [(key 1).2.1]
      exact hb
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
    refine ⟨x, (key 0).1 ?_⟩
    exact ((key 0).2.2 x).trans hbeq
  · intro (y : SplitSet R n (p + 1) →₀ ℤ)
    constructor
    · intro hy0
      have hy : Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y
          ∈ chains (splitSeq R n) (p + 1) := by
        rw [← (key (p + 1)).2.1]
        exact LinearMap.mem_range.mpr ⟨y, rfl⟩
      have hbd : bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → List ((Fin n → R) × (Fin n → R))) y) = 0 := by
        have h1 := (key p).2.2 y
        rw [hy0] at h1
        exact h1.symm.trans Finsupp.mapDomain_zero
      obtain ⟨b, hb, hbeq⟩ := hp _ hy hbd
      have hb' : b ∈ LinearMap.range
          (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n (p + 1 + 1) → List ((Fin n → R) × (Fin n → R)))) := by
        rw [(key (p + 1 + 1)).2.1]
        exact hb
      obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hb'
      refine ⟨x, (key (p + 1)).1 ?_⟩
      exact ((key (p + 1)).2.2 x).trans hbeq
    · rintro ⟨x, rfl⟩
      exact hzero p x

end GlobalTheory.HomStab.SplitEx

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.splitSequence_rep_complex_exact : ∀ (R : Type) [CommRing R] (n : ℕ), (∀ p, splitD R n (p + 1) ≫ splitD R n p = 0) ∧ (ExactAt (splitSeq R n) 0 → Function.Surjective (splitD R n 0).hom) ∧ ∀ p, ExactAt (splitSeq R n) (p + 1) → Function.Exact (splitD R n (p + 1)).hom (splitD R n p).hom := by
  first
  | exact @GlobalTheory.HomStab.SplitEx.main
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SurjectiveHMapZeroOfStaircase
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStaircaseStepSurjective
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem homStab_step : ∀ (k G : Type) [CommRing k] [Group G] (C₃ C₂ Z₁ C₁ Z₀ : Rep k G) (a : C₃ ⟶ C₂)
    (b : C₂ ⟶ Z₁) (ι : Z₁ ⟶ C₁) (e : C₁ ⟶ Z₀) (h : ι ≫ e = 0), (ShortComplex.mk ι e h).ShortExact →
    a ≫ b = 0 → ∀ q : ℕ, Function.Surjective (hMap b q).hom →
    Function.Exact (hMap a q).hom (hMap (b ≫ ι) q).hom → Function.Surjective (hMap e (q + 1)).hom := by
  intro k G _ _ C₃ C₂ Z₁ C₁ Z₀ a b ι e h hX hab q hb hex
  have hcomp : ∀ {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) (n : ℕ),
      hMap (f ≫ g) n = hMap f n ≫ hMap g n :=
    fun f g n => (groupHomology.functor k G n).map_comp f g
  have hzero : hMap (0 : C₃ ⟶ Z₁) q = 0 := (groupHomology.functor k G q).map_zero _ _
  have hinj : Function.Injective (hMap ι q).hom := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := hb z
    have hy : (hMap (b ≫ ι) q).hom y = 0 := by
      rw [hcomp]
      simpa using hz
    obtain ⟨x, rfl⟩ := (hex y).1 hy
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← hcomp, hab, hzero]
    rfl
  intro w
  have h3 := groupHomology.mapShortComplex₃_exact hX (i := q + 1) (j := q) rfl
  have hδ : (groupHomology.δ hX (q + 1) q rfl).hom w = 0 := by
    apply hinj
    rw [map_zero]
    exact (groupHomology.mapShortComplex₁ hX (i := q + 1) (j := q) rfl).moduleCat_zero_apply w
  exact (ShortComplex.moduleCat_exact_iff _).1 h3 w hδ

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Staircase

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hd0 hexC hexH
  have ses : ∀ (W X Y : Rep.{0, 0, 0} k G) (u : W ⟶ X) (v : X ⟶ Y) (huv : u ≫ v = 0),
      Function.Exact u.hom v.hom →
      (ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp)).ShortExact := by
    intro W X Y u v huv hex
    have hS' : (ShortComplex.mk (kernel.ι u) u (kernel.condition u)).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel u)
    let φ : ShortComplex.mk (kernel.ι u) (kernel.lift v u huv)
        (by rw [← cancel_mono (kernel.ι v)]; simp) ⟶
        ShortComplex.mk (kernel.ι u) u (kernel.condition u) :=
      { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι v, comm₁₂ := by simp, comm₂₃ := by simp }
    have hinj : Function.Injective (kernel.ι v).hom := (Rep.mono_iff_injective _).mp inferInstance
    refine { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hS',
             mono_f := inferInstance, epi_g := ?_ }
    rw [Rep.epi_iff_surjective]
    intro z
    have hz : v.hom ((kernel.ι v).hom z) = 0 := by
      have h := congrArg (fun f => f.hom z) (kernel.condition v)
      simpa using h
    obtain ⟨y, hy⟩ := (hex _).mp hz
    refine ⟨y, hinj ?_⟩
    have h := congrArg (fun f => f.hom y) (kernel.lift_ι v u huv)
    exact h.trans hy
  have epi0 : ∀ (X Y : Rep.{0, 0, 0} k G) (f : X ⟶ Y), Function.Surjective f.hom →
      Function.Surjective (hMap f 0).hom := by
    intro X Y f hf
    haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf
    exact (ModuleCat.epi_iff_surjective _).mp (groupHomology.epi_map_0_of_epi f)
  have liftSurj : ∀ p, p + 1 ≤ i →
      Function.Surjective (kernel.lift (d p) (d (p + 1)) (hd p)).hom := by
    intro p hp
    exact (Rep.epi_iff_surjective _).mp (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p hp)).epi_g
  have R : ∀ q p, p + 1 + q = i →
      Function.Surjective (hMap (kernel.lift (d p) (d (p + 1)) (hd p)) q).hom := by
    intro q
    induction q with
    | zero =>
      intro p hp
      exact epi0 _ _ _ (liftSurj p (by omega))
    | succ q ih =>
      intro p hp
      have hab : d (p + 3) ≫ kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) = 0 := by
        rw [← cancel_mono (kernel.ι (d (p + 1)))]
        simp [hd]
      have hbι : kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1)) =
          d (p + 2) := kernel.lift_ι _ _ _
      have hE : Function.Exact (hMap (d (p + 3)) q).hom
          (hMap (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1)) ≫ kernel.ι (d (p + 1))) q).hom := by
        rw [hbι]
        exact hexH (p + 2) q (by omega) (by omega)
      exact homStab_step k G (C (p + 4)) (C (p + 3)) (kernel (d (p + 1))) (C (p + 2)) (kernel (d p))
        (d (p + 3)) (kernel.lift (d (p + 1)) (d (p + 2)) (hd (p + 1))) (kernel.ι (d (p + 1)))
        (kernel.lift (d p) (d (p + 1)) (hd p)) _
        (ses _ _ _ (d (p + 1)) (d p) (hd p) (hexC p (by omega))) hab q (ih (p + 1) (by omega)) hE
  cases i with
  | zero => exact epi0 _ _ _ hd0
  | succ q =>
    have ses0 : (ShortComplex.mk (kernel.ι (d 0)) (d 0) (kernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel (d 0))
        mono_f := inferInstance
        epi_g := (Rep.epi_iff_surjective _).mpr hd0 }
    have hab : d 2 ≫ kernel.lift (d 0) (d 1) (hd 0) = 0 := by
      rw [← cancel_mono (kernel.ι (d 0))]
      simp [hd]
    have hbι : kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0) = d 1 := kernel.lift_ι _ _ _
    have hE : Function.Exact (hMap (d 2) q).hom
        (hMap (kernel.lift (d 0) (d 1) (hd 0) ≫ kernel.ι (d 0)) q).hom := by
      rw [hbι]
      exact hexH 1 q (by omega) (by omega)
    exact homStab_step k G (C 3) (C 2) (kernel (d 0)) (C 1) (C 0) (d 2)
      (kernel.lift (d 0) (d 1) (hd 0)) (kernel.ι (d 0)) (d 0) _ ses0 hab q (R q 0 (by omega)) hE

end GlobalTheory.HomStab.Staircase

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.surjective_hMap_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 1 ≤ p → p + q = i → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Surjective (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.Staircase.main
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HomologyRowExactOfStabilisationPattern
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.Row

theorem hMap_zero' {k G : Type} [CommRing k] [Group G] (A B : Rep k G) (n : ℕ) :
    hMap (0 : A ⟶ B) n = 0 := by
  simp [hMap, groupHomology.map]

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p),
    (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k)
    (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ),
    (∀ p q, p ≤ T → IsIso (e p q)) →
    (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) →
    ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) →
    (Odd p → Function.Surjective (s (p + 1) q).hom) →
    Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  intro k G _ _ C d hd M e s T hiso hrel p q hp hinj hsurj
  have bij : ∀ p q, p ≤ T → Function.Bijective (e p q).hom := fun p q h =>
    (ConcreteCategory.isIso_iff_bijective (e p q)).1 (hiso p q h)
  have rel : ∀ p q, p + 1 ≤ T → ∀ m, (hMap (d p) q).hom ((e (p + 1) q).hom m) =
      (if Even p then s p q ≫ e p q else 0).hom m :=
    fun p q h m => congrArg (fun f => ModuleCat.Hom.hom f m) (hrel p q h)
  intro y
  obtain ⟨m, rfl⟩ := (bij (p + 1) q (by omega)).2 y
  rcases Nat.even_or_odd p with hev | hod
  · have hnot : ¬ Even (p + 1) := by
      rw [Nat.even_add_one]
      exact not_not.2 hev
    rw [rel p q (by omega), if_pos hev]
    constructor
    · intro h0
      have h1 : (s p q).hom m = 0 := by
        apply (bij p q (by omega)).1
        rw [map_zero]
        exact h0
      have h2 : m = 0 := by
        apply hinj hev
        rw [h1, map_zero]
      exact ⟨0, by rw [h2, map_zero, map_zero]⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := (bij (p + 2) q hp).2 z
      have hw := rel (p + 1) q (by omega) w
      rw [if_neg hnot] at hw
      have hm : (e (p + 1) q).hom m = 0 := by
        rw [← hz]
        exact hw
      have hm0 : m = 0 := (bij (p + 1) q (by omega)).1 (by rw [hm, map_zero])
      rw [hm0, map_zero]
  · have hnot : ¬ Even p := Nat.not_even_iff_odd.2 hod
    have hev1 : Even (p + 1) := hod.add_one
    rw [rel p q (by omega), if_neg hnot]
    constructor
    · intro _
      obtain ⟨w, hw⟩ := hsurj hod m
      refine ⟨(e (p + 2) q).hom w, ?_⟩
      rw [rel (p + 1) q (by omega), if_pos hev1, ← hw]
      rfl
    · intro _
      rfl

end GlobalTheory.HomStab.Row

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.homology_row_exact_of_stabilisation_pattern : ∀ (k G : Type) [CommRing k] [Group G] (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q) (T : ℕ), (∀ p q, p ≤ T → IsIso (e p q)) → (∀ p q, p + 1 ≤ T → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → ∀ p q, p + 2 ≤ T → (Even p → Function.Injective (s p q).hom) → (Odd p → Function.Surjective (s (p + 1) q).hom) → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom := by
  first
  | exact @GlobalTheory.HomStab.Row.main
  | exact @GlobalTheory.HomStab.Row.hMap_zero'
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyGLStabSurjectiveOfStableRangeInduct
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStabilisationSurjectiveBottom
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem stab_surj_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  intro k G _ _ i C d hd hs hex M e s hiso hsq hinj hsur
  have hsurjH : Function.Surjective (hMap (d 0) i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i C d hd hs hex ?_
    intro p q hp hpq
    refine GlobalTheory.T.homology_row_exact_of_stabilisation_pattern k G C d hd M e s (i + 2) hiso hsq p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev (by obtain ⟨r, hr⟩ := hev; omega) hpq
    · intro hodd
      exact hsur (p + 1) q hodd.add_one (by omega) (by omega)
  have h0 : e 1 i ≫ hMap (d 0) i = s 0 i ≫ e 0 i := by
    have hev : Even 0 := ⟨0, rfl⟩
    rw [hsq 0 i (by omega)]
    exact if_pos hev
  haveI := hiso 0 i (by omega)
  haveI := hiso 1 i (by omega)
  have b0 := ConcreteCategory.bijective_of_isIso (e 0 i)
  have b1 := ConcreteCategory.bijective_of_isIso (e 1 i)
  intro y
  obtain ⟨w, hw⟩ := hsurjH (e 0 i y)
  obtain ⟨x, rfl⟩ := b1.2 w
  refine ⟨x, b0.1 ?_⟩
  rw [← hw]
  have h1 := congrArg (fun f : M 1 i ⟶ groupHomology (C 0) i => f.hom x) h0
  simpa using h1.symm

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_surjective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 2 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 2 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i → Function.Injective (s p q).hom) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Surjective (s p q).hom) → Function.Surjective (s 0 i).hom := by
  first
  | exact @GlobalTheory.HomStab.stab_surj_bottom
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem grpHMap_stab_surjective_congr (R : Type) [CommRing R] (i a b a' b' : ℕ) (h : a ≤ b) (h' : a' ≤ b') (ha : a = a') (hb : b = b')
    (hs : Function.Surjective (grpHMap (stab R a b h) i).hom) :
    Function.Surjective (grpHMap (stab R a' b' h') i).hom := by
  subst ha hb; exact hs

theorem grpHMap_stab_surjective_step : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom := by
  intro R _ s hsr i IH m m' h hm hi
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.splitSeq_firstPage_iso_and_differential R s hsr (m + 1)
  obtain ⟨hdd, hd0, hex⟩ := GlobalTheory.T.splitSequence_rep_complex_exact R (m + 1)
  have key := GlobalTheory.T.quillen_stabilisation_surjective_bottom ℤ (GL (Fin (m + 1)) R) i (splitRep R (m + 1)) (splitD R (m + 1)) hdd
    (hd0 (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hsr (m + 1) 0 (by omega)))
    (fun p hp => hex p (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hsr (m + 1) (p + 1) (by omega)))
    (fun p q => grpH (GL (Fin (m + 1 - p)) R) q) e
    (fun p q => grpHMap (stab R (m + 1 - (p + 1)) (m + 1 - p) (by omega)) q)
    (fun p q hp => he p q (by omega))
    (fun p q hp => hc p q (by omega))
    (fun p q hp h2 hpq => (IH q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).2 (by omega))
    (fun p q hp h2 hpq => (IH q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).1 (by omega))
  exact grpHMap_stab_surjective_congr R i _ _ m m' _ h (by omega) (by omega) key

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.groupHomology_GL_stab_surjective_of_stableRange_induction : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom := by
  first
  | exact @GlobalTheory.HomStab.grpHMap_stab_surjective_step
  | exact @GlobalTheory.HomStab.grpHMap_stab_surjective_congr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyGLStabInjectiveOfStableRangeInducti
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.QuillenStabilisationInjectiveBottom
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactHMapOneZeroOfStaircase
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab.StairMid

variable {k G : Type} [CommRing k] [Group G]

def shC (C : ℕ → Rep k G) (Z : Rep k G) : ℕ → Rep k G
  | 0 => Z
  | n + 1 => C (n + 2)

def shD (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p) (Z : Rep k G) (b : C 2 ⟶ Z) :
    ∀ p, shC C Z (p + 1) ⟶ shC C Z p
  | 0 => b
  | p + 1 => d (p + 2)

theorem main : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  intro k G _ _ i C d hd hs hex hH
  obtain ⟨Z, ι, hι, b, hse, hbι, hbs, hdb, hexb⟩ := GlobalTheory.T.exists_syzygy_factorization k G C d hd hs (hex 0 (by omega))
  have hfun : ∀ {A B : Rep k G} (f : A ⟶ B), hMap f i = (groupHomology.functor k G i).map f := fun f => rfl
  have hsurj : Function.Surjective (hMap b i).hom := by
    refine GlobalTheory.T.surjective_hMap_zero_of_staircase k G i (shC C Z) (shD C d Z b) ?_ hbs ?_ ?_
    · intro p
      cases p with
      | zero => exact hdb
      | succ p => exact hd (p + 2)
    · intro p hp
      cases p with
      | zero => exact hexb (hex 1 (by omega))
      | succ p => exact hex (p + 2) (by omega)
    · intro p q hp hpq
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      exact hH (r + 2) q (by omega) (by omega)
  have hles := (ShortComplex.moduleCat_exact_iff _).1 (groupHomology.mapShortComplex₂_exact hse i)
  have hcomp : hMap (d 1) i = hMap b i ≫ hMap ι i := by
    rw [hfun, hfun, hfun, ← hbι]
    exact (groupHomology.functor k G i).map_comp b ι
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hles x hx
    obtain ⟨z, rfl⟩ := hsurj y
    refine ⟨z, ?_⟩
    rw [hcomp]
    exact hy
  · rintro ⟨z, rfl⟩
    have h0 : hMap (d 1) i ≫ hMap (d 0) i = 0 := by
      have e := (groupHomology.functor k G i).map_comp (d 1) (d 0)
      rw [hd 0, Functor.map_zero] at e
      rw [hfun, hfun]
      exact e.symm
    rw [← ModuleCat.comp_apply, h0]
    rfl

end GlobalTheory.HomStab.StairMid

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exact_hMap_one_zero_of_staircase : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → (∀ p q, 2 ≤ p → p + q = i + 1 → Function.Exact (hMap (d (p + 1)) q).hom (hMap (d p) q).hom) → Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
  first
  | exact @GlobalTheory.HomStab.StairMid.main
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory

theorem injective_stabilisation_bottom_of_rows_exact : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  intro k G _ _ i C d hdd hsurj hex M e s hiso hcomm hinj hsur
  have hE : Function.Exact (hMap (d 1) i).hom (hMap (d 0) i).hom := by
    refine T.exact_hMap_one_zero_of_staircase k G i C d hdd hsurj hex ?_
    intro p q hp hpq
    refine T.homology_row_exact_of_stabilisation_pattern k G C d hdd M e s (i + 3) hiso hcomm p q (by omega) ?_ ?_
    · intro hev
      exact hinj p q hev hp hpq
    · intro hodd
      have h3 : 3 ≤ p := by
        obtain ⟨m, rfl⟩ := hodd
        omega
      exact hsur (p + 1) q (by simpa using hodd.add_one) (by omega) (by omega)
  have h0 := hcomm 0 i (by omega)
  have h1 := hcomm 1 i (by omega)
  simp only [Even.zero, if_true] at h0
  have h1' : e 2 i ≫ hMap (d 1) i = 0 := by
    simpa using h1
  haveI := hiso 1 i (by omega)
  haveI := hiso 2 i (by omega)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hx1 : (hMap (d 0) i).hom ((e 1 i).hom x) = 0 := by
    have := congrArg (fun f => f.hom x) h0
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this, hx, map_zero]
  obtain ⟨y, hy⟩ := (hE _).mp hx1
  have hy2 : y = (e 2 i).hom ((inv (e 2 i)).hom y) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.inv_hom_id]
    rfl
  have hzero : (e 1 i).hom x = 0 := by
    rw [← hy, hy2]
    have := congrArg (fun f => f.hom ((inv (e 2 i)).hom y)) h1'
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    rw [this]
    rfl
  have : x = (inv (e 1 i)).hom ((e 1 i).hom x) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, IsIso.hom_inv_id]
    rfl
  rw [this, hzero, map_zero]

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.quillen_stabilisation_injective_bottom : ∀ (k G : Type) [CommRing k] [Group G] (i : ℕ) (C : ℕ → Rep k G) (d : ∀ p, C (p + 1) ⟶ C p), (∀ p, d (p + 1) ≫ d p = 0) → Function.Surjective (d 0).hom → (∀ p, p + 1 ≤ i + 1 → Function.Exact (d (p + 1)).hom (d p).hom) → ∀ (M : ℕ → ℕ → ModuleCat.{0} k) (e : ∀ p q, M p q ⟶ groupHomology (C p) q) (s : ∀ p q, M (p + 1) q ⟶ M p q), (∀ p q, p ≤ i + 3 → IsIso (e p q)) → (∀ p q, p + 1 ≤ i + 3 → e (p + 1) q ≫ hMap (d p) q = if Even p then s p q ≫ e p q else 0) → (∀ p q, Even p → 2 ≤ p → p + q = i + 1 → Function.Injective (s p q).hom) → (∀ p q, Even p → 4 ≤ p → p + q = i + 2 → Function.Surjective (s p q).hom) → Function.Injective (s 0 i).hom := by
  first
  | exact @GlobalTheory.injective_stabilisation_bottom_of_rows_exact
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory

theorem homStab_GL_inj_step : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom := by
  intro R _ s hs i ih m m' h hm hi
  subst hm
  obtain ⟨e, he, hed⟩ := GlobalTheory.T.splitSeq_firstPage_iso_and_differential R s hs (m + 1)
  obtain ⟨hdd, hsurj, hex⟩ := GlobalTheory.T.splitSequence_rep_complex_exact R (m + 1)
  have key := GlobalTheory.T.quillen_stabilisation_injective_bottom ℤ (GL (Fin (m + 1)) R) i (splitRep R (m + 1)) (splitD R (m + 1)) hdd
    (hsurj (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hs (m + 1) 0 (by omega)))
    (fun p hp => hex p (GlobalTheory.T.splitSeq_exactAt_of_two_mul_add_stableRange_le R s hs (m + 1) (p + 1) (by omega)))
    (fun p q => grpH (GL (Fin (m + 1 - p)) R) q) e
    (fun p q => grpHMap (stab R (m + 1 - (p + 1)) (m + 1 - p) (by omega)) q)
    (fun p q hp => he p q (by omega))
    (fun p q hp => hed p q (by omega))
    (fun p q hp h2 hpq => (ih q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).2 (by omega))
    (fun p q hp h4 hpq => (ih q (m + 1 - (p + 1)) (m + 1 - p) (by omega) (by omega) (by omega)).1 (by omega))
  exact key

end GlobalTheory

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.groupHomology_GL_stab_injective_of_stableRange_induction : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → ∀ i : ℕ, (∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 → (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧ (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom)) → ∀ m m' (h : m ≤ m'), m' = m + 1 → 2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom := by
  first
  | exact @GlobalTheory.homStab_GL_inj_step
end
end

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem kStability_main : UpperTheory.V.Published.KStability := by
  intro R _ s hs
  have key : ∀ i : ℕ, ∀ m m' (h : m ≤ m'), m' = m + 1 →
      (2 * i + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) i).hom) ∧
      (2 * i + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) i).hom) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      have hyp : ∀ q m m' (h : m ≤ m'), q < i → m' = m + 1 →
          (2 * q + s + 1 ≤ m → Function.Surjective (grpHMap (stab R m m' h) q).hom) ∧
          (2 * q + s + 2 ≤ m → Function.Injective (grpHMap (stab R m m' h) q).hom) :=
        fun q m m' h hq hm => ih q hq m m' h hm
      intro m m' h hm
      exact ⟨GlobalTheory.T.groupHomology_GL_stab_surjective_of_stableRange_induction R s hs i hyp m m' h hm, GlobalTheory.T.groupHomology_GL_stab_injective_of_stableRange_induction R s hs i hyp m m' h hm⟩
  intro i n hn
  have h1 := key i n (n + 1) (Nat.le_succ n) rfl
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨(h1.2 hn), (h1.1 (by omega))⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
end
end

theorem PositivityTheory.v8.KStability.kStability : UpperTheory.V.Published.KStability :=
  GlobalTheory.HomStab.kStability_main
