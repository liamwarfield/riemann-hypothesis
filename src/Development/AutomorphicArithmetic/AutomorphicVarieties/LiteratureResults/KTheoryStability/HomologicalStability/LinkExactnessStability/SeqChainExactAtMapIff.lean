module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainExactAtMapIff
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCxMap

theorem bd_mapDomain {V W : Type} (e : V → W) (c : List V →₀ ℤ) :
    bd W (Finsupp.lmapDomain ℤ ℤ (List.map e) c) = Finsupp.lmapDomain ℤ ℤ (List.map e) (bd V c) := by
  have key : (bd W).comp (Finsupp.lmapDomain ℤ ℤ (List.map e)) =
      (Finsupp.lmapDomain ℤ ℤ (List.map e)).comp (bd V) := by
    apply Finsupp.lhom_ext
    intro l n
    simp [bd, Finsupp.linearCombination_single, Finsupp.mapDomain_single, Finset.smul_sum,
      Finsupp.mapDomain_finsetSum, Finsupp.mapDomain_smul, List.eraseIdx_map,
      ← Finsupp.single_mul]
  exact LinearMap.congr_fun key c

theorem chains_map {V W : Type} (e : V → W) (F : Set (List V)) (q : ℕ) :
    chains (List.map e '' F) q = (chains F q).map (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
  unfold chains
  rw [Finsupp.lmapDomain_supported]
  congr 1
  ext l
  constructor
  · rintro ⟨⟨l', hl', rfl⟩, hlen⟩
    exact ⟨l', ⟨hl', by simpa using hlen⟩, rfl⟩
  · rintro ⟨l', ⟨hl', hlen⟩, rfl⟩
    exact ⟨⟨l', hl', rfl⟩, by simpa using hlen⟩

end GlobalTheory.SeqCxMap

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_exactAt_map_iff : ∀ (V W : Type) (e : V → W), Function.Injective e → ∀ (F : Set (List V)) (p : ℕ), ExactAt (List.map e '' F) p ↔ ExactAt F p := by
  intro V W e he F p
  have hinj : Function.Injective (Finsupp.lmapDomain ℤ ℤ (List.map e)) := by
    intro x y hxy
    exact Finsupp.mapDomain_injective (List.map_injective_iff.mpr he) hxy
  unfold GlobalTheory.SeqCx.ExactAt
  constructor
  · intro h c hc hbc
    obtain ⟨b, hb, hbb⟩ := h (Finsupp.lmapDomain ℤ ℤ (List.map e) c)
      (by rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hc)
      (by rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero])
    rw [GlobalTheory.SeqCxMap.chains_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨b', hb', hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain]; exact hbb)⟩
  · intro h c hc hbc
    rw [GlobalTheory.SeqCxMap.chains_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨b', hb', hbb⟩ := h c' hc'
      (hinj (by rw [← GlobalTheory.SeqCxMap.bd_mapDomain, hbc, map_zero]))
    refine ⟨Finsupp.lmapDomain ℤ ℤ (List.map e) b', ?_, ?_⟩
    · rw [GlobalTheory.SeqCxMap.chains_map]; exact Submodule.mem_map_of_mem hb'
    · rw [GlobalTheory.SeqCxMap.bd_mapDomain, hbb]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainBoundaryCompBoundaryApply
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.BdBd

theorem bd_single (V : Type) (l : List V) (r : ℤ) :
    bd V (Finsupp.single l r) =
      r • ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ) := by
  simp [bd, Finsupp.linearCombination_single]

noncomputable def consMap (V : Type) (x : V) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)

theorem bd_single_cons (V : Type) (x : V) (l : List V) :
    bd V (Finsupp.single (x :: l) 1) =
      Finsupp.single l 1 - consMap V x (bd V (Finsupp.single l 1)) := by
  rw [bd_single, bd_single, one_smul, one_smul, List.length_cons, Finset.sum_range_succ']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [consMap, map_sum, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, pow_zero, one_smul, pow_succ, mul_neg_one,
    neg_smul, Finset.sum_neg_distrib]
  abel

theorem bd_consMap (V : Type) (x : V) :
    bd V ∘ₗ consMap V x = LinearMap.id - consMap V x ∘ₗ bd V := by
  apply Finsupp.lhom_ext
  intro l r
  have h : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [h]
  simp only [map_zsmul]
  rw [show consMap V x (Finsupp.single l 1) = Finsupp.single (x :: l) 1 by
    simp [consMap, Finsupp.mapDomain_single], bd_single_cons, smul_sub]

theorem bd_bd_single (V : Type) (l : List V) : bd V (bd V (Finsupp.single l 1)) = 0 := by
  induction l with
  | nil => simp [bd_single]
  | cons x l ih =>
    rw [bd_single_cons, map_sub]
    have := congrArg (fun f => f (bd V (Finsupp.single l 1))) (bd_consMap V x)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
    rw [this, ih, map_zero]
    abel

end GlobalTheory.SeqCx.BdBd

namespace GlobalTheory.SeqCx

theorem bd_bd : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  intro V c
  have h : bd V ∘ₗ bd V = 0 := by
    apply Finsupp.lhom_ext
    intro l r
    have e : Finsupp.single l r = r • Finsupp.single l (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    rw [e, map_zsmul, map_zsmul, GlobalTheory.SeqCx.BdBd.bd_bd_single, smul_zero]
  exact congrArg (fun f => f c) h

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_boundary_comp_boundary_apply : ∀ (V : Type) (c : List V →₀ ℤ), bd V (bd V c) = 0 := by
  exact @GlobalTheory.SeqCx.bd_bd
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsFreeResolutionShortExact
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem exists_free_shortExact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  intro k G _ _ A
  let e : Rep.free k G A ⟶ A := Rep.freeLift k G A (fun x => x)
  have he : Epi e := (Rep.epi_iff_surjective e).2 fun x =>
    ⟨Finsupp.single x (MonoidAlgebra.single 1 1), by
      simp [e, Representation.freeLift_single_single]⟩
  exact ⟨A, kernel e, kernel.ι e, e, kernel.condition e,
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel e) inferInstance he⟩

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.exists_free_resolution_short_exact : ∀ (k G : Type) [CommRing k] [Group G] (A : Rep k G), ∃ (ι : Type) (K : Rep k G) (i : K ⟶ Rep.free k G ι) (e : Rep.free k G ι ⟶ A) (h : i ≫ e = 0), (ShortComplex.mk i e h).ShortExact := by
  first
  | exact @GlobalTheory.HomStab.exists_free_shortExact
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ProjectiveRepGroupHomologyPosVanishes
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

theorem isZero_groupHomology_succ_of_projective : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  intro k G _ _ P hP n
  classical
  let S : Subgroup G := ⊥
  let B : Rep k S := Rep.res S.subtype P
  let adj := Rep.indResAdjunction k S.subtype
  let ε : (Rep.indFunctor k S.subtype).obj B ⟶ P := adj.counit.app P
  have hε : Epi ε := by
    rw [Rep.epi_iff_surjective]
    intro x
    refine ⟨(adj.unit.app B).hom x, ?_⟩
    have h2 := congrArg (fun f => f.hom x) (adj.right_triangle_components P)
    exact h2
  let s := Projective.factorThru (𝟙 P) ε
  have hs : s ≫ ε = 𝟙 P := Projective.factorThru_comp _ _
  have hZ : IsZero (groupHomology (Rep.ind S.subtype B) (n + 1)) :=
    (isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (groupHomology.indIso S B (n + 1))
  rw [IsZero.iff_id_eq_zero]
  have hid : (groupHomology.functor k G (n + 1)).map (s ≫ ε) = 𝟙 _ := by
    rw [hs]
    exact CategoryTheory.Functor.map_id _ _
  refine Eq.trans hid.symm ?_
  rw [CategoryTheory.Functor.map_comp,
    hZ.eq_of_tgt ((groupHomology.functor k G (n + 1)).map s) 0]
  exact zero_comp

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.projective_rep_groupHomology_pos_vanishes : ∀ (k G : Type) [CommRing k] [Group G] (P : Rep k G), Projective P → ∀ n : ℕ, IsZero (groupHomology P (n + 1)) := by
  first
  | exact @GlobalTheory.HomStab.isZero_groupHomology_succ_of_projective
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.GroupHomologyLongExactMapsNaturalOfRes
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

private theorem groupHomology_chainsMap_comp_comm_of_compat (k G H : Type) [CommRing k] [Group G] [Group H]
    (φ : H →* G) (A B : Rep k H) (C D : Rep k G)
    (f : A ⟶ B) (g : C ⟶ D) (u : A ⟶ Rep.res φ C) (v : B ⟶ Rep.res φ D)
    (h : ∀ a, v.hom (f.hom a) = g.hom (u.hom a)) :
    groupHomology.chainsMap (MonoidHom.id H) f ≫ groupHomology.chainsMap φ v =
      groupHomology.chainsMap φ u ≫ groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp [groupHomology.chainsMap_f_single, h]

theorem groupHomology_δ_natural_changeGroup : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)) (hX : X.ShortExact) (hY : Y.ShortExact) (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, groupHomology.δ hX (n + 1) n rfl ≫ groupHomology.map φ u₁ n = groupHomology.map φ u₃ (n + 1) ≫ groupHomology.δ hY (n + 1) n rfl ∧ hMap X.f n ≫ groupHomology.map φ u₂ n = groupHomology.map φ u₁ n ≫ hMap Y.f n ∧ hMap X.g n ≫ groupHomology.map φ u₃ n = groupHomology.map φ u₂ n ≫ hMap Y.g n := by
  intro k G H _ _ _ φ X Y hX hY u₁ u₂ u₃ h₁ h₂ n
  have c₁ := groupHomology_chainsMap_comp_comm_of_compat k G H φ _ _ _ _ X.f Y.f u₁ u₂ h₁
  have c₂ := groupHomology_chainsMap_comp_comm_of_compat k G H φ _ _ _ _ X.g Y.g u₂ u₃ h₂
  have d₁ := congrArg (fun f => HomologicalComplex.homologyMap f n) c₁
  have d₂ := congrArg (fun f => HomologicalComplex.homologyMap f n) c₂
  simp only [HomologicalComplex.homologyMap_comp] at d₁ d₂
  refine ⟨?_, d₁, d₂⟩
  let Φ : X.map (groupHomology.chainsFunctor k H) ⟶ Y.map (groupHomology.chainsFunctor k G) :=
    { τ₁ := groupHomology.chainsMap φ u₁
      τ₂ := groupHomology.chainsMap φ u₂
      τ₃ := groupHomology.chainsMap φ u₃
      comm₁₂ := c₁.symm
      comm₂₃ := c₂.symm }
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (groupHomology.map_chainsFunctor_shortExact hX) (groupHomology.map_chainsFunctor_shortExact hY)
    (n + 1) n rfl

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.groupHomology_longExact_maps_natural_of_res : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)) (hX : X.ShortExact) (hY : Y.ShortExact) (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, groupHomology.δ hX (n + 1) n rfl ≫ groupHomology.map φ u₁ n = groupHomology.map φ u₃ (n + 1) ≫ groupHomology.δ hY (n + 1) n rfl ∧ hMap X.f n ≫ groupHomology.map φ u₂ n = groupHomology.map φ u₁ n ≫ hMap Y.f n ∧ hMap X.g n ≫ groupHomology.map φ u₃ n = groupHomology.map φ u₂ n ≫ hMap Y.g n := by
  first
  | exact @GlobalTheory.HomStab.groupHomology_δ_natural_changeGroup
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqChainCycleBoundedByCone
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

theorem cone_cycle_isBoundary : ∀ (V : Type) (F G : Set (List V)) (x : V), (∀ l ∈ G, x :: l ∈ F) →
    ∀ (p : ℕ), ∀ c ∈ chains G p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c := by
  classical
  intro V F G x hx p c hc hbd
  let cone : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) := Finsupp.lmapDomain ℤ ℤ (fun l : List V => x :: l)
  have hcone : ∀ l : List V, cone (Finsupp.single l 1) = Finsupp.single (x :: l) 1 := by
    intro l
    simp [cone, Finsupp.mapDomain_single]
  have hs : ∀ l : List V, bd V (cone (Finsupp.single l 1)) =
      Finsupp.single l 1 - cone (bd V (Finsupp.single l 1)) := by
    intro l
    rw [hcone]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [bd, Finsupp.linearCombination_single, one_smul, List.length_cons,
      Finset.sum_range_succ', List.eraseIdx_cons_succ, List.eraseIdx_cons_zero, pow_zero,
      map_sum, map_zsmul, hcone, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    abel
  have key : ∀ d : List V →₀ ℤ, bd V (cone d) = d - cone (bd V d) := by
    intro d
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _), hf, hg, map_add (f := _), map_add (f := _)]
      abel
    | single l n =>
      rw [← Finsupp.smul_single_one]
      simp only [map_zsmul, hs, smul_sub]
  refine ⟨cone c, ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    have hl' := Finsupp.mapDomain_support hl
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hl'
    have hm' := (Finsupp.mem_supported _ _).mp hc hm
    exact ⟨hx m hm'.1, by simp [hm'.2]⟩
  · rw [key, hbd, map_zero, sub_zero]

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_cycle_bounded_by_cone : ∀ (V : Type) (F G : Set (List V)) (x : V), (∀ l ∈ G, x :: l ∈ F) → ∀ (p : ℕ), ∀ c ∈ chains G p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c := by
  first
  | exact @GlobalTheory.cone_cycle_isBoundary
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedSplitSeqAndUniSeqWithMemIff
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

theorem mem_splitSeq_iff_pairwise (R : Type) [CommRing R] (n : ℕ) (l : List ((Fin n → R) × (Fin n → R))) :
    l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧
      l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0 := by
  simp only [splitSeq, Set.mem_setOf_eq, List.pairwise_iff_get]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.get_of_mem hy
      simpa using h i i
    · simpa [hij.ne] using h i j
    · simpa [hij.ne'] using h j i
  · rintro ⟨h1, h2⟩ i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_neg hij.ne]
      exact (h2 i j hij).1
    · rw [if_pos rfl]
      exact h1 _ (List.get_mem _ _)
    · rw [if_neg hij.ne']
      exact (h2 j i hij).2

theorem splitSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (splitSeq R n) := by
  intro l hl l' hs
  rw [mem_splitSeq_iff_pairwise] at hl ⊢
  exact ⟨fun y hy => hl.1 y (hs.subset hy), hl.2.sublist hs⟩

theorem mem_uniSeq_iff_exists_split (R : Type) [CommRing R] (n : ℕ) (w : List (Fin n → R)) :
    w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨List.ofFn fun i => (w.get i, f i), ?_, ?_⟩
    · intro i j
      have hi : (i : ℕ) < w.length := by simpa using i.2
      have hj : (j : ℕ) < w.length := by simpa using j.2
      have := hf ⟨i, hi⟩ ⟨j, hj⟩
      simp only [List.get_eq_getElem, List.getElem_ofFn] at this ⊢
      simpa [Fin.ext_iff] using this
    · simp [List.map_ofFn]
      exact List.ofFn_get w
  · rintro ⟨l, hl, rfl⟩
    refine ⟨fun i => (l.get ⟨i, by simpa using i.2⟩).2, fun i j => ?_⟩
    have := hl ⟨i, by simpa using i.2⟩ ⟨j, by simpa using j.2⟩
    simp only [List.get_eq_getElem, List.getElem_map] at this ⊢
    simpa [Fin.ext_iff] using this

theorem uniSeq_sublist_closed (R : Type) [CommRing R] (n : ℕ) : SubClosed (uniSeq R n) := by
  intro w hw w' hs
  rw [mem_uniSeq_iff_exists_split] at hw ⊢
  obtain ⟨l, hl, rfl⟩ := hw
  obtain ⟨l', hl', rfl⟩ := List.sublist_map_iff.mp hs
  exact ⟨l', splitSeq_sublist_closed R n l hl l' hl', rfl⟩

end GlobalTheory.SeqCx

theorem GlobalTheory.SeqCx.split_uni_closed : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) :=
  fun R _ n => ⟨splitSeq_sublist_closed R n, uniSeq_sublist_closed R n, mem_splitSeq_iff_pairwise R n, mem_uniSeq_iff_exists_split R n⟩

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.subClosed_splitSeq_and_uniSeq_with_mem_iff : ∀ (R : Type) [CommRing R] (n : ℕ), SubClosed (splitSeq R n) ∧ SubClosed (uniSeq R n) ∧ (∀ l : List ((Fin n → R) × (Fin n → R)), l ∈ splitSeq R n ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise fun y z => y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0) ∧ (∀ w : List (Fin n → R), w ∈ uniSeq R n ↔ ∃ l ∈ splitSeq R n, l.map Prod.fst = w) := by
  exact @GlobalTheory.SeqCx.split_uni_closed
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsSplitSeqLinkInOrthogonalEqLinkIn
open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx.RowLink

variable {R : Type} [CommRing R] {N : ℕ}

def Orth (y z : (Fin N → R) × (Fin N → R)) : Prop := y.2 ⬝ᵥ z.1 = 0 ∧ z.2 ⬝ᵥ y.1 = 0

theorem mem_splitSeq_iff (l : List ((Fin N → R) × (Fin N → R))) :
    l ∈ splitSeq R N ↔ (∀ y ∈ l, y.2 ⬝ᵥ y.1 = 1) ∧ l.Pairwise Orth := by
  simp only [splitSeq, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, List.pairwise_iff_get.mpr fun i j hij => ⟨?_, ?_⟩⟩
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
      simpa using h i i
    · simpa [Fin.ne_of_lt hij] using h i j
    · simpa [(Fin.ne_of_lt hij).symm] using h j i
  · rintro ⟨h1, h2⟩ i j
    have hp := List.pairwise_iff_get.mp h2
    rcases lt_trichotomy i j with hij | rfl | hij
    · simpa [Fin.ne_of_lt hij] using (hp i j hij).1
    · simpa using h1 _ (List.get_mem l i)
    · simpa [(Fin.ne_of_lt hij).symm] using (hp j i hij).2

theorem append_mem_splitSeq_iff (l₁ l₂ : List ((Fin N → R) × (Fin N → R))) :
    l₁ ++ l₂ ∈ splitSeq R N ↔
      l₁ ∈ splitSeq R N ∧ l₂ ∈ splitSeq R N ∧ ∀ a ∈ l₁, ∀ b ∈ l₂, Orth a b := by
  rw [mem_splitSeq_iff, mem_splitSeq_iff, mem_splitSeq_iff, List.pairwise_append]
  constructor
  · rintro ⟨h1, p1, p2, p3⟩
    exact ⟨⟨fun y hy => h1 y (List.mem_append.mpr (Or.inl hy)), p1⟩,
      ⟨fun y hy => h1 y (List.mem_append.mpr (Or.inr hy)), p2⟩, p3⟩
  · rintro ⟨⟨h1, p1⟩, ⟨h2, p2⟩, p3⟩
    exact ⟨fun y hy => (List.mem_append.mp hy).elim (h1 y) (h2 y), p1, p2, p3⟩

def corr (γ : List ((Fin N → R) × (Fin N → R))) (v : Fin N → R) : Fin N → R :=
  v - ∑ i : Fin γ.length, ((γ.get i).2 ⬝ᵥ v) • (γ.get i).1

theorem dot_corr_of_orth (γ : List ((Fin N → R) × (Fin N → R))) (u v : Fin N → R)
    (hu : ∀ z ∈ γ, u ⬝ᵥ z.1 = 0) : u ⬝ᵥ corr γ v = u ⬝ᵥ v := by
  unfold corr
  rw [dotProduct_sub, dotProduct_sum, Finset.sum_eq_zero, sub_zero]
  intro i _
  rw [dotProduct_smul, hu _ (List.get_mem γ i), smul_zero]

theorem form_dot_corr (γ : List ((Fin N → R) × (Fin N → R))) (hγ : γ ∈ splitSeq R N)
    (z : (Fin N → R) × (Fin N → R)) (hz : z ∈ γ) (v : Fin N → R) : z.2 ⬝ᵥ corr γ v = 0 := by
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hz
  have h : ∀ i j : Fin γ.length, (γ.get i).2 ⬝ᵥ (γ.get j).1 = if i = j then 1 else 0 := hγ
  unfold corr
  rw [dotProduct_sub, dotProduct_sum]
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin γ.length)),
      (γ.get k).2 ⬝ᵥ (((γ.get i).2 ⬝ᵥ v) • (γ.get i).1) =
        if k = i then (γ.get i).2 ⬝ᵥ v else 0 := by
    intro i _
    rw [dotProduct_smul, h k i, smul_eq_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hs, Finset.sum_ite_eq Finset.univ k, if_pos (Finset.mem_univ _),
    sub_self]

end GlobalTheory.SeqCx.RowLink

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.exists_splitSeq_linkIn_orthogonal_eq_linkIn : ∀ (R : Type) [CommRing R] (N : ℕ) (γ σ : List ((Fin N → R) × (Fin N → R))), γ ∈ splitSeq R N → σ ∈ splitSeq R N → (∀ y ∈ σ, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0) → ∃ ρ ∈ splitSeq R N, ρ.length = γ.length + σ.length ∧ linkIn {x | x ∈ splitSeq R N ∧ ∀ y ∈ x, ∀ z ∈ γ, y.2 ⬝ᵥ z.1 = 0} {y | ∀ z ∈ γ, z.2 ⬝ᵥ y.1 = 0} σ = linkIn (splitSeq R N) Set.univ ρ := by
  intro R _ N γ σ hγ hσ hσγ
  obtain ⟨σ', hσ'eq⟩ : ∃ s, s = σ.map (fun y => (GlobalTheory.SeqCx.RowLink.corr γ y.1, y.2)) := ⟨_, rfl⟩
  have hc : ∀ y ∈ σ, ∀ v, y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ v = y.2 ⬝ᵥ v :=
    fun y hy v => GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ y.2 v (hσγ y hy)
  have hσ's : σ' ∈ splitSeq R N := by
    rw [GlobalTheory.SeqCx.RowLink.mem_splitSeq_iff] at hσ ⊢
    rw [hσ'eq]
    refine ⟨?_, ?_⟩
    · intro y' hy'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
      show y.2 ⬝ᵥ GlobalTheory.SeqCx.RowLink.corr γ y.1 = 1
      rw [hc y hy]
      exact hσ.1 y hy
    · rw [List.pairwise_map]
      refine hσ.2.imp_of_mem ?_
      intro a b ha hb hab
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at hab ⊢
      exact ⟨(hc a ha b.1).trans hab.1, (hc b hb a.1).trans hab.2⟩
  have horth : ∀ a ∈ γ, ∀ b ∈ σ', GlobalTheory.SeqCx.RowLink.Orth a b := by
    intro a ha b hb
    rw [hσ'eq] at hb
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    simp only [GlobalTheory.SeqCx.RowLink.Orth]
    exact ⟨GlobalTheory.SeqCx.RowLink.form_dot_corr γ hγ a ha y.1, hσγ y hy a ha⟩
  have hρ : γ ++ σ' ∈ splitSeq R N :=
    (GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff γ σ').mpr ⟨hγ, hσ's, horth⟩
  refine ⟨γ ++ σ', hρ, by rw [List.length_append, hσ'eq, List.length_map], ?_⟩
  ext w
  simp only [linkIn, Set.mem_setOf_eq, Set.mem_univ, implies_true, true_and, List.append_assoc,
    GlobalTheory.SeqCx.RowLink.append_mem_splitSeq_iff, List.mem_append]
  constructor
  · rintro ⟨hS, ⟨-, hw, hσw⟩, hz⟩
    refine ⟨hγ, ⟨hσ's, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      rw [hσ'eq] at ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      have h1 := hσw y hy b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 y.1 (hz b (Or.inr hb))).trans h1.2⟩
    · intro a ha b hb
      rcases hb with hb | hb
      · exact horth a ha b hb
      · simp only [GlobalTheory.SeqCx.RowLink.Orth]
        exact ⟨hS b hb a ha, hz b (Or.inr hb) a ha⟩
  · rintro ⟨-, ⟨-, hw, hσ'w⟩, hγx⟩
    refine ⟨fun x hx z hz => And.left (hγx z hz x (Or.inr hx)), ⟨hσ, hw, ?_⟩, ?_⟩
    · intro a ha b hb
      have hbγ : ∀ z ∈ γ, b.2 ⬝ᵥ z.1 = 0 := fun z hz => And.right (hγx z hz b (Or.inr hb))
      have h1 := hσ'w (GlobalTheory.SeqCx.RowLink.corr γ a.1, a.2)
        (by rw [hσ'eq]; exact List.mem_map.mpr ⟨a, ha, rfl⟩) b hb
      simp only [GlobalTheory.SeqCx.RowLink.Orth] at h1 ⊢
      exact ⟨h1.1, (GlobalTheory.SeqCx.RowLink.dot_corr_of_orth γ b.2 a.1 hbγ).symm.trans h1.2⟩
    · intro y hy z hz
      rcases hy with hy | hy
      · exact hσγ y hy z hz
      · exact And.right (hγx z hz y (Or.inr hy))

end
end
