module

public import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafQCQSInductPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf
  LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafQCQSInductPf

def Cov (X : Scheme.{0}) (L : List X.Opens) : Prop :=
  (∀ u ∈ L, IsAffineOpen u) ∧ ∀ x : X, ∃ u ∈ L, x ∈ u

lemma sep_of {X Y : Scheme.{0}} (g : Y ⟶ X) [IsOpenImmersion g] [X.IsSeparated] : Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from g]; infer_instance⟩

lemma fp_res {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (hf : FP f) (W : X.Opens)
    (hW : IsCompact (W : Set X)) : FP (W.ι ≫ f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, ?_, inferInstance⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp hW
  exact quasiCompact_of_compactSpace _

lemma cov_pull {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) :
    Cov W.toScheme (L.map (W.ι ⁻¹ᵁ ·)) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    exact (hA u hu).preimage_of_isOpenImmersion W.ι (by simpa using hle u hu)
  · intro x
    obtain ⟨u, hu, hx⟩ := hc (W.ι x) (by
      have := Set.mem_range_self (f := W.ι) x
      rwa [Scheme.Opens.range_ι] at this)
    exact ⟨_, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hx⟩

lemma exists_list {X : Scheme.{0}} (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ L : List X.Opens, (∀ u ∈ L, IsAffineOpen u) ∧ (∀ u ∈ L, u ≤ W) ∧ ∀ x ∈ W, ∃ u ∈ L, x ∈ u := by
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hW
  refine ⟨hs.toFinset.toList.map (fun a : X.affineOpens => a.1), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hu
    exact a.prop
  · intro u hu
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
    rw [e]
    exact le_iSup₂ (f := fun (i : X.affineOpens) (_ : i ∈ s) => (i : X.Opens)) a (by simpa using ha)
  · intro x hx
    rw [e] at hx
    simp only [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, List.mem_map.mpr ⟨a, by simpa using ha, rfl⟩, hxa⟩

lemma compact_of_cover {X : Scheme.{0}} (W : X.Opens) (L : List X.Opens) (hA : ∀ u ∈ L, IsAffineOpen u)
    (hle : ∀ u ∈ L, u ≤ W) (hc : ∀ x ∈ W, ∃ u ∈ L, x ∈ u) : IsCompact (W : Set X) := by
  have : (W : Set X) = ⋃ u ∈ L, (u : Set X) := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun hx => let ⟨u, hu, h⟩ := hc x hx; ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => hle u hu h⟩
  rw [this]
  exact L.finite_toSet.isCompact_biUnion fun u hu => (hA u hu).isCompact

lemma mem_V {X : Scheme.{0}} (L : List X.Opens) (x : X) :
    x ∈ (⨆ u ∈ L, u : X.Opens) ↔ ∃ u ∈ L, x ∈ u := by
  simp

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma glue_step {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (U : X.Opens) (L' : List X.Opens)
    (hc : Cov X (U :: L'))
    (hV : Cov (⨆ u ∈ L', u : X.Opens).toScheme
        (L'.map ((⨆ u ∈ L', u : X.Opens).ι ⁻¹ᵁ ·)) → P ((⨆ u ∈ L', u : X.Opens).ι ≫ f))
    (hW : P ((U ⊓ ⨆ u ∈ L', u : X.Opens).ι ≫ f)) :
    P f := by
  have hU : IsAffineOpen U := hc.1 U (by simp)
  have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
  have hUV : U ⊔ (⨆ u ∈ L', u : X.Opens) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨u, hu, hx⟩ := hc.2 x
    rcases List.mem_cons.mp hu with rfl | hu
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inl hx)
    · exact TopologicalSpace.Opens.mem_sup.mpr (Or.inr ((mem_V L' x).mpr ⟨u, hu, hx⟩))
  refine hG f hf U _ hUV ?_ ?_ ?_
  · haveI : IsAffine U := hU
    exact hA _ inferInstance (fp_res f hf U hU.isCompact)
  · refine hV (cov_pull _ L' hL' (fun u hu => ?_) (fun x hx => (mem_V L' x).mp hx))
    exact le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu
  · exact hW

end

section
variable {S : Scheme.{0}} [IsAffine S] (P : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop)
  (hA : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsAffine X → FP f → P f)
  (hG : ∀ {X : Scheme.{0}} (f : X ⟶ S), FP f → ∀ (U V : X.Opens), U ⊔ V = ⊤ →
      P (U.ι ≫ f) → P (V.ι ≫ f) → P ((U ⊓ V).ι ≫ f) → P f)
include hA hG

lemma empty_case {X : Scheme.{0}} (f : X ⟶ S) (hf : FP f) (hc : Cov X []) : P f := by
  have : IsEmpty X := ⟨fun x => by obtain ⟨u, hu, _⟩ := hc.2 x; simp at hu⟩
  exact hA f inferInstance hf

lemma stepA : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    X.IsSeparated → Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf _ hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hs hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      have : (⨆ u ∈ L', u : X.Opens).toScheme.IsSeparated := sep_of (⨆ u ∈ L', u : X.Opens).ι
      refine ih _ _ (by simp [hl]) (fp_res f hf _ ?_) this hcV
      exact compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have hA' : ∀ v ∈ L'.map (U ⊓ ·), IsAffineOpen v := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact hU.inf (hL' u hu)
      have hle : ∀ v ∈ L'.map (U ⊓ ·), v ≤ W := by
        intro v hv
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact inf_le_inf_left U (le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
      have hcW : ∀ x ∈ W, ∃ v ∈ L'.map (U ⊓ ·), x ∈ v := by
        intro x hx
        obtain ⟨hxU, hxV⟩ := hx
        obtain ⟨u, hu, h⟩ := (mem_V L' x).mp hxV
        exact ⟨U ⊓ u, List.mem_map.mpr ⟨u, hu, rfl⟩, ⟨hxU, h⟩⟩
      have : W.toScheme.IsSeparated := sep_of W.ι
      exact ih _ ((L'.map (U ⊓ ·)).map (W.ι ⁻¹ᵁ ·)) (by simp [hl])
        (fp_res f hf W (compact_of_cover W _ hA' hle hcW)) this (cov_pull W _ hA' hle hcW)

lemma stepB : ∀ (n : ℕ) {X : Scheme.{0}} (f : X ⟶ S) (L : List X.Opens), L.length = n → FP f →
    Cov X L → P f := by
  intro n
  induction n with
  | zero =>
    intro X f L hl hf hc
    rw [List.eq_nil_of_length_eq_zero hl] at hc
    exact empty_case P hA hG f hf hc
  | succ n ih =>
    intro X f L hl hf hc
    obtain ⟨U, L', rfl⟩ : ∃ U L', L = U :: L' := by
      cases L with
      | nil => simp at hl
      | cons U L' => exact ⟨U, L', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    have hU : IsAffineOpen U := hc.1 U (by simp)
    have hL' : ∀ u ∈ L', IsAffineOpen u := fun u hu => hc.1 u (by simp [hu])
    have hVc : IsCompact ((⨆ u ∈ L', u : X.Opens) : Set X) :=
      compact_of_cover _ L' hL' (fun u hu => le_iSup₂ (f := fun u (_ : u ∈ L') => u) u hu)
        (fun x hx => (mem_V L' x).mp hx)
    refine glue_step P hA hG f hf U L' hc ?_ ?_
    · intro hcV
      exact ih _ _ (by simp [hl]) (fp_res f hf _ hVc) hcV
    · set W : X.Opens := U ⊓ ⨆ u ∈ L', u
      have : QuasiSeparated f := hf.2.2
      have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      have hWc : IsCompact (W : Set X) :=
        QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU.isCompact (⨆ u ∈ L', u : X.Opens).2 hVc
      obtain ⟨L2, h1, h2, h3⟩ := exists_list W hWc
      haveI : IsAffine U := hU
      have : W.toScheme.IsSeparated := sep_of (X.homOfLE (inf_le_left : W ≤ U))
      exact stepA P hA hG _ (W.ι ≫ f) (L2.map (W.ι ⁻¹ᵁ ·)) rfl (fp_res f hf W hWc) this
        (cov_pull W L2 h1 h2 h3)

end

theorem LeafQCQSInduct_of : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := by
  intro S _ P hA hG X f hf
  have : QuasiCompact f := hf.2.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨L, h1, -, h3⟩ := exists_list (⊤ : X.Opens) (by simpa using isCompact_univ)
  exact stepB P hA hG _ f L rfl hf ⟨h1, fun x => h3 x trivial⟩

end LateralTheory.E.LeafQCQSInductPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GluedCurveChartOverlapIsPullback
section -- merged from Development.EtaleCohomology.EtaleSheaves.SpecSubalgebraPullbackLiftIsClosedImmersion
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafSpecGenClosed
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

set_option backward.isDefEq.respectTransparency false in
theorem sep_of_cover {X S : Scheme.{0}} (f : X ⟶ S) (U : X.OpenCover)
    (H : ∀ i j, IsClosedImmersion (pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f
      (by simp) (by simp))) : IsSeparated f := by
  constructor
  apply IsZariskiLocalAtTarget.of_openCover (Scheme.Pullback.openCoverOfLeftRight U U f f)
  rintro ⟨i, j⟩
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv]
  have e : (pullbackDiagonalMapIdIso (U.f i) (U.f j) f).inv ≫
      (Scheme.Pullback.openCoverOfLeftRight U U f f).pullbackHom (pullback.diagonal f) (i, j) =
      pullback.map (U.f i) (U.f j) (U.f i ≫ f) (U.f j ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp only [Scheme.Cover.pullbackHom, Category.assoc, limit.lift_π,
      PullbackCone.mk_π_app, pullback.lift_fst, pullback.lift_snd, Category.comp_id]
    · exact pullbackDiagonalMapIdIso_inv_snd_fst (U.f i) (U.f j) f
    · exact pullbackDiagonalMapIdIso_inv_snd_snd (U.f i) (U.f j) f
  rw [e]; exact H i j

theorem closed_of_pb {X S W P Q : Scheme.{0}} (f : X ⟶ S) (ia : P ⟶ X) (ib : Q ⟶ X) (pa : W ⟶ P)
    (pb : W ⟶ Q) (hp : IsPullback pa pb ia ib) (ga : P ⟶ S) (gb : Q ⟶ S) (hga : ia ≫ f = ga)
    (hgb : ib ≫ f = gb) (w : pa ≫ ga = pb ≫ gb)
    (hc : IsClosedImmersion (pullback.lift pa pb w)) :
    IsClosedImmersion (pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp)) := by
  subst hga hgb
  have e : pullback.map ia ib (ia ≫ f) (ib ≫ f) (𝟙 _) (𝟙 _) f (by simp) (by simp) =
      hp.isoPullback.inv ≫ pullback.lift pa pb w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_inv_snd]
  rw [e]; infer_instance

def LeafGluePullback : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsPullback (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)).toRingHom))
    G.iA G.iB

theorem spec_w {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L) (hA : A ≤ D) (hB : B ≤ D) :
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hA).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω A)) =
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hB).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]; congr 1

def LeafSpecGenClosed : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
  (hA : A ≤ D) (hB : B ≤ D), D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) →
  IsClosedImmersion (pullback.lift _ _ (spec_w A B D hA hB))

theorem dr_le {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L) (hu : u⁻¹ ∈ B) :
    Dr Ω A u ≤ Algebra.adjoin Ω ((A : Set L) ∪ B) :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr hu))

theorem LeafGlueSep_of (hP : LeafGluePullback) (hC : LeafSpecGenClosed) :
    LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hD := dr_le A B u h.2.2.1
  apply sep_of_cover G.c0 (LateralTheory.E.LeafGlueIsProperPf.cov G)
  intro i j
  cases i <;> cases j
  · exact closed_of_pb G.c0 G.iB G.iB (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iB) _ _ G.hcB G.hcB (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω B))))))
  · exact closed_of_pb G.c0 G.iB G.iA _ _ (hP Ω L A B u h G).flip _ _ G.hcB G.hcA _
      (hC Ω L B A _ _ _ (by rw [Set.union_comm]; exact hD))
  · exact closed_of_pb G.c0 G.iA G.iB _ _ (hP Ω L A B u h G) _ _ G.hcA G.hcB _ (hC Ω L A B _ _ _ hD)
  · exact closed_of_pb G.c0 G.iA G.iA (𝟙 _) (𝟙 _) (IsKernelPair.id_of_mono G.iA) _ _ G.hcA G.hcA (by simp)
      (by exact (inferInstance : IsClosedImmersion (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap Ω A))))))

end LateralTheory.E.GluedCurveChartOverlaps
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem prod_surj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (A B D : Subalgebra Ω L)
    (hA : A ≤ D) (hB : B ≤ D) (hD : D ≤ Algebra.adjoin Ω ((A : Set L) ∪ B)) :
    Function.Surjective (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) := by
  intro x
  have hx : (x : L) ∈ (Algebra.TensorProduct.productMap A.val B.val).range := by
    rw [Algebra.TensorProduct.productMap_range, A.range_val, B.range_val]
    have := hD x.2
    rwa [Algebra.adjoin_union, Algebra.adjoin_eq, Algebra.adjoin_eq] at this
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  rw [← hy]
  have e : D.val.comp (Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)) =
      Algebra.TensorProduct.productMap A.val B.val := by
    ext <;> rfl
  exact congrArg (fun φ : _ →ₐ[Ω] L => φ y) e

theorem spec_subalgebra_pullback_lift_is_closed_immersion : LeafSpecGenClosed := by
  intro Ω L _ _ _ A B D hA hB hD
  let φ := Algebra.TensorProduct.productMap (Subalgebra.inclusion hA) (Subalgebra.inclusion hB)
  have e : pullback.lift _ _ (spec_w A B D hA hB) =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pullbackSpecIso Ω A B).inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
    · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext a; simp [φ]
  rw [e]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (prod_surj A B D hA hB hD)
  infer_instance

end LateralTheory.E.GluedCurveChartOverlaps
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.GluedCurveChartOverlaps

theorem mem_adj {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B : Subalgebra Ω L) (u : L) (hu : u ≠ 0)
    (huB : u⁻¹ ∈ B) (d : L) (hd : d ∈ Algebra.adjoin Ω ((B : Set L) ∪ {u})) : ∃ n : ℕ, d * u⁻¹ ^ n ∈ B := by
  induction hd using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hu]; exact B.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * u⁻¹ ^ m + (y * u⁻¹ ^ m) * u⁻¹ ^ n := by ring
    rw [this]
    exact B.add_mem (B.mul_mem hn (B.pow_mem huB _)) (B.mul_mem hm (B.pow_mem huB _))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx; obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x * y) * u⁻¹ ^ (n + m) = (x * u⁻¹ ^ n) * (y * u⁻¹ ^ m) := by ring
    rw [this]; exact B.mul_mem hn hm

theorem away {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] (B D : Subalgebra Ω L) (hB : B ≤ D) (u : L)
    (hu : u ≠ 0) (huB : u⁻¹ ∈ B) (huD : u ∈ D) (hD : D ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u})) :
    letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
    IsLocalization.Away (⟨u⁻¹, huB⟩ : B) D := by
  letI : Algebra B D := (Subalgebra.inclusion hB).toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, n, rfl⟩
    show IsUnit (algebraMap B D ((⟨u⁻¹, huB⟩ : B) ^ n))
    rw [map_pow]
    refine IsUnit.pow n ?_
    exact ⟨⟨algebraMap B D ⟨u⁻¹, huB⟩, ⟨u, huD⟩, Subtype.ext (inv_mul_cancel₀ hu),
      Subtype.ext (mul_inv_cancel₀ hu)⟩, rfl⟩
  · intro d
    obtain ⟨n, hn⟩ := mem_adj B u hu huB d (hD d.2)
    refine ⟨(⟨d * u⁻¹ ^ n, hn⟩, ⟨_, n, rfl⟩), Subtype.ext ?_⟩
    show d * u⁻¹ ^ n = (d : L) * (u⁻¹ ^ n)
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    have : (x : L) = (y : L) := by
      have h2 := congrArg (fun z : D => (z : L)) hxy
      exact h2
    simp [Subtype.ext this]

set_option backward.isDefEq.respectTransparency false in
theorem glued_curve_chart_overlap_is_pullback : LeafGluePullback := by
  intro Ω L _ _ _ A B u h G
  haveI := G.hiA; haveI := G.hiB
  have hadj := h.2.2.2.2.2.2.2.2.2.2.2.1
  have huD : u ∈ Dr Ω A u := Algebra.subset_adjoin (Or.inl h.2.1)
  have hD : Dr Ω A u ≤ Algebra.adjoin Ω ((B : Set L) ∪ {u}) := hadj.le
  haveI hjB : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom)) := by
    letI : Algebra B (Dr Ω A u) := (Subalgebra.inclusion (le_Dr_B A B u hadj)).toRingHom.toAlgebra
    haveI := away B (Dr Ω A u) (le_Dr_B A B u hadj) u h.1 h.2.2.1 huD hD
    exact IsOpenImmersion.of_isLocalization (S := Dr Ω A u) (⟨u⁻¹, h.2.2.1⟩ : B)
  refine IsOpenImmersion.isPullback _ _ _ _ G.agree.symm ?_
  ext x
  show G.iB.base x ∈ Set.range G.iA.base ↔ x ∈ Set.range _
  constructor
  · intro hx
    have hx' : G.iB.base x ∈ Set.range G.iA.base ∩ Set.range G.iB.base := ⟨hx, x, rfl⟩
    rw [G.inter, G.agree] at hx'
    obtain ⟨y, hy⟩ := hx'
    refine ⟨y, G.iB.isOpenEmbedding.injective ?_⟩
    rw [← hy]; rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (le_Dr_A A u)).toRingHom)).base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.agree]; rfl

end LateralTheory.E.GluedCurveChartOverlaps

namespace LateralTheory.E.GluedCurveSeparated

theorem LeafGlueSep_of : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep :=
  LateralTheory.E.GluedCurveChartOverlaps.LeafGlueSep_of LateralTheory.E.GluedCurveChartOverlaps.glued_curve_chart_overlap_is_pullback
    LateralTheory.E.GluedCurveChartOverlaps.spec_subalgebra_pullback_lift_is_closed_immersion

end LateralTheory.E.GluedCurveSeparated
end
end
