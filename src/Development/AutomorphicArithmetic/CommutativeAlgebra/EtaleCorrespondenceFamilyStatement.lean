module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsComparisonFamilyNatural
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamPullbackAlongSecondMapSmulIotaMultiKaehler
set_option autoImplicit false

noncomputable section

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

namespace GlobalTheory.WH.PullCoc

section Gen

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E E' : Type} [AddCommGroup E] [Module k E]
  [AddCommGroup E'] [Module k E']

end Gen

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section J2

variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K']

theorem mapDR_smul_ιMulti {L : Type} [Field L] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] (b : K) (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      algebraMap K L b • ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  rw [map_smul, algebraMap_smul]
  congr 1
  simp [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, mapDR, map1, Function.comp_def,
    KaehlerDifferential.map_D]

theorem deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD (j2 : K →ₐ[ℂ] K') (b : K) (q : ℕ) (v : Fin q → K) :
    pr2L j2 (b • ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      j2 b • ExteriorAlgebra.ιMulti K' q fun j => D ℂ K' (j2 (v j)) := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul_ιMulti (L := K') b q v

end J2

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc

namespace GlobalTheory.WH.PullCoc

section Y

variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K']
  {d : ℕ} (x : Fin (d + 1) → F)

end Y

end GlobalTheory.WH.PullCoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechIsCxOfMono
set_option autoImplicit false

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem cech_isCx_of_mono : ∀ (k : Type) [Field k] (ι : Type) [LinearOrder ι] (E : Type) [AddCommGroup E] [Module k E]
    (A : Finset ι → Submodule k E), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (cech A).IsCx := by
  intro k _ ι _ E _ _ A hA n a ha
  have ha' : ∀ s, a s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥) :=
    fun s => (Submodule.mem_pi.1 ha) s (Set.mem_univ _)
  refine ⟨?_, ?_⟩
  · show GlobalTheory.DI.delta a ∈ cechC A (n + 1)
    refine Submodule.mem_pi.2 fun t _ => ?_
    show ∑ i ∈ t, GlobalTheory.cubeSign t i • a (t.erase i) ∈ _
    split_ifs with ht
    · refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exact hA _ _ h2.1 (Finset.erase_subset _ _) h
      · rw [Submodule.mem_bot] at h; rw [h]; exact zero_mem _
    · rw [Submodule.mem_bot]
      refine Finset.sum_eq_zero fun i hi => ?_
      have h := ha' (t.erase i)
      split_ifs at h with h2
      · exfalso
        apply ht
        refine ⟨⟨i, hi⟩, ?_⟩
        have h3 := Finset.card_erase_add_one hi
        have h4 := h2.2
        omega
      · rw [Submodule.mem_bot] at h; rw [h, smul_zero]
  · exact GlobalTheory.DI.delta_delta a

end GlobalTheory.PD
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCorrespondenceFunctionFieldStatementTwo
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

open scoped TensorProduct in
open CategoryTheory.Limits in
private theorem surj_productMap {Y : Scheme.{0}} [Y.IsSeparated] {A B C : CommRingCat.{0}} (f1 : Spec A ⟶ Y) (f2 : Spec B ⟶ Y)
    (r1 : A ⟶ C) (r2 : B ⟶ C) (pb : IsPullback (Spec.map r1) (Spec.map r2) f1 f2) :
    Function.Surjective (Algebra.TensorProduct.productMap r1.hom.toIntAlgHom r2.hom.toIntAlgHom) := by
  let i : Y ⟶ Spec (.of ℤ) := specZIsTerminal.from Y
  have e1 : f1 ≫ i = Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) := specZIsTerminal.hom_ext _ _
  have e2 : f2 ≫ i = Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := specZIsTerminal.hom_ext _ _
  let φ : A ⊗[ℤ] B →+* C := (Algebra.TensorProduct.productMap r1.hom.toIntAlgHom r2.hom.toIntAlgHom).toRingHom
  let J : Spec C ⟶ Spec (.of (A ⊗[ℤ] B)) :=
    pb.isoPullback.hom ≫ pullback.mapDesc f1 f2 i ≫ (pullback.congrHom e1 e2).hom ≫ (pullbackSpecIso ℤ A B).hom
  have hJ : IsClosedImmersion J := inferInstance
  have hφ1 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := A) (B := B)) ≫ CommRingCat.ofHom φ = r1 := by
    ext a
    simp [φ]
  have hφ2 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := ℤ) (A := A) (B := B)).toRingHom ≫ CommRingCat.ofHom φ = r2 := by
    ext b
    simp [φ]
  have q1 : pullback.mapDesc f1 f2 i ≫ (pullback.congrHom e1 e2).hom ≫ pullback.fst _ _ = pullback.fst f1 f2 := by
    simp only [pullback.mapDesc, pullback.congrHom_hom, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  have q2 : pullback.mapDesc f1 f2 i ≫ (pullback.congrHom e1 e2).hom ≫ pullback.snd _ _ = pullback.snd f1 f2 := by
    simp only [pullback.mapDesc, pullback.congrHom_hom, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hJe : J = Spec.map (CommRingCat.ofHom φ) := by
    rw [← cancel_mono (pullbackSpecIso ℤ A B).inv]
    apply pullback.hom_ext
    · simp only [J, Category.assoc, Iso.hom_inv_id, Category.comp_id, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      rw [hφ1, q1, pb.isoPullback_hom_fst]
    · simp only [J, Category.assoc, Iso.hom_inv_id, Category.comp_id, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      rw [q2, pb.isoPullback_hom_snd, ← hφ2]
      rfl
  rw [hJe] at hJ
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map (CommRingCat.ofHom φ))).2
  have nat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  intro c
  obtain ⟨t, ht⟩ := hs ((Scheme.ΓSpecIso C).inv.hom c)
  refine ⟨(Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).hom.hom t, ?_⟩
  have h3 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).hom.hom t)) nat
  simp only [CommRingCat.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply] at h3
  have h4 : (Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).inv.hom ((Scheme.ΓSpecIso (.of (A ⊗[ℤ] B))).hom.hom t) = t := by
    simp
  rw [h4] at h3
  have h5 := (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso C).inv)
  exact h5 (h3.trans ht)

private theorem pb_aff {Y : Scheme.{0}} [Y.IsSeparated] {W1 W2 : Y.Opens} (h1 : IsAffineOpen W1) (h2 : IsAffineOpen W2) :
    IsPullback (Spec.map (Y.presheaf.map (homOfLE (inf_le_left : W1 ⊓ W2 ≤ W1)).op))
      (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op)) h1.fromSpec h2.fromSpec := by
  have h12 : IsAffineOpen (W1 ⊓ W2) := h1.inf h2
  have ha := h1.map_fromSpec h12 (homOfLE (inf_le_left : W1 ⊓ W2 ≤ W1)).op
  have hb := h2.map_fromSpec h12 (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op
  haveI : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op)) := by
    have : IsOpenImmersion (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op) ≫ h2.fromSpec) := by
      rw [hb]; infer_instance
    exact IsOpenImmersion.of_comp _ h2.fromSpec
  refine IsOpenImmersion.isPullback _ _ _ _ (hb.trans ha.symm) ?_
  refine TopologicalSpace.Opens.ext (Set.ext fun z => ⟨fun hz => ?_, ?_⟩)
  · have hz1 : h2.fromSpec z ∈ W1 := by
      have : h2.fromSpec z ∈ Set.range h1.fromSpec := hz
      rwa [h1.range_fromSpec] at this
    have hz2 : h2.fromSpec z ∈ W2 := by
      have : h2.fromSpec z ∈ Set.range h2.fromSpec := ⟨z, rfl⟩
      rwa [h2.range_fromSpec] at this
    have hz3 : h2.fromSpec z ∈ Set.range h12.fromSpec := by
      rw [h12.range_fromSpec]; exact ⟨hz1, hz2⟩
    obtain ⟨w, hw⟩ := hz3
    refine ⟨w, h2.fromSpec.isOpenEmbedding.injective ?_⟩
    rw [← hw, ← hb]
    rfl
  · rintro ⟨w, rfl⟩
    have : h12.fromSpec w ∈ W1 ⊓ W2 := by
      have h3 : h12.fromSpec w ∈ Set.range h12.fromSpec := ⟨w, rfl⟩
      rwa [h12.range_fromSpec] at h3
    have h4 : h2.fromSpec (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op) w) ∈ W1 := by
      have h5 : h2.fromSpec (Spec.map (Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op) w) = h12.fromSpec w := by
        rw [← hb]; rfl
      rw [h5]; exact this.1
    change h2.fromSpec _ ∈ Set.range h1.fromSpec
    rw [h1.range_fromSpec]
    exact h4

private theorem germ_res' {Y : Scheme.{0}} [IsIntegral Y] {V W : Y.Opens} (h : V ≤ W) (hV : genericPoint Y ∈ V)
    (hW : genericPoint Y ∈ W) (f : Γ(Y, W)) :
    (Y.presheaf.germ V (genericPoint Y) hV).hom ((Y.presheaf.map (homOfLE h).op).hom f) =
      (Y.presheaf.germ W (genericPoint Y) hW).hom f :=
  congrArg (fun q => q.hom f) (TopCat.Presheaf.germ_res Y.presheaf (homOfLE h) (genericPoint Y) hV)

open scoped TensorProduct in
private theorem ringOn_inf {Y : Scheme.{0}} [IsIntegral Y] [Y.IsSeparated] (p' : Y ⟶ Sp ℂ)
    [instL : Algebra ℂ Y.functionField] (hL : instL = ffAlg p') {W1 W2 : Y.Opens} (h1 : IsAffineOpen W1)
    (h2 : IsAffineOpen W2) (g1 : genericPoint Y ∈ W1) (g2 : genericPoint Y ∈ W2) (g12 : genericPoint Y ∈ W1 ⊓ W2) :
    UpperTheory.A.ringOn p' hL W1 g1 ⊔ UpperTheory.A.ringOn p' hL W2 g2 = UpperTheory.A.ringOn p' hL (W1 ⊓ W2) g12 := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rintro _ ⟨f, rfl⟩
      exact ⟨(Y.presheaf.map (homOfLE (inf_le_left : W1 ⊓ W2 ≤ W1)).op).hom f, germ_res' _ g12 g1 f⟩
    · rintro _ ⟨f, rfl⟩
      exact ⟨(Y.presheaf.map (homOfLE (inf_le_right : W1 ⊓ W2 ≤ W2)).op).hom f, germ_res' _ g12 g2 f⟩
  · rintro _ ⟨g, rfl⟩
    obtain ⟨t, rfl⟩ := surj_productMap h1.fromSpec h2.fromSpec _ _ (pb_aff h1 h2) g
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero]
      exact zero_mem _
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem ha hb
    | tmul a b =>
      rw [Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      refine mul_mem (Algebra.mem_sup_left ?_) (Algebra.mem_sup_right ?_)
      · exact ⟨a, (germ_res' _ g12 g1 a).symm⟩
      · exact ⟨b, (germ_res' _ g12 g2 b).symm⟩

private theorem mem_bot_of_int {F K : Type} [CommRing F] [Algebra ℂ F] [Field K] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] (T : Subalgebra ℂ F) (hT : T ≤ ⊥) {y : K} (hy : IsIntegral T y) : y ∈ (⊥ : Subalgebra ℂ K) := by
  haveI : Algebra.IsIntegral ℂ T := ⟨fun a => by
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 (hT a.2)
    have : a = algebraMap ℂ T c := Subtype.ext hc.symm
    rw [this]
    exact isIntegral_algebraMap⟩
  have h := isIntegral_trans (R := ℂ) (A := T) y hy
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible h)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one ℂ y hdeg
  exact Algebra.mem_bot.2 ⟨c, hc⟩

private theorem rA_empty_le {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F) : rA ℂ x ∅ ≤ ⊥ := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨i, hi, -⟩
  simp at hi

private theorem rB_empty_le {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) : rB ℂ K x ∅ ≤ ⊥ :=
  fun _ hy => mem_bot_of_int (rA ℂ x ∅) (rA_empty_le x) hy

private theorem restriction_empty_le_bot {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K') : R2 x j2 ∅ ≤ ⊥ := by
  intro y hy
  refine mem_bot_of_int (F := K') ((rB ℂ K x ∅).map j2) ?_ hy
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 (rB_empty_le x hb)
  exact Algebra.mem_bot.2 ⟨c, (j2.commutes c).symm⟩

private theorem inf_join {Z Y : Scheme.{0}} {n : ℕ} (c1 c2 : Y ⟶ Z) (U : Fin n → Z.Opens) (S : Finset (Fin n ⊕ₗ Fin n)) :
    S.inf (UpperTheory.A.joinCover c1 c2 U) =
      (lft S).inf (fun i => c1 ⁻¹ᵁ U i) ⊓ (rgt S).inf (fun i => c2 ⁻¹ᵁ U i) := by
  classical
  have ml : ∀ i, i ∈ lft S ↔ toLex (Sum.inl i) ∈ S := fun i => by
    simp [lft, Finset.mem_toLeft]
  have mr : ∀ i, i ∈ rgt S ↔ toLex (Sum.inr i) ∈ S := fun i => by
    simp [rgt, Finset.mem_toRight]
  apply le_antisymm
  · refine le_inf (Finset.le_inf fun i hi => ?_) (Finset.le_inf fun i hi => ?_)
    · exact Finset.inf_le (f := UpperTheory.A.joinCover c1 c2 U) ((ml i).1 hi)
    · exact Finset.inf_le (f := UpperTheory.A.joinCover c1 c2 U) ((mr i).1 hi)
  · refine Finset.le_inf fun k hk => ?_
    rcases h : ofLex k with j | j
    · have hk' : k = toLex (Sum.inl j) := by rw [← h]; rfl
      subst hk'
      exact inf_le_left.trans (Finset.inf_le (f := fun i => c1 ⁻¹ᵁ U i) ((ml j).2 hk))
    · have hk' : k = toLex (Sum.inr j) := by rw [← h]; rfl
      subst hk'
      exact inf_le_right.trans (Finset.inf_le (f := fun i => c2 ⁻¹ᵁ U i) ((mr j).2 hk))

private theorem blocks_nonempty {n : ℕ} {S : Finset (Fin n ⊕ₗ Fin n)} (hS : S.Nonempty) :
    (lft S).Nonempty ∨ (rgt S).Nonempty := by
  obtain ⟨k, hk⟩ := hS
  rcases h : ofLex k with j | j
  · have hk' : k = toLex (Sum.inl j) := by rw [← h]; rfl
    subst hk'
    exact Or.inl ⟨j, by simpa [lft, Finset.mem_toLeft] using hk⟩
  · have hk' : k = toLex (Sum.inr j) := by rw [← h]; rfl
    subst hk'
    exact Or.inr ⟨j, by simpa [rgt, Finset.mem_toRight] using hk⟩

theorem UpperTheory.etaleCorrespondence_functionField_statement_two :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsAffCover s' (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S)) := by

  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU
  have base := UpperTheory.A.isAffCover_join s s' c1 c2 hP hL U _ hU
  have C1 := (UpperTheory.A.isFinCover_pull h1 hK hL g1 hx hU).2
  have C2 := UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hP c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  haveI := UpperTheory.A.isSeparated_of_proj s hP
  haveI : Y.IsSeparated := UpperTheory.A.isSeparated_of_hom c1
  refine ⟨base.alg, base.affine, base.cover, base.ne, fun S hS y => ?_⟩
  have hcongr : ∀ {W W' : Y.Opens} (_ : W = W') (hW : genericPoint Y ∈ W) (hW' : genericPoint Y ∈ W'),
      UpperTheory.A.ringOn s' hL W hW = UpperTheory.A.ringOn s' hL W' hW' := by
    intro W W' e hW hW'
    subst e
    rfl
  have r1 : ∀ I : Finset (Fin (d + 1)), I.Nonempty →
      rB ℂ Y.functionField x I = UpperTheory.A.ringOn s' hL (I.inf fun i => c1 ⁻¹ᵁ U i) (C1.ne I) :=
    fun I hI => Subalgebra.ext (C1.ring I hI)
  have r2 : ∀ J : Finset (Fin (d + 1)), J.Nonempty →
      R2 x j2 J = UpperTheory.A.ringOn s' hL (J.inf fun i => c2 ⁻¹ᵁ U i) (C2.ne J) :=
    fun J hJ => Subalgebra.ext (C2.ring J hJ)
  have hinf := inf_join c1 c2 U S
  suffices h : RY x j2 (lft S) (rgt S) = UpperTheory.A.ringOn s' hL (S.inf (UpperTheory.A.joinCover c1 c2 U)) (base.ne S) by
    rw [h]
    exact Iff.rfl
  rcases (lft S).eq_empty_or_nonempty with hI | hI
  · have hJ : (rgt S).Nonempty := (blocks_nonempty hS).resolve_left (by simp [hI])
    have e : S.inf (UpperTheory.A.joinCover c1 c2 U) = (rgt S).inf fun i => c2 ⁻¹ᵁ U i := by
      rw [hinf, hI]
      simp
    rw [hcongr e _ (C2.ne _), ← r2 _ hJ, RY, hI]
    exact sup_eq_right.2 ((rB_empty_le x).trans bot_le)
  · rcases (rgt S).eq_empty_or_nonempty with hJ | hJ
    · have e : S.inf (UpperTheory.A.joinCover c1 c2 U) = (lft S).inf fun i => c1 ⁻¹ᵁ U i := by
        rw [hinf, hJ]
        simp
      rw [hcongr e _ (C1.ne _), ← r1 _ hI, RY, hJ]
      exact sup_eq_left.2 ((restriction_empty_le_bot x j2).trans bot_le)
    · rw [hcongr hinf _ (by rw [← hinf]; exact base.ne S), RY, r1 _ hI, r2 _ hJ]
      exact ringOn_inf s' hL (C1.affine _ hI) (C2.affine _ hJ) _ _ _
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

set_option autoImplicit false

section Alg

variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]

private theorem left_union (I : Finset ι) (J : Finset κ) : lft (uni I J) = I := by
  ext i; simp [lft, uni]

private theorem right_union (I : Finset ι) (J : Finset κ) : rgt (uni I J) = J := by
  ext i; simp [rgt, uni]

private theorem uni_lr (s : Finset (ι ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  unfold uni lft rgt
  rw [Finset.toLeft_disjSum_toRight, Finset.map_map]
  ext t; simp

private theorem card_uni_commutative_algebra (I : Finset ι) (J : Finset κ) : (uni I J).card = I.card + J.card := by
  simp [uni]

private def tr (ι : Type) {κ : Type} (j : κ) : ι ⊕ₗ κ := toLex (Sum.inr j)

private def tl {ι : Type} (κ : Type) (i : ι) : ι ⊕ₗ κ := toLex (Sum.inl i)

private theorem tr_mono : StrictMono (tr ι : κ → ι ⊕ₗ κ) := by
  intro a b h
  simp [tr, h]

private theorem tl_mono : StrictMono (tl κ : ι → ι ⊕ₗ κ) := by
  intro a b h
  simp [tl, h]

private theorem image_tr (J : Finset κ) : J.image (tr ι) = uni (∅ : Finset ι) J := by
  ext x
  simp only [tr, uni, Finset.mem_image, Finset.mem_map, Finset.empty_disjSum]
  simp

private theorem image_tl (I : Finset ι) : I.image (tl κ) = uni I (∅ : Finset κ) := by
  ext x
  simp only [tl, uni, Finset.mem_image, Finset.mem_map, Finset.disjSum_empty]
  simp

variable {E E' : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

private theorem pullC_mono {τ : κ → ι} (h : StrictMono τ) (φ : E →ₗ[ℂ] E') (c : Finset ι → E) (s : Finset κ) :
    pullC τ φ c s = φ (c (s.image τ)) := by
  have hinj : Set.InjOn τ (s : Set κ) := h.injective.injOn
  have hsign : sortSign τ s = 1 := by
    unfold sortSign
    refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
    rw [if_neg]
    rintro ⟨hab, hba⟩
    exact lt_asymm (h hab) hba
  simp [pullC, hinj, hsign]

private theorem pull_tr (c : Finset (ι ⊕ₗ κ) → E) (J : Finset κ) :
    pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) c J = c (uni ∅ J) := by
  rw [pullC_mono tr_mono]
  exact congrArg c (image_tr J)

private theorem pull_tl (c : Finset (ι ⊕ₗ κ) → E) (I : Finset ι) :
    pullC (tl κ) (LinearMap.id : E →ₗ[ℂ] E) c I = c (uni I ∅) := by
  rw [pullC_mono tl_mono]
  exact congrArg c (image_tl I)

private theorem lift_cocycle (A : Finset (ι ⊕ₗ κ) → Submodule ℂ E) (A' : Finset κ → Submodule ℂ E)
    (hcx : (cech A).IsCx) (hA : ∀ J : Finset κ, J.Nonempty → A' J ≤ A (uni ∅ J)) (p : ℤ)
    (c0 : (cech A).Z p) (b : Finset κ → E)
    (h : pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) c0.1 - b ∈ (cech A').B p) :
    ∃ c : (cech A).Z p, (∀ J, c.1 (uni ∅ J) = b J) ∧
      (Submodule.Quotient.mk c : (cech A).H p) = Submodule.Quotient.mk c0 := by
  classical
  have hB : pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) c0.1 - b ∈ Submodule.map (deltaL ℂ κ E) (cechC A' (p - 1)) := h
  obtain ⟨e, he, hde⟩ := Submodule.mem_map.1 hB
  rw [UpperTheory.PullbackConnectingMap.mem_cechC] at he
  let et : Finset (ι ⊕ₗ κ) → E := fun s => if lft s = ∅ then e (rgt s) else 0
  have hpe : pullC (tr ι) (LinearMap.id : E →ₗ[ℂ] E) et = e := by
    funext J
    rw [pull_tr]
    simp [et, left_union, right_union]
  have hetC : et ∈ cechC A (p - 1) := by
    rw [UpperTheory.PullbackConnectingMap.mem_cechC]
    intro s
    by_cases hl : lft s = ∅
    · have hs : uni ∅ (rgt s) = s := by
        rw [← hl]
        exact uni_lr s
      have hcard : s.card = (rgt s).card := by
        have := card_uni_commutative_algebra (∅ : Finset ι) (rgt s)
        rw [hs] at this
        simpa using this
      have hne : s.Nonempty ↔ (rgt s).Nonempty := by
        rw [← Finset.card_pos, ← Finset.card_pos, hcard]
      simp only [et, hl, if_true]
      constructor
      · rintro ⟨hsn, hsc⟩
        have hrn := hne.1 hsn
        have hmem := (he (rgt s)).1 ⟨hrn, by rw [← hcard]; exact hsc⟩
        have := hA _ hrn hmem
        rw [hs] at this
        exact this
      · intro hno
        refine (he (rgt s)).2 ?_
        rintro ⟨hrn, hrc⟩
        exact hno ⟨hne.2 hrn, by rw [hcard]; exact hrc⟩
    · simp [et, hl]
  have hcxe := hcx (p - 1) et hetC
  rw [sub_add_cancel] at hcxe
  obtain ⟨hDC, hDD⟩ := hcxe
  have hc0 : c0.1 ∈ (cech A).C p ⊓ LinearMap.ker (cech A).D := c0.2
  rw [Submodule.mem_inf] at hc0
  have hmemZ : c0.1 - (cech A).D et ∈ (cech A).Z p := by
    show _ ∈ (cech A).C p ⊓ LinearMap.ker (cech A).D
    rw [Submodule.mem_inf]
    refine ⟨sub_mem hc0.1 hDC, ?_⟩
    rw [LinearMap.mem_ker, map_sub, hDD, sub_zero]
    exact hc0.2
  refine ⟨⟨_, hmemZ⟩, ?_, ?_⟩
  · intro J
    have h1 : (cech A).D et (uni ∅ J) = (deltaL ℂ κ E) e J := by
      have := congrFun (UpperTheory.PullbackConnectingMap.pullC_delta (tr ι) (LinearMap.id : E →ₗ[ℂ] E) et) J
      rw [pull_tr, hpe] at this
      exact this
    have h2 := congrFun hde J
    rw [Pi.sub_apply, pull_tr] at h2
    show (c0.1 - (cech A).D et) (uni ∅ J) = b J
    rw [Pi.sub_apply, h1, h2]
    abel
  · rw [Submodule.Quotient.eq]
    show c0.1 - (cech A).D et - c0.1 ∈ (cech A).B p
    rw [sub_sub_cancel_left, ← map_neg]
    exact Submodule.mem_map_of_mem (Submodule.neg_mem _ hetC)

end Alg

private theorem aff_mono {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type}
    {U : ι → X.Opens} {B : Finset ι → Subalgebra ℂ X.functionField} (hU : IsAffCover p U B) (s t : Finset ι)
    (hs : s.Nonempty) (h : s ⊆ t) : B s ≤ B t := by
  intro y hy
  obtain ⟨f, rfl⟩ := (hU.ring s hs y).1 hy
  have hle : t.inf U ≤ s.inf U := Finset.inf_mono h
  refine (hU.ring t (hs.mono h) _).2 ⟨X.presheaf.map (homOfLE hle).op f, ?_⟩
  exact X.presheaf.germ_res_apply (homOfLE hle) (genericPoint X) (hU.ne t) f

theorem UpperTheory.etaleCorrespondence_family_statement :
    ∀ (E : UpperTheory.A.EFam), UpperTheory.A.NatP E → UpperTheory.A.NatT E → ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)) (hY : IsAffCover s' (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x)) (a p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ Z.functionField) (hb : b ∈ (cech fun I => omB ℂ Z.functionField (rB ℂ Z.functionField x I) a).Z p),
      ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ Y.functionField (RY x j2 (lft s) (rgt s)) a).Z p,
        (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
        ∃ h : trC (k := ℂ) (K := Z.functionField) (L := Y.functionField) (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ Z.functionField (rB ℂ Z.functionField x I) a).Z p,
          E d Z s _ U (rB ℂ Z.functionField x) hK hU a p (hodgeTrace h1 a p (hodgePull h2 a p ((E d Z s _ U (rB ℂ Z.functionField x) hK hU a p).symm (Submodule.Quotient.mk ⟨b, hb⟩)))) = Submodule.Quotient.mk ⟨_, h⟩ := by
  intro E hP hT d Z Y _ _ s s' _ _ hPr c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU hY a p b hb
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
  have hU2 : IsAffCover s' (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) :=
    UpperTheory.etaleCorrespondence_functionField_statement_one d Z Y s s' hPr c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have hJ : IsAffCover s' (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S)) :=
    UpperTheory.etaleCorrespondence_functionField_statement_two d Z Y s s' hPr c1 c2 h1 h2 hK hL g1 j2 g2 F x U hx hU
  have hdr2 : IsDRMap ℂ j2 (pr2L j2) := fun q b v => PullCoc.deRhamPullbackAlongSecondMap_smul_iotaMulti_kaehlerD j2 b q v
  have hdrid : IsDRMap ℂ (AlgHom.id ℂ Y.functionField) (LinearMap.id) := by
    intro q b v
    simp
  have hm1 := UpperTheory.PullbackConnectingMap.pullC_isMap hK hL hU hU2 c2 h2 j2 (pr2L j2) (id : Fin (d + 1) → Fin (d + 1)) hdr2 g2
    (fun i => le_rfl) a
  have hleR : ∀ k : Fin (d + 1), c2 ⁻¹ᵁ U k ≤ (𝟙 Y) ⁻¹ᵁ UpperTheory.A.joinCover c1 c2 U (tr (Fin (d + 1)) k) := by
    intro k
    simp [UpperTheory.A.joinCover, tr]
  have hleL : ∀ k : Fin (d + 1), c1 ⁻¹ᵁ U k ≤ (𝟙 Y) ⁻¹ᵁ UpperTheory.A.joinCover c1 c2 U (tl (Fin (d + 1)) k) := by
    intro k
    simp [UpperTheory.A.joinCover, tl]
  have hmR := UpperTheory.PullbackConnectingMap.pullC_isMap hL hL hJ hU2 (𝟙 Y) (Category.id_comp s') (AlgHom.id ℂ Y.functionField)
    LinearMap.id (tr (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleR a
  have hmL := UpperTheory.PullbackConnectingMap.pullC_isMap hL hL hJ hY (𝟙 Y) (Category.id_comp s') (AlgHom.id ℂ Y.functionField)
    LinearMap.id (tl (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleL a
  have hfin := (GlobalTheory.T.finiteEtale_functionField_integralClosure_differentials Z Y s s' c1 h1 inferInstance inferInstance d hK hL g1).1
  have hmT := UpperTheory.PullbackConnectingMap.trL_isMap (ι := Fin (d + 1)) s' h1 hK hL hU hY (fun V hV hV' g => (g1 V hV hV' g).symm) hfin a
  set z := (E d Z s (Fin (d + 1)) U (rB ℂ Z.functionField x) hK hU a p).symm (Submodule.Quotient.mk ⟨b, hb⟩) with hz
  set w := hodgePull h2 a p z with hw
  have hN1 := hP d Z s (Fin (d + 1)) U (rB ℂ Z.functionField x) hK hU d Y s' (Fin (d + 1)) (fun i => c2 ⁻¹ᵁ U i)
    (R2 x j2) hL hU2 c2 h2 j2 (pr2L j2) id hdr2 g2 (fun i => le_rfl) a p hm1 z
  have hN2 := hP d Y s' (Fin (d + 1) ⊕ₗ Fin (d + 1)) (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S))
    hL hJ d Y s' (Fin (d + 1)) (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) hL hU2 (𝟙 Y) (Category.id_comp s')
    (AlgHom.id ℂ Y.functionField) LinearMap.id (tr (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleR a p hmR w
  have hN3 := hP d Y s' (Fin (d + 1) ⊕ₗ Fin (d + 1)) (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S))
    hL hJ d Y s' (Fin (d + 1)) (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x) hL hY (𝟙 Y) (Category.id_comp s')
    (AlgHom.id ℂ Y.functionField) LinearMap.id (tl (Fin (d + 1))) hdrid (Lef.germCompat_id Y) hleL a p hmL w
  have hT1 := hT d Z s Y s' c1 h1 (Fin (d + 1)) U (rB ℂ Z.functionField x) (rB ℂ Y.functionField x) hK hL hU hY g1 a p hmT w
  rw [hodgePull_id] at hN2 hN3
  rw [hz, LinearEquiv.apply_symm_apply] at hN1
  obtain ⟨c0, hc0⟩ := Submodule.Quotient.mk_surjective _
    (E d Y s' (Fin (d + 1) ⊕ₗ Fin (d + 1)) (UpperTheory.A.joinCover c1 c2 U) (fun S => RY x j2 (lft S) (rgt S)) hL hJ a p w)
  rw [← hc0] at hN2
  rw [hN1] at hN2
  simp only [Cx.hmap, Submodule.mapQ_apply] at hN2
  rw [Submodule.Quotient.eq] at hN2
  rw [← neg_sub, Submodule.neg_mem_iff] at hN2
  have hpb : pullC (id : Fin (d + 1) → Fin (d + 1)) (pr2L j2) b = fun J => pr2L j2 (b J) := by
    funext J
    rw [pullC_mono strictMono_id]
    simp
  have hdiff : pullC (tr (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c0.1
      - pullC (id : Fin (d + 1) → Fin (d + 1)) (pr2L j2) b
      ∈ (cech fun J => omB ℂ Y.functionField (R2 x j2 J) a).B p := hN2
  rw [hpb] at hdiff
  have hcx : (cech fun S : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ Y.functionField (RY x j2 (lft S) (rgt S)) a).IsCx :=
    cech_isCx_of_mono ℂ _ _ _ fun s t hs hst => omB_mono _ _ (aff_mono hJ s t hs hst) a
  have hA : ∀ J : Finset (Fin (d + 1)), J.Nonempty → omB ℂ Y.functionField (R2 x j2 J) a
      ≤ omB ℂ Y.functionField (RY x j2 (lft (uni (∅ : Finset (Fin (d + 1))) J)) (rgt (uni (∅ : Finset (Fin (d + 1))) J))) a := by
    intro J _
    rw [left_union, right_union]
    exact omB_mono _ _ le_sup_right a
  obtain ⟨c, hcJ, hcq⟩ := lift_cocycle _ (fun J => omB ℂ Y.functionField (R2 x j2 J) a) hcx hA p c0 _ hdiff
  refine ⟨c.1, c.2, hcJ, ?_⟩
  rw [← hc0, ← hcq] at hN3
  rw [hN3] at hT1
  simp only [Cx.hmap, Submodule.mapQ_apply] at hT1
  have hval : trC (k := ℂ) (K := Z.functionField) (L := Y.functionField) (fun I => c.1 (uni I ∅))
      = UpperTheory.PullbackConnectingMap.trL Z Y (Fin (d + 1)) (pullC (tl (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c.1) := by
    funext I
    show trDR ℂ Z.functionField Y.functionField (c.1 (uni I ∅))
      = trDR ℂ Z.functionField Y.functionField (pullC (tl (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c.1 I)
    rw [pull_tl]
  obtain ⟨m, hm1, hm2⟩ : ∃ m : (cech fun I => omB ℂ Z.functionField (rB ℂ Z.functionField x I) a).Z p,
      m.1 = UpperTheory.PullbackConnectingMap.trL Z Y (Fin (d + 1)) (pullC (tl (Fin (d + 1))) (LinearMap.id : DR ℂ Y.functionField →ₗ[ℂ] DR ℂ Y.functionField) c.1)
      ∧ E d Z s (Fin (d + 1)) U (rB ℂ Z.functionField x) hK hU a p (hodgeTrace h1 a p w) = Submodule.Quotient.mk m :=
    ⟨_, rfl, hT1⟩
  refine ⟨by rw [hval, ← hm1]; exact m.2, ?_⟩
  rw [hm2]
  congr 1
  exact Subtype.ext (hm1.trans hval.symm)
